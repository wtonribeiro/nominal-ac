(***************************************************************************
 * Tuples.v                						   *		
***************************************************************************)

Require Import Perm.


(** Computes the lenght of a tuple regarding the nth E function symbol n *)

Fixpoint TPlength (t: term) (E n: nat) : nat :=
match t with 
 | (<|t1,t2|>)  => (TPlength t1 E n) + (TPlength t2 E n) 
 | (Fc E0 n0 t1)  => if (E,n) ==np (E0,n0) then
                        (TPlength t1 E n)
                     else 1
 | _ => 1  
end.

(** Computes the ith argument from the tuple t, argument of the nth E function symbol n *)

Fixpoint TPith (i: nat) (t: term) (E n: nat) : term :=
  match t with 

    | (<|t1,t2|>) =>  let l1 :=  (TPlength t1 E n) in 
                        if (le_dec i l1) then
                           (TPith i t1 E n)
                        else (TPith (i-l1) t2 E n)   

   | (Fc E0 n0 t0) => if (E,n) ==np (E0,n0) then
                         (TPith i t0 E n) 
                      else t
                             
   | _  => t
          
  end.

(** Eliminates the ith argument in the tuple t, argument of the E operator n *)

Fixpoint TPithdel (i: nat) (t: term) (E n: nat) : term :=
  match t with 

   | (<|t1,t2|>) => let l1 := (TPlength t1 E n) in 
                      let l2 := (TPlength t2 E n) in 
                        if (le_dec i l1) then 
                         (if (l1 === 1) then t2 
                         else (<|(TPithdel i t1 E n),t2|>))
                        else
                        let ii := i-l1 in   
                         (if (l2 === 1) then t1
                          else (<|t1,(TPithdel ii t2 E n)|>)) 

   | (Fc E0 n0 t0) =>   if TPlength (Fc E0 n0 t) E n === 1 then (<<>>)
                        else (Fc E0 n0 (TPithdel i t0 E n))
                               
                               
   | _ => (<<>>)
end. 


(** The follow function replaces the all superscripts m in S0 to m0 *) 

Fixpoint rpl_super (S0 : set nat) (E0: nat) (t:term) : term :=
match t with
  | Fc E n s  => if (set_In_dec eq_nat_dec E S0) then
                   Fc (E + E0 + 1) n (rpl_super S0 E0 s)
                 else Fc E n (rpl_super S0 E0 s)  
  | [a]^s     => [a]^(rpl_super S0 E0 s)
  | <|s1,s2|> => <|rpl_super S0 E0 s1, rpl_super S0 E0 s2|>
  | _         => t
end.                   


Fixpoint set_super (t:term) : set nat :=
  match t with
    | Fc E n s => set_add eq_nat_dec E (set_super s)
    | [a]^s => set_super s
    | <|s1,s2|> => set_union eq_nat_dec (set_super s1) (set_super s2)
    | _ => []                                                  
  end.



(* TPlength properties *)

Lemma TPlength_geq_1 : forall t E n, TPlength t E n >= 1.
Proof.
  intros; induction t; simpl; try omega.
  case ((E, n) ==np (n0, n1)); intro H0; trivial; try omega.
Qed.

Lemma TPlength_geq_1' : forall t E n, 1 <= TPlength t E n.
Proof.
  intros. assert (Q: TPlength t E n >= 1).
  apply TPlength_geq_1. omega.
Qed.

Hint Resolve TPlength_geq_1.
Hint Resolve TPlength_geq_1'.

Lemma TPlength_Fc_eq : forall E n t,  TPlength (Fc E n t) E n = TPlength t E n.
Proof.
  intros; simpl. case ((E, n) ==np (E, n)); intro H; trivial.
  false. apply H; trivial.
Qed.
  
Hint Rewrite TPlength_Fc_eq : tuples.

Lemma TPlength_Fc_diff : forall E E' n n' t, (E,n) <> (E',n') -> 
 TPlength (Fc E n t) E' n' = 1.
Proof.
  intros; simpl. case ((E', n') ==np (E, n)); intro H'; trivial.
  false. apply H. rewrite H'. trivial.
Qed.  

Hint Resolve TPlength_Fc_diff.

Lemma TPlength_TPith : forall t E n i, TPlength (TPith i t E n) E n = 1.
Proof.
  intros t E n. induction t; intros; simpl; trivial.
  case (le_dec i (TPlength t1 E n)); intro H0. 
  rewrite IHt1; trivial. rewrite IHt2; trivial.
  case ((E, n) ==np (n0, n1)); intro H1.
  rewrite IHt; trivial.
  simpl. case ((E, n) ==np (n0, n1));
  intro H2; try contradiction; trivial.
Qed.

Hint Rewrite TPlength_TPith : tuples.

Lemma Perm_TPlength : forall t E n pi, 
 TPlength (pi @@ t) E n = TPlength t E n. 
Proof.
 intros. induction t; autorewrite with perm; trivial.
 simpl. rewrite IHt1. rewrite IHt2. trivial.
 simpl. case ((E, n) ==np (n0, n1)); intro H; trivial.
Qed.

Hint Rewrite Perm_TPlength : tuples.


(** TPith properties *)

Lemma TPith_0 : forall t E n, TPith 0 t E n = TPith 1 t E n.
Proof.
  intros. induction t; simpl; trivial.
  case (le_dec 1 (TPlength t1 E n)); intro H1; trivial.
  assert (Q: TPlength t1 E n >= 1). auto. omega.
  case ((E, n) ==np (n0, n1)); intro H1; trivial.
Qed.

Lemma TPith_overflow: forall i t E n, i >= TPlength t E n ->
                                      TPith i t E n = TPith (TPlength t E n) t E n.
Proof.  
  intros. case (i === TPlength t E n); intro H0; try rewrite H0; trivial.
  assert (H2: i > TPlength t E n). omega. clear H H0.
  gen i. induction t; simpl in *|-*; intros; trivial.
  case (le_dec i (TPlength t1 E n)); intro H0; try omega.
  case (le_dec (TPlength t1 E n + TPlength t2 E n) (TPlength t1 E n)); intro H1; try omega.
  assert (Q: TPlength t1 E n >= 1). auto. assert (Q': TPlength t2 E n >= 1). auto. omega.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n) with (TPlength t2 E n); try omega.
  rewrite IHt2; trivial. omega.
  gen H2. case ((E, n) ==np (n0, n1)); intros H1 H; trivial. rewrite IHt; trivial.
Qed.

Hint Resolve TPith_overflow.

Lemma TPith_Pr_le : forall i t1 t2 E n, 
 i <= TPlength t1 E n -> TPith i (<|t1,t2|>) E n = TPith i t1 E n. 
Proof.
 intros; simpl; 
 case (le_dec i (TPlength t1 E n)); 
 intro H0; try contradiction; trivial. 
Qed.

Hint Resolve TPith_Pr_le.

Lemma TPith_Pr_gt : forall i t1 t2 E n,
 i >  TPlength t1 E n -> 
 TPith i (<|t1,t2|>) E n = TPith (i - (TPlength t1 E n)) t2 E n.
Proof.
 intros; simpl; 
 case (le_dec i (TPlength t1 E n)); intro H0; trivial. 
 omega.
Qed.

Hint Resolve TPith_Pr_gt.

Lemma TPith_Fc_eq : forall i t E n, TPith i (Fc E n t) E n = TPith i t E n. 
Proof.
 intros. simpl.
 case ((E, n) ==np (E, n)); intro H; trivial.
 false. apply H; trivial.
Qed.

Hint Rewrite TPith_Fc_eq : tuples.

Lemma TPith_Fc_diff : forall i t E E' n n', (E,n) <> (E',n') ->
                                            TPith i (Fc E n t) E' n' = Fc E n t. 
Proof.
 intros. simpl.
 case ((E', n') ==np (E, n)); intro H0; trivial.
 false. apply H. rewrite H0. trivial.
Qed.

Hint Resolve TPith_Fc_diff.

Lemma Perm_TPith : forall t pi E n i,
 pi @ (TPith i t E n) = TPith i (pi @ t) E n.
Proof.
  intros. gen i.
  induction t; intros;
  autorewrite with perm; simpl TPith;
  autorewrite with perm; autorewrite with tuples; trivial.
  case (le_dec i (TPlength t1 E n)); intro H.
  rewrite IHt1; trivial. rewrite IHt2; trivial.
  case ((E, n) ==np (n0, n1)); intro H; try rewrite IHt; trivial.
  autorewrite with perm; trivial.
Qed.  
  

(** TPithdel properties *)

Lemma TPithdel_0 : forall t E n, TPithdel 0 t E n = TPithdel 1 t E n.
Proof.
  intros. induction t; simpl; trivial.
  case (le_dec 1 (TPlength t1 E n)); intro H.
  case (TPlength t1 E n === 1); intro H0; try fequals; trivial.
  assert (Q: TPlength t1 E n >= 1). auto. omega.
  case ((E, n) ==np (n0, n1)); intro H; trivial.
  case (TPlength t E n === 1); intro H2; try fequals; trivial.
Qed. 

Hint Rewrite TPithdel_0 : tuples.


Lemma TPithdel_overflow: forall i t E n, i >= TPlength t E n ->
                                         TPithdel i t E n = TPithdel (TPlength t E n) t E n.
Proof.  
  intros. case (i === TPlength t E n); intro H0; try rewrite H0; trivial.
  assert (H2: i > TPlength t E n). omega. clear H H0.
  gen i H2. induction t; simpl in *|-*; intros; trivial.
  case (le_dec i (TPlength t1 E n)); intro H0; try omega.
  case (le_dec (TPlength t1 E n + TPlength t2 E n) (TPlength t1 E n)); intro H1.
  assert (Q: TPlength t1 E n >= 1). auto.  assert (Q': TPlength t2 E n >= 1). auto. omega.
  clear H0 H1. repeat case_nat; trivial; try fequals.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n) with (TPlength t2 E n); try omega.
  rewrite IHt2; trivial; try omega.
  gen H2. case ((E, n) ==np (n0, n1)); intros H1 H; trivial.
  case_nat; trivial. rewrite IHt; trivial.
Qed.

Hint Resolve TPithdel_overflow.


Lemma TPithdel_TPlength_1 : forall i t E n, 
 TPlength t E n = 1 -> TPithdel i t E n = <<>>.
Proof.
 intros. destruct t; simpl; trivial. 
 apply False_ind. simpl in H.
 assert (Q: TPlength t1 E n >= 1 /\ TPlength t2 E n >= 1). auto. omega.
 simpl in H. gen H. case ((E, n) ==np (n0, n1)); intros H0 H; trivial.
 inverts H0. case_nat; trivial; try contradiction.
Qed.

Hint Resolve TPithdel_TPlength_1.

Lemma TPithdel_Fc_eq : forall i t E n, 
 TPlength t E n <> 1 ->
 TPithdel i (Fc E n t) E n = Fc E n (TPithdel i t E n).
Proof. 
 intros; simpl.
 case ((E, n) ==np (E, n)); intro H0.
 case_nat; try contradiction; trivial.
 false. apply H0. trivial.
Qed.

Hint Resolve TPithdel_Fc_eq.

Lemma TPithdel_Fc_diff : forall i t E E' n n', (E,n) <> (E',n') ->
                                               TPithdel i (Fc E n t) E' n' = <<>>.
Proof.
 intros. rewrite TPithdel_TPlength_1; auto.
Qed.

Hint Resolve TPithdel_Fc_diff.

Lemma TPithdel_t1_Pr : forall i t1 t2 E n, i <= TPlength t1 E n -> TPlength t1 E n = 1 ->
                                           TPithdel i (<|t1,t2|>) E n = t2. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try contradiction.
  case_nat; try contradiction; trivial.
Qed.

Hint Resolve TPithdel_t1_Pr.

Lemma TPithdel_t2_Pr : forall i t1 t2 E n, i > TPlength t1 E n -> TPlength t2 E n = 1 ->
                                           TPithdel i (<|t1,t2|>) E n = t1. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try omega. 
  case_nat; try contradiction; trivial.
Qed.

Hint Resolve TPithdel_t2_Pr.

Lemma TPithdel_Pr_le : forall i t1 t2 E n, i <= TPlength t1 E n -> TPlength t1 E n <> 1 ->
                                           TPithdel i (<|t1,t2|>) E n = <|(TPithdel i t1 E n),t2|>. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try contradiction.
  case_nat; try contradiction; trivial.
Qed.  

Hint Resolve TPithdel_Pr_le.

Lemma TPithdel_Pr_gt : forall i t1 t2 E n, i > TPlength t1 E n -> TPlength t2 E n <> 1 ->
                                           TPithdel i (<|t1,t2|>) E n = <|t1,(TPithdel (i - TPlength t1 E n) t2 E n)|>. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try omega. 
  case_nat; try contradiction; trivial.
Qed.

Hint Resolve TPithdel_Pr_gt.

Lemma TPlength_TPithdel : forall i t E n, (TPlength t E n) <> 1 ->
                                          TPlength (TPithdel i t E n) E n = (TPlength t E n) - 1.
Proof.
 intros. gen i. induction t; intros; simpl in *|-*; try omega.
 case (le_dec i (TPlength t1 E n)); intro H0. case_nat; try omega.
 simpl. rewrite IHt1; try omega.
 assert (Q:TPlength t1 E n >= 1). auto.
 assert (Q': TPlength t2 E n >= 1). auto. omega.
 case_nat; try omega. simpl. rewrite IHt2; try omega.
 assert (Q:TPlength t1 E n >= 1). auto.
 assert (Q': TPlength t2 E n >= 1). auto. omega.
 gen H. case ((E, n) ==np (n0, n1)); intros H0 H; simpl; try omega.
 inverts H0. case_nat; try contradiction.
 simpl. case ((n0, n1) ==np (n0, n1)); intro H0. rewrite IHt; trivial.
 false. apply H0. trivial.
Qed.

Hint Resolve TPlength_TPithdel.


Lemma TPith_TPithdel_lt : forall t E n i j, i > 0 -> i < j -> i < TPlength t E n ->  
                                            TPith i (TPithdel j t E n) E n = TPith i t E n.
Proof.
  intros t E n. 
  induction t; intros; simpl in *|-; try omega.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (TPlength t1 E n === 1); intro H3; try omega.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPith_Pr_le with (t1:=t1); try omega.
  rewrite TPith_Pr_le. rewrite IHt1; try omega; trivial.
  rewrite TPlength_TPithdel; try omega; trivial.
  case (TPlength t2 E n === 1); intro H4.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  rewrite TPith_Pr_le; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega.
  case (le_dec i (TPlength t1 E n)); intro H5. 
  rewrite 2 TPith_Pr_le; try omega; trivial.
  rewrite 2 TPith_Pr_gt; try omega; trivial.
  rewrite IHt2; try omega; trivial.
  gen H1. case ((E, n) ==np (n0, n1)); intros H1 H2.
  inverts H1. case (TPlength t n0 n1 === 1); intro H1. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; trivial. omega.  
Qed.

Hint Resolve TPith_TPithdel_lt.


Lemma TPith_TPithdel_geq : forall t E n i j, i > 0 -> i >= j -> i < TPlength t E n ->
                                             TPith i (TPithdel j t E n) E n = TPith (i + 1) t E n.
Proof.
  intros t E n. 
  induction t; intros; simpl in *|-; try omega.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (TPlength t1 E n === 1); intro H3.
  rewrite TPithdel_t1_Pr; trivial.
  rewrite TPith_Pr_gt; try omega.
  replace (i + 1 - TPlength t1 E n) with i; try omega; trivial.
  rewrite TPithdel_Pr_le; try omega.
  case (le_dec (i + 1) (TPlength t1 E n)); intro H4.
  rewrite 2 TPith_Pr_le; try omega.
  rewrite IHt1; try omega; trivial.
  rewrite TPlength_TPithdel; try omega; trivial.
  rewrite 2 TPith_Pr_gt; try omega.
  rewrite TPlength_TPithdel; try omega; trivial.
  assert (Q: TPlength t1 E n >= 1). auto.
  replace (i - (TPlength t1 E n - 1)) with
          (i + 1 - TPlength t1 E n); try omega; trivial.
  rewrite TPlength_TPithdel; try omega. 
  case (TPlength t2 E n === 1); intro H3; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite 2 TPith_Pr_gt; try omega.
  gen_eq ii : (i - TPlength t1 E n); intro Hii.
  replace (i + 1 - TPlength t1 E n) with (ii + 1); try omega.
  rewrite IHt2; try omega; trivial.
  gen H1. case ((E, n) ==np (n0, n1)); intros H1 H2.
  inverts H1. case (TPlength t n0 n1 === 1); intro H1. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; trivial. omega.  
Qed.

Hint Resolve TPith_TPithdel_geq.


Lemma TPithdel_lt_comm : forall t E n i j, i > 0 -> i < j -> j <= TPlength t E n ->
                                           TPithdel i (TPithdel j t E n) E n = TPithdel (j - 1) (TPithdel i t E n) E n.
Proof.
  intros t E n.
  induction t; intros; simpl in *|-; try omega.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (TPlength t1 E n === 1); intro H3; try omega.
  rewrite TPithdel_Pr_le with (i:=j); try omega.
  rewrite TPithdel_Pr_le with (t1:=t1); try omega.
  case (TPlength t1 E n === 2); intro H4.
  rewrite 2 TPithdel_t1_Pr;
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite 2 TPithdel_Pr_le;
  try rewrite TPlength_TPithdel; try omega; trivial. fequals. 
  rewrite IHt1; try omega; trivial.
  case (TPlength t2 E n === 1); intro H3.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  case (le_dec i (TPlength t1 E n)); intro H4.
  case (TPlength t1 E n === 1); intro H5.
  rewrite TPithdel_t1_Pr with (t1 := t1); try omega.
  rewrite 2 TPithdel_TPlength_1; try omega; trivial.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  rewrite TPlength_TPithdel; try omega. omega.  
  rewrite TPithdel_Pr_gt; try omega.
  case (le_dec i (TPlength t1 E n)); intro H4.
  case (TPlength t1 E n === 1); intro H5.
  rewrite 2 TPithdel_t1_Pr with (i:=i); trivial.
  rewrite H5. trivial.
  rewrite 2 TPithdel_Pr_le with (i:=i); trivial.  
  rewrite TPithdel_Pr_gt;
  try rewrite TPlength_TPithdel; try omega. fequals.
  replace (j - 1 - (TPlength t1 E n - 1)) with
  (j - TPlength t1 E n); try omega; trivial.
  case (TPlength t2 E n === 2); intro H5. 
  rewrite TPithdel_t2_Pr with (i:=i);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite TPithdel_t2_Pr; 
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite 3 TPithdel_Pr_gt;
  try rewrite TPlength_TPithdel; try omega; trivial. fequals.
  gen_eq jj : (j - TPlength t1 E n); intro H6.
  replace (j - 1 - TPlength t1 E n) with (jj - 1); try omega.
  rewrite IHt2; try omega; trivial.
  gen H1. case ((E, n) ==np (n0, n1)); intros H1 H2.
  inverts H1. case (TPlength t n0 n1 === 1); intro H1. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite TPithdel_Fc_eq with (t:=t); trivial.
  case (TPlength t n0 n1 === 2); intro H3.
  rewrite TPithdel_TPlength_1 with (i:=i);
  autorewrite with tuples; try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite TPithdel_TPlength_1 with (i:=j-1);
  autorewrite with tuples; try rewrite TPlength_TPithdel; try omega; trivial.  
  rewrite 2 TPithdel_Fc_eq;
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite IHt; trivial. omega.  
Qed.

Lemma TPithdel_geq_comm : forall t E n i j, i > 0 -> j <= i -> i < TPlength t E n ->
                                            TPithdel i (TPithdel j t E n) E n = TPithdel j (TPithdel (i + 1) t E n) E n.
Proof.
  intros. gen_eq ii : (i + 1); intro H2.
  replace i with (ii - 1); try omega.
  case (j === 0); intro H3; try rewrite H3; repeat rewrite TPithdel_0.  
  rewrite <- TPithdel_lt_comm; try omega; trivial.
  rewrite <- TPithdel_lt_comm; try omega; trivial.
Qed.  
   

Lemma Perm_TPithdel : forall t pi E n i,
 pi @ (TPithdel i t E n) = TPithdel i (pi @ t) E n.
Proof.
  intros. gen i. induction t; intro;
  autorewrite with perm; autorewrite with perm; trivial.
  case (le_dec i (TPlength t1 E n)); intro H1. 
  case (TPlength t1 E n === 1); intro H2.
  rewrite 2 TPithdel_t1_Pr;
  autorewrite with tuples; trivial.
  rewrite 2 TPithdel_Pr_le;
  autorewrite with tuples perm; try omega.
  rewrite IHt1; trivial.
  case (TPlength t2 E n === 1); intro H2.
  rewrite 2 TPithdel_t2_Pr;
  autorewrite with tuples; try omega; trivial.
  rewrite 2 TPithdel_Pr_gt;
  autorewrite with tuples perm; try omega.
  rewrite IHt2; trivial.
  case ((n0,n1) ==np (E,n)); intro H0.
  inverts H0. case (TPlength t E n === 1); intro H0.
  rewrite 2 TPithdel_TPlength_1;
  autorewrite with perm tuples;
  try omega; trivial.
  rewrite 2 TPithdel_Fc_eq;
  autorewrite with perm tuples; trivial.
  rewrite IHt; trivial.
  rewrite 2 TPithdel_Fc_diff;  
  autorewrite with perm tuples;
  try omega; trivial.    
Qed. 

Hint Resolve Perm_TPithdel. 


(** About size_term and TPlength *)

Lemma size_swapp_term : forall s t, size_term (|[s] @ t) = size_term t. 
Proof. 
 intros. destruct s. induction t; simpl; trivial; omega.
Qed.

Hint Rewrite size_swapp_term : tuples.

Lemma size_term_Pr_l : forall t1 t2, size_term t1 < size_term (<|t1,t2|>).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Pr_r : forall t1 t2, size_term t2 < size_term (<|t1,t2|>).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Fc : forall E n t, size_term t < size_term (Fc E n t).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Ab_1 : forall a t, size_term t < size_term ([a]^t).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Ab_2 : forall a s t, size_term (|[s] @ t) < size_term ([a]^t).
Proof. intros. simpl. rewrite size_swapp_term. omega. Qed.

Hint Resolve size_term_Pr_l.
Hint Resolve size_term_Pr_r.
Hint Resolve size_term_Fc.
Hint Resolve size_term_Ab_1.
Hint Resolve size_term_Ab_2.

Lemma size_term_geq_1 : forall t, size_term t >= 1.
Proof. introv. induction t; simpl; try omega; auto. Qed.

Hint Resolve size_term_geq_1.

Lemma TPlength_leq_size_term : forall t E n, TPlength t E n <= size_term t.
Proof.
  intros. induction t; simpl; try omega.
  case ((E, n) ==np (n0, n1)); intro H0; omega.
Qed.

Hint Resolve TPlength_leq_size_term.

Lemma size_term_TPith : forall i t E n,
 size_term (TPith i t E n) <= size_term t.
Proof.
 intros. gen i. induction t; intro i.
 simpl; trivial. simpl; trivial. simpl; omega.
 case (le_dec i (TPlength t1 E n)); intro H.
 rewrite TPith_Pr_le; trivial; simpl; trivial.
 assert (Q: size_term (TPith i t1 E n) <= size_term t1). apply IHt1. omega.
 rewrite TPith_Pr_gt; try omega; simpl.
 assert (Q: size_term (TPith (i - TPlength t1 E n) t2 E n) <= size_term t2). apply IHt2. omega. 
 case ((n0,n1) ==np (E,n)); intro H.
 inverts H. rewrite TPith_Fc_eq; trivial. simpl. 
 assert (Q: size_term (TPith i t E n) <= size_term t). apply IHt. omega.
 rewrite TPith_Fc_diff; trivial. simpl; trivial.
Qed.

Hint Resolve size_term_TPith. 

Lemma size_term_TPithdel : forall i t E n, TPlength t E n <> 1 ->
                                           size_term (TPithdel i t E n) < size_term t.
Proof.
 intros. gen i. induction t; intro i.
 simpl in H; omega. simpl in H; omega. simpl in H; omega.
 case (le_dec i (TPlength t1 E n)); intro H0.
 case (TPlength t1 E n === 1); intro H1.
 rewrite TPithdel_t1_Pr; trivial. 
 rewrite TPithdel_Pr_le; trivial; simpl; trivial.
 assert (Q: size_term (TPithdel i t1 E n) < size_term t1). apply IHt1; trivial. omega.
 case (TPlength t2 E n === 1); intro H1.
 rewrite TPithdel_t2_Pr; try omega. simpl; omega.
 rewrite TPithdel_Pr_gt; try omega; simpl.
 assert (Q: size_term (TPithdel (i - TPlength t1 E n) t2 E n) < size_term t2). apply IHt2; trivial. omega.
 assert (Q:size_term t >=1). auto.
 case ((n0,n1) ==np (E,n)); intro H0.
 inverts H0. case (TPlength t E n === 1); intro H0.
 rewrite TPithdel_TPlength_1; autorewrite with tuples; simpl; try omega; trivial.
 rewrite TPithdel_Fc_eq; trivial. simpl. 
 assert (Q': size_term (TPithdel i t E n) < size_term t). apply IHt; trivial. omega.
 rewrite TPithdel_Fc_diff; trivial. simpl. omega.
 simpl in H. omega.
Qed.

Hint Resolve size_term_TPithdel.


(** About rpl_super and set_super*)

Lemma rpl_super_perm : forall S0 m pi t,
                      rpl_super S0 m (pi @ t) = pi @ (rpl_super S0 m t).
Proof.
  intros. induction t; intros;
          autorewrite with perm; simpl rpl_super;
          autorewrite with perm; trivial.
  rewrite IHt; trivial. rewrite IHt1. rewrite IHt2; trivial.
  case (set_In_dec eq_nat_dec n S0);
  rewrite IHt; autorewrite with perm; trivial.
Qed.

Lemma TPlength_rpl_super : forall S0 E0 E n t,
      ~ set_In E S0 -> E0 >= E ->
      TPlength (rpl_super S0 E0 t) E n  = TPlength t E n.
Proof.
  intros. induction t.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl. rewrite IHt1. rewrite IHt2; trivial.
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1.
  autorewrite with tuples. simpl.
  case (set_In_dec eq_nat_dec E S0);
  intro H1; try contradiction.
  autorewrite with tuples; trivial.
  rewrite TPlength_Fc_diff; trivial.
  simpl. case (set_In_dec eq_nat_dec n0 S0); intro H2.
  case (((n0 + E0 + 1),n1) ==np (E,n)); intro H3; try omega.
  inverts H3; try omega. rewrite TPlength_Fc_diff; trivial.
  rewrite TPlength_Fc_diff; trivial.
  simpl; trivial.
Qed.

Lemma TPith_rpl_super : forall i S0 E0 E n t,
      ~ set_In E S0 -> E0 >= E ->                     
      TPith i (rpl_super S0 E0 t) E n = rpl_super S0 E0 (TPith i t E n).
Proof.
  intros. gen i. induction t; intro i.
  simpl; trivial. simpl; trivial. simpl; trivial.
  case (le_dec i (TPlength t1 E n)); intro H1.
  rewrite TPith_Pr_le; trivial. simpl rpl_super.
  rewrite TPith_Pr_le; trivial. rewrite TPlength_rpl_super; trivial.
  rewrite TPith_Pr_gt; try omega. simpl rpl_super.
  rewrite TPith_Pr_gt; try rewrite TPlength_rpl_super; try omega; trivial. 
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1. autorewrite with tuples.
  simpl. case (set_In_dec eq_nat_dec E S0); intro H1; try contradiction.
  autorewrite with tuples. rewrite IHt; trivial.
  rewrite TPith_Fc_diff; trivial. simpl.
  case (set_In_dec eq_nat_dec n0 S0); intro H2.
  case (((n0 + E0 + 1),n1) ==np (E,n)); intro H3. inverts H3; try omega.
  rewrite TPith_Fc_diff; trivial.
  rewrite TPith_Fc_diff; trivial. 
  simpl; trivial.
Qed.

Lemma TPithdel_rpl_super : forall i S0 E0 E n t,
      ~ set_In E S0 -> E0 >= E ->                        
      TPithdel i (rpl_super S0 E0 t) E n  =
      rpl_super S0 E0 (TPithdel i t E n).
Proof.
  intros. gen i. induction t; intro i.
  simpl; trivial. simpl; trivial. simpl; trivial.
  case (le_dec i (TPlength t1 E n)); intro H1.
  case (TPlength t1 E n === 1); intro H2.
  rewrite TPithdel_t1_Pr; trivial. simpl rpl_super.
  rewrite TPithdel_t1_Pr; try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Pr_le; trivial. simpl rpl_super.
  rewrite TPithdel_Pr_le; try rewrite TPlength_rpl_super; trivial. rewrite IHt1; trivial.
  case (TPlength t2 E n === 1); intro H2.
  rewrite TPithdel_t2_Pr; try omega. simpl rpl_super.
  rewrite TPithdel_t2_Pr; try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega. simpl rpl_super.
  rewrite TPithdel_Pr_gt; try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite IHt2; trivial.
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1. autorewrite with tuples.
  simpl. case (set_In_dec eq_nat_dec E S0); intro H1; try contradiction.
  case ((E, n) ==np (E, n)); intro H2. case_nat.
  rewrite TPithdel_TPlength_1;
  autorewrite with tuples; try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Fc_eq; try rewrite TPlength_rpl_super; trivial.
  simpl. case (set_In_dec eq_nat_dec E S0); intro H3; try contradiction.
  rewrite IHt; trivial. false. apply H2; trivial.
  rewrite TPithdel_Fc_diff; trivial. simpl.
  case (set_In_dec eq_nat_dec n0 S0); intro H2.
  case (((n0 + E0 + 1),n1) ==np (E,n)); intro H3. inverts H3; try omega.
  rewrite TPithdel_Fc_diff; trivial.
  rewrite TPithdel_Fc_diff; trivial. 
  simpl; trivial.
Qed.


Lemma set_super_TPith : forall i E0 E n t, set_In E0 (set_super (TPith i t E n)) ->
                                           set_In E0 (set_super t).
Proof.
  intros. gen i. induction t; intros.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl. case (le_dec i (TPlength t1 E n)); intro H0.
  rewrite TPith_Pr_le in H; trivial.
  apply set_union_intro1. apply (IHt1 i); trivial.
  rewrite TPith_Pr_gt in H; try omega.
  apply set_union_intro2. apply (IHt2 (i - TPlength t1 E n)); trivial.
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1.
  autorewrite with tuples in H. simpl. apply set_add_intro1. apply (IHt i); trivial.
  rewrite TPith_Fc_diff in H; trivial.
  simpl; trivial.
Qed.

Lemma set_super_TPithdel : forall i E0 E n t, set_In E0 (set_super (TPithdel i t E n)) ->
                                              set_In E0 (set_super t).
Proof.
  intros. gen i. induction t; intros.
  simpl; trivial. simpl; trivial. simpl in H. contradiction.
  simpl. case (le_dec i (TPlength t1 E n)); intro H0.
  case (TPlength t1 E n === 1); intro H1.
  rewrite TPithdel_t1_Pr in H; trivial.
  apply set_union_intro2; trivial.
  rewrite TPithdel_Pr_le in H; trivial. simpl in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply (IHt1 i); trivial.
  apply set_union_intro2; trivial.
  case (TPlength t2 E n === 1); intro H1.
  rewrite TPithdel_t2_Pr in H; try omega.
  apply set_union_intro1; trivial.
  rewrite TPithdel_Pr_gt in H; try omega. simpl in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  apply (IHt2 (i - TPlength t1 E n)); trivial.
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1.
  case (TPlength t E n === 1); intro H1.
  rewrite TPithdel_TPlength_1 in H; autorewrite with tuples; trivial.
  simpl in H. contradiction.
  rewrite TPithdel_Fc_eq in H; trivial. simpl in H.
  simpl. apply set_add_elim in H. destruct H. 
  apply set_add_intro2; trivial.
  apply set_add_intro1. apply (IHt i); trivial.
  rewrite TPithdel_Fc_diff in H; trivial.
  simpl in H. contradiction.
  simpl; trivial.
Qed.

Lemma set_rpl_super : forall m S0 t,
(forall k, set_In k S0 -> m >= k) ->
(forall n, set_In n S0 -> ~ set_In n (set_super (rpl_super S0 m t))).
Proof.
  intros. induction t; simpl in *|-*; auto.
  intro. apply set_union_elim in H1.
  destruct H1; [apply IHt1; trivial | apply IHt2; trivial].  
  case (set_In_dec eq_nat_dec n0 S0); intro H1; simpl.
  intro. apply IHt. apply set_add_elim in H2.
  destruct H2; trivial. assert (Q: m >= n). apply H; trivial.
  assert (Q': n <> n0 + m + 1). omega. contradiction.
  intro. apply IHt. apply set_add_elim in H2.
  destruct H2; trivial. rewrite H2 in H0. contradiction.
Qed.

Lemma perm_set_super : forall pi t,
                       set_super (pi @ t) = set_super t .
Proof.
  intros. induction t; autorewrite with perm; simpl; auto.
  rewrite IHt1. rewrite IHt2. trivial.
  rewrite IHt. trivial.
Qed.


Lemma leq_nat_set : forall (S0 : set nat),
                    exists m, forall n, set_In n S0 -> n <= m.
Proof.
  intros. induction S0.
  exists 0; intros. simpl in H. contradiction.
  simpl. case IHS0; intros.
  case (le_dec a x); intro H1.
  exists x; intros. destruct H0.
  rewrite <- H0; trivial. apply H; trivial.
  exists a; intros. destruct H0; try omega.
  assert (Q: n <= x). apply H; trivial. omega.
Qed.
 
Lemma pick_fresh_nat : forall (S1 : set nat),
                        exists m, ~ set_In m S1.
Proof.
  intro. case (leq_nat_set S1); intros.
  exists (S x). intro H0. apply H in H0. omega.
Qed.


Notation "S1 |U S2" := (set_union eq_nat_dec S1 S2) (at level 67).
Notation "S1 |I S2" := (set_inter eq_nat_dec S1 S2) (at level 67).

Definition subset (A : Set) (S1 S2 : set A) :=
  forall m, set_In m S1 -> set_In m S2.

Lemma nil_empty_set : forall (A: Set) (S: set A), S = [] <-> (forall k, ~ set_In k S).
Proof.
  intros. split~; intros. rewrite H.
  intro H'. simpl in H'. trivial.
  destruct S; trivial.
  assert (Q:~set_In a (a :: S)). apply H.
  false. apply Q. simpl. left~.
Qed.