(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Tuples.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: Jun 23, 2018.
 ============================================================================
 *)

Require Import Perm.


(** Computes the length of a tuple regarding the nth E function symbol *)


Fixpoint TPlength (t: term) (E n: nat) : nat :=
match t with 
 | (<|t1,t2|>)    => (TPlength t1 E n) + (TPlength t2 E n) 
 | (Fc E0 n0 t1)  => if (E,n) ==np (E0,n0)
                     then (TPlength t1 E n)
                     else 1
 | _ => 1  
end.

(** Computes the ith argument from the tuple t, argument of the nth E function symbol *)

Fixpoint TPith (i: nat) (t: term) (E n: nat) : term :=
match t with 
 | (<|t1,t2|>)   => let l1 := TPlength t1 E n in 
                      if le_dec i l1
                      then TPith i t1 E n
                      else TPith (i-l1) t2 E n   

 | (Fc E0 n0 t0) => if (E,n) ==np (E0,n0)
                    then TPith i t0 E n
                    else t
                             
 | _             => t
end.

(** Eliminates the ith argument in the tuple t, argument of the nth E function symbol *)

Fixpoint TPithdel (i: nat) (t: term) (E n: nat) : term :=
match t with
 | (<|t1,t2|>) => let l1 := (TPlength t1 E n) in 
                  let l2 := (TPlength t2 E n) in 
                    if (le_dec i l1)
                    then 
                      if eq_nat_dec l1 1
                      then t2 
                      else <|(TPithdel i t1 E n),t2|>
                    else
                      let ii := i-l1 in   
                        if eq_nat_dec l2 1
                        then t1
                        else <|t1,(TPithdel ii t2 E n)|> 

 | (Fc E0 n0 t0) => if eq_nat_dec (TPlength (Fc E0 n0 t) E n) 1
                    then <<>>
                    else Fc E0 n0 (TPithdel i t0 E n)                          
                               
 | _ => <<>>
end.

  

(** Replaces all superscripts m in S0 by m0 *) 

Fixpoint rpl_super (S0 : set nat) (E0: nat) (t:term) : term :=
match t with
  | Fc E n s  => if (set_In_dec eq_nat_dec E S0) then
                   Fc (E + E0 + 1) n (rpl_super S0 E0 s)
                 else Fc E n (rpl_super S0 E0 s)  
  | [a]^s     => [a]^(rpl_super S0 E0 s)
  | <|s1,s2|> => <|rpl_super S0 E0 s1, rpl_super S0 E0 s2|>
  | _         => t
end.                   


(** Computes the set of superscripts that occur in t *)

Fixpoint set_super (t:term) : set nat :=
  match t with
    | Fc E n s => set_add eq_nat_dec E (set_super s)
    | [a]^s => set_super s
    | <|s1,s2|> => set_union eq_nat_dec (set_super s1) (set_super s2)
    | _ => []                                                  
  end.



(** Generates a colection of arguments of a given funcion symbol regarding a given 
list of indices *)

Fixpoint nat_seq (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n0 => S n0 :: nat_seq n0          
  end.
              
Fixpoint Args_col_list (L : list nat) (t : term) (E n: nat) : list term :=

  match L with

   | [] => []
            
   | i::L0 => TPith i t E n :: (Args_col_list L0 t E n) 
             
  end.


Fixpoint Args_right_assoc (Lt : list term) : term :=

  match Lt with

  | [] => <<>>

  | [t] => t

  | t :: Lt0 => <| t, Args_right_assoc Lt0 |>

  end.                                      


Fixpoint Args_assoc (L : list nat) (Lt : list term) : term :=

  match L, Lt with

  | S n :: L0 , t :: Lt0  =>

                 if lt_dec n (length Lt0)
                 then <| Args_assoc L0 (head_list _ (S n) Lt),
                         Args_right_assoc (tail_list _ (S n) Lt) |>
                 else Args_right_assoc Lt                     

  | _ , _  => Args_right_assoc Lt
                                  
                                        
  end.


Definition valid_col (L : list nat) (t : term) (E n : nat) :=

  NoDup L /\

  forall a, In a L -> a >= 1 /\ a <= TPlength t E n .



Definition Args_col (L L' : list nat) (t : term) (E n : nat) :=

  Args_assoc L' (Args_col_list L t E n) . 



(** **)

Fixpoint func_symbols_term (t : term) {struct t} : nat :=
  match t with
    | [a]^s => func_symbols_term s
    | <|u,v|> => (func_symbols_term u) + (func_symbols_term v)                             
    | Fc E n s => (func_symbols_term s) + 1
    | _ => 0
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
  intros; simpl. case ((E, n) ==np (E, n)); intro H; trivial. false. 
Qed.
  
Hint Rewrite TPlength_Fc_eq : tuples.

Lemma TPlength_Fc_diff : forall E E' n n' t, (E,n) <> (E',n') -> 
 TPlength (Fc E n t) E' n' = 1.
Proof.
  intros; simpl. case ((E', n') ==np (E, n)); intro H'; trivial. false. 
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
  intros. case (eq_nat_dec i (TPlength t E n)); intro H0; try rewrite H0; trivial.
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
 case ((E, n) ==np (E, n)); intro H; trivial. false. 
Qed.

Hint Rewrite TPith_Fc_eq : tuples.

Lemma TPith_Fc_diff : forall i t E E' n n', (E,n) <> (E',n') ->
                                            TPith i (Fc E n t) E' n' = Fc E n t. 
Proof.
 intros. simpl.
 case ((E', n') ==np (E, n)); intro H0; trivial. false. 
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
  case (eq_nat_dec (TPlength t1 E n) 1); intro H0; try fequals; trivial.
  assert (Q: TPlength t1 E n >= 1). auto. omega.
  case ((E, n) ==np (n0, n1)); intro H; trivial.
  case (eq_nat_dec (TPlength t E n) 1); intro H2; try fequals; trivial.
Qed. 

Hint Rewrite TPithdel_0 : tuples.


Lemma TPithdel_overflow: forall i t E n, i >= TPlength t E n ->
                                         TPithdel i t E n = TPithdel (TPlength t E n) t E n.
Proof.  
  intros. case (eq_nat_dec i (TPlength t E n)); intro H0; try rewrite H0; trivial.
  assert (H2: i > TPlength t E n). omega. clear H H0.
  gen i H2. induction t; simpl in *|-*; intros; trivial.
  case (le_dec i (TPlength t1 E n)); intro H0; try omega.
  case (le_dec (TPlength t1 E n + TPlength t2 E n) (TPlength t1 E n)); intro H1.
  assert (Q: TPlength t1 E n >= 1). auto.  assert (Q': TPlength t2 E n >= 1). auto. omega.
  clear H0 H1. case (eq_nat_dec (TPlength t2 E n) 1); intro H3; try fequals.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n) with (TPlength t2 E n); try omega.
  rewrite IHt2; trivial; try omega.
  gen H2. case ((E, n) ==np (n0, n1)); intros H1 H; trivial.
  case (eq_nat_dec (TPlength t E n) 1); intro H0; trivial. rewrite IHt; trivial.
Qed.

Hint Resolve TPithdel_overflow.


Lemma TPithdel_TPlength_1 : forall i t E n, 
 TPlength t E n = 1 -> TPithdel i t E n = <<>>.
Proof.
 intros. destruct t; simpl; trivial. 
 apply False_ind. simpl in H.
 assert (Q: TPlength t1 E n >= 1 /\ TPlength t2 E n >= 1). auto. omega.
 simpl in H. gen H. case ((E, n) ==np (n0, n1)); intros H0 H; trivial.
 inverts H0. case (eq_nat_dec (TPlength t n0 n1) 1); intro H0; trivial; try contradiction.
Qed.

Hint Resolve TPithdel_TPlength_1.

Lemma TPithdel_Fc_eq : forall i t E n, 
 TPlength t E n <> 1 ->
 TPithdel i (Fc E n t) E n = Fc E n (TPithdel i t E n).
Proof. 
 intros; simpl.
 case ((E, n) ==np (E, n)); intro H0.
 case (eq_nat_dec (TPlength t E n) 1); intro H1; trivial; try contradiction.
 false.
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
  case (eq_nat_dec (TPlength t1 E n) 1); intro H2; trivial; try contradiction. 
Qed.

Hint Resolve TPithdel_t1_Pr.

Lemma TPithdel_t2_Pr : forall i t1 t2 E n, i > TPlength t1 E n -> TPlength t2 E n = 1 ->
                                           TPithdel i (<|t1,t2|>) E n = t1. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try omega. 
  case (eq_nat_dec (TPlength t2 E n) 1); intro H2; trivial; try contradiction.
Qed.

Hint Resolve TPithdel_t2_Pr.

Lemma TPithdel_Pr_le : forall i t1 t2 E n, i <= TPlength t1 E n -> TPlength t1 E n <> 1 ->
                                           TPithdel i (<|t1,t2|>) E n = <|(TPithdel i t1 E n),t2|>. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try contradiction.
  case (eq_nat_dec (TPlength t1 E n) 1); intro H2; trivial; try contradiction.
Qed.  

Hint Resolve TPithdel_Pr_le.

Lemma TPithdel_Pr_gt : forall i t1 t2 E n, i > TPlength t1 E n -> TPlength t2 E n <> 1 ->
                                           TPithdel i (<|t1,t2|>) E n = <|t1,(TPithdel (i - TPlength t1 E n) t2 E n)|>. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try omega. 
  case (eq_nat_dec (TPlength t2 E n) 1); intro H2; trivial; try contradiction.
Qed.

Hint Resolve TPithdel_Pr_gt.

Lemma TPlength_TPithdel : forall i t E n, (TPlength t E n) <> 1 ->
                                          TPlength (TPithdel i t E n) E n = (TPlength t E n) - 1.
Proof.
 intros. gen i. induction t; intros; simpl in *|-*; try omega.
 case (le_dec i (TPlength t1 E n)); intro H0.
 case (eq_nat_dec (TPlength t1 E n) 1); intro H1; try omega.
 simpl. rewrite IHt1; try omega.
 assert (Q:TPlength t1 E n >= 1). auto.
 assert (Q': TPlength t2 E n >= 1). auto. omega.
 case (eq_nat_dec (TPlength t2 E n) 1); intro H1; try omega.
 simpl. rewrite IHt2; try omega.
 assert (Q:TPlength t1 E n >= 1). auto.
 assert (Q': TPlength t2 E n >= 1). auto. omega.
 gen H. case ((E, n) ==np (n0, n1)); intros H0 H; simpl; try omega.
 inverts H0.  case (eq_nat_dec (TPlength t n0 n1) 1); intro H0; try contradiction. 
 simpl. case ((n0, n1) ==np (n0, n1)); intro H1. rewrite IHt; trivial. false. 
Qed.

Hint Resolve TPlength_TPithdel.



Lemma TPith_TPithdel_leq_1 : forall t E n i j, i <= 1 -> j <= 1 -> TPlength t E n <> 1 ->
                                               TPith i (TPithdel j t E n) E n = TPith 2 t E n.
Proof.
  intros. induction t.
  simpl; trivial. simpl in H1. false.
  simpl in H1. false.
  case (eq_nat_dec (TPlength t1 E n) 1); intro H2.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPith_Pr_gt; try omega.
  rewrite H2. simpl.
  case (eq_nat_dec i 0); intro H3. rewrite H3. apply TPith_0.
  assert (Q : i = 1). omega. rewrite Q; trivial.
  assert (Q : TPlength t1 E n >= 1). auto.
  rewrite TPithdel_Pr_le; try omega.
  rewrite 2 TPith_Pr_le; try omega.
  apply IHt1; trivial. rewrite TPlength_TPithdel; omega.
  simpl in H1. gen H1. case ((E, n) ==np (n0, n1)); intros H1 H2.
  inverts H1. rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. apply IHt; trivial. false.
  simpl in H1. false.
Qed.

Hint Resolve TPith_TPithdel_leq_1.


Lemma TPith_TPithdel_geq_TPlength : forall t E n i j,
                                    TPlength t E n <> 1 ->  
                                    i >= TPlength t E n - 1 -> j >= TPlength t E n  ->
                                    TPith i (TPithdel j t E n) E n = TPith (TPlength t E n - 1) t E n.
Proof.
  intros. gen i j H0 H1. induction t; intros; simpl in H; try omega. 
  assert (Q : TPlength t1 E n >= 1). auto.
  assert (Q' : TPlength t2 E n >= 1). auto.
  simpl in H0. simpl TPlength in *|-*.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H2. 
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPith_Pr_le; try omega.
  replace (TPlength t1 E n + TPlength t2 E n - 1) with
          (TPlength t1 E n); try omega.
  rewrite TPith_overflow; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite 2 TPith_Pr_gt; try omega.
  rewrite IHt2; try omega.
  replace (TPlength t1 E n + TPlength t2 E n - 1 - TPlength t1 E n)
   with (TPlength t2 E n - 1); try omega. trivial.
  gen H. case ((E, n) ==np (n0, n1)); intros H2 H3. inverts H2.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite TPlength_Fc_eq in *|-*.
  rewrite 2 TPith_Fc_eq. rewrite IHt; trivial.
  false.
Qed.


Lemma TPith_TPithdel_geq_TPlength' : forall t E n i j,
                                    TPlength t E n <> 1 ->  
                                    i >= TPlength t E n - 1 -> j < TPlength t E n  ->
                                    TPith i (TPithdel j t E n) E n = TPith (TPlength t E n) t E n.
Proof.
  intros. gen i j H0 H1. induction t; intros; simpl in H; try omega. 
  assert (Q : TPlength t1 E n >= 1). auto.
  assert (Q' : TPlength t2 E n >= 1). auto.
  simpl in H0. simpl TPlength in *|-*.
  case (le_dec j (TPlength t1 E n)); intro H2. 
  case (eq_nat_dec (TPlength t1 E n) 1); intro H3.
  rewrite TPithdel_t1_Pr; trivial.
  rewrite TPith_Pr_gt; try omega.
  rewrite 1 TPith_overflow; try omega.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega; trivial.
  rewrite TPithdel_Pr_le; trivial.
  rewrite 2 TPith_Pr_gt; try omega.
  rewrite TPlength_TPithdel; trivial.
  rewrite TPith_overflow; try omega. 
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega; trivial.  
  rewrite TPlength_TPithdel; try omega.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite 2 TPith_Pr_gt; try omega.
  rewrite IHt2; try omega.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega; trivial.
  gen H. case ((E, n) ==np (n0, n1)); intros H2 H3.
  inverts H2.
  rewrite TPlength_Fc_eq in *|-*.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; try omega; trivial.
  false.
Qed.


Lemma TPith_TPithdel_lt : forall t E n i j, i > 0 -> i < j -> i < TPlength t E n ->  
                                            TPith i (TPithdel j t E n) E n = TPith i t E n.
Proof.
  intros t E n. 
  induction t; intros; simpl in *|-; try omega.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (eq_nat_dec (TPlength t1 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPith_Pr_le with (t1:=t1); try omega.
  rewrite TPith_Pr_le. rewrite IHt1; try omega; trivial.
  rewrite TPlength_TPithdel; try omega; trivial.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H4.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  rewrite TPith_Pr_le; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega.
  case (le_dec i (TPlength t1 E n)); intro H5. 
  rewrite 2 TPith_Pr_le; try omega; trivial.
  rewrite 2 TPith_Pr_gt; try omega; trivial.
  rewrite IHt2; try omega; trivial.
  gen H1. case ((E, n) ==np (n0, n1)); intros H1 H2.
  inverts H1. case (eq_nat_dec (TPlength t n0 n1) 1); intro H1. omega.
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
  case (eq_nat_dec (TPlength t1 E n) 1); intro H3.
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
  case (eq_nat_dec (TPlength t2 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite 2 TPith_Pr_gt; try omega.
  gen_eq ii : (i - TPlength t1 E n); intro Hii.
  replace (i + 1 - TPlength t1 E n) with (ii + 1); try omega.
  rewrite IHt2; try omega; trivial.
  gen H1. case ((E, n) ==np (n0, n1)); intros H1 H2.
  inverts H1. case (eq_nat_dec (TPlength t n0 n1) 1); intro H1. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; trivial. omega.  
Qed.

Hint Resolve TPith_TPithdel_geq.

Lemma TPith_TPithdel_exists : forall i j t E n, TPlength t E n <> 1 ->
                                                exists k, TPith i (TPithdel j t E n) E n = TPith k t E n .
Proof.
  intros. case (le_dec j i); intro H0.
  case (eq_nat_dec i 0); intro H1.
  assert (Q : j = 0). omega.
  rewrite TPith_TPithdel_leq_1; try omega.
  exists 2; trivial.
  case (le_dec (TPlength t E n) i); intro H2.
  case (le_dec (TPlength t E n) j); intro H3.
  rewrite TPith_TPithdel_geq_TPlength; try omega.
  exists (TPlength t E n - 1); trivial.
  rewrite TPith_TPithdel_geq_TPlength'; try omega.
  exists (TPlength t E n); trivial.
  rewrite TPith_TPithdel_geq; try omega.
  exists (i + 1); trivial.
  case (eq_nat_dec i 0); intro H1. rewrite H1.
  rewrite TPith_0. case (eq_nat_dec j 1); intro H2.
  rewrite TPith_TPithdel_leq_1; try omega.
  exists 2; trivial.
  rewrite TPith_TPithdel_lt; try omega.
  exists 1; trivial.
  assert (Q : TPlength t E n >= 1). auto. omega.
  case (le_dec (TPlength t E n) i); intro H2.
  rewrite TPith_TPithdel_geq_TPlength; try omega.
  exists (TPlength t E n - 1); trivial.
  rewrite TPith_TPithdel_lt; try omega.
  exists i; trivial.
Qed.  

Lemma TPithdel_lt_comm : forall t E n i j, i > 0 -> i < j -> j <= TPlength t E n ->
                                           TPithdel i (TPithdel j t E n) E n = TPithdel (j - 1) (TPithdel i t E n) E n.
Proof.
  intros t E n.
  induction t; intros; simpl in *|-; try omega.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (eq_nat_dec (TPlength t1 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_le with (i:=j); try omega.
  rewrite TPithdel_Pr_le with (t1:=t1); try omega.
  case (eq_nat_dec (TPlength t1 E n) 2); intro H4.
  rewrite 2 TPithdel_t1_Pr;
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite 2 TPithdel_Pr_le;
  try rewrite TPlength_TPithdel; try omega; trivial. fequals. 
  rewrite IHt1; try omega; trivial.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H3.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  case (le_dec i (TPlength t1 E n)); intro H4.
  case (eq_nat_dec (TPlength t1 E n) 1); intro H5.
  rewrite TPithdel_t1_Pr with (t1 := t1); try omega.
  rewrite 2 TPithdel_TPlength_1; try omega; trivial.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  rewrite TPlength_TPithdel; try omega. omega.  
  rewrite TPithdel_Pr_gt; try omega.
  case (le_dec i (TPlength t1 E n)); intro H4.
  case (eq_nat_dec (TPlength t1 E n) 1); intro H5.
  rewrite 2 TPithdel_t1_Pr with (i:=i); trivial.
  rewrite H5. trivial.
  rewrite 2 TPithdel_Pr_le with (i:=i); trivial.  
  rewrite TPithdel_Pr_gt;
  try rewrite TPlength_TPithdel; try omega. fequals.
  replace (j - 1 - (TPlength t1 E n - 1)) with
  (j - TPlength t1 E n); try omega; trivial.
  case (eq_nat_dec (TPlength t2 E n) 2); intro H5. 
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
  inverts H1. case (eq_nat_dec (TPlength t n0 n1) 1); intro H1. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite TPithdel_Fc_eq with (t:=t); trivial.
  case (eq_nat_dec (TPlength t n0 n1) 2); intro H3.
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
  case (eq_nat_dec j 0); intro H3; try rewrite H3; repeat rewrite TPithdel_0.  
  rewrite <- TPithdel_lt_comm; try omega; trivial.
  rewrite <- TPithdel_lt_comm; try omega; trivial.
Qed.  
   

Lemma Perm_TPithdel : forall t pi E n i,
 pi @ (TPithdel i t E n) = TPithdel i (pi @ t) E n.
Proof.
  intros. gen i. induction t; intro;
  autorewrite with perm; autorewrite with perm; trivial.
  case (le_dec i (TPlength t1 E n)); intro H1. 
  case (eq_nat_dec (TPlength t1 E n) 1); intro H2.
  rewrite 2 TPithdel_t1_Pr;
  autorewrite with tuples; trivial.
  rewrite 2 TPithdel_Pr_le;
  autorewrite with tuples perm; try omega.
  rewrite IHt1; trivial.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H2.
  rewrite 2 TPithdel_t2_Pr;
  autorewrite with tuples; try omega; trivial.
  rewrite 2 TPithdel_Pr_gt;
  autorewrite with tuples perm; try omega.
  rewrite IHt2; trivial.
  case ((n0,n1) ==np (E,n)); intro H0.
  inverts H0. case (eq_nat_dec (TPlength t E n) 1); intro H0.
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


(** About term_size and TPlength *)


Lemma TPlength_leq_term_size : forall t E n, TPlength t E n <= term_size t.
Proof.
  intros. induction t; simpl; try omega.
  case ((E, n) ==np (n0, n1)); intro H0; omega.
Qed.

Hint Resolve TPlength_leq_term_size.

Lemma term_size_TPith : forall i t E n,
 term_size (TPith i t E n) <= term_size t.
Proof.
 intros. gen i. induction t; intro i.
 simpl; trivial. simpl; trivial. simpl; omega.
 case (le_dec i (TPlength t1 E n)); intro H.
 rewrite TPith_Pr_le; trivial; simpl; trivial.
 assert (Q: term_size (TPith i t1 E n) <= term_size t1). apply IHt1. omega.
 rewrite TPith_Pr_gt; try omega; simpl.
 assert (Q: term_size (TPith (i - TPlength t1 E n) t2 E n) <= term_size t2). apply IHt2. omega. 
 case ((n0,n1) ==np (E,n)); intro H.
 inverts H. rewrite TPith_Fc_eq; trivial. simpl. 
 assert (Q: term_size (TPith i t E n) <= term_size t). apply IHt. omega.
 rewrite TPith_Fc_diff; trivial. simpl; trivial.
Qed.

Hint Resolve term_size_TPith.

Lemma term_size_TPith' : forall i t E n,
 TPlength t E n <> 1 ->                           
 term_size (TPith i t E n) < term_size t.
Proof.
 intros. destruct t;  simpl in *|-; try omega.
 assert (Q0  : TPlength t1 E n >= 1). auto.
 assert (Q1 : TPlength t2 E n >= 1). auto. 
 case (le_dec i (TPlength t1 E n)); intro H0.
 rewrite TPith_Pr_le; trivial; simpl.
 assert (Q2 : term_size (TPith i t1 E n) <= term_size t1). auto. omega.
 rewrite TPith_Pr_gt; try omega; simpl.
 assert (Q2 : term_size (TPith (i - TPlength t1 E n) t2 E n) <= term_size t2). auto. omega.
 gen H. case ((E, n) ==np (n0, n1)); intros H0 H1; try omega.
 inverts H0. rewrite TPith_Fc_eq. simpl.
 assert (Q2 : term_size (TPith i t n0 n1) <= term_size t). auto. omega.
Qed. 


Lemma Fc_TPith_neq : forall i E n t, TPith i (Fc E n t) E n <> Fc E n t. 
Proof.
  intros. rewrite TPith_Fc_eq.
  assert (Q : term_size (TPith i t E n) <= term_size t). auto.
  assert (Q' : term_size (TPith i t E n) < term_size (Fc E n t)). simpl. omega.
  intro H.  rewrite H in Q'. omega.
Qed.

Hint Resolve Fc_TPith_neq.


Lemma term_size_TPithdel : forall i t E n, TPlength t E n <> 1 ->
                                           term_size (TPithdel i t E n) < term_size t.
Proof.
 intros. gen i. induction t; intro i.
 simpl in H; omega. simpl in H; omega. simpl in H; omega.
 case (le_dec i (TPlength t1 E n)); intro H0.
 case (eq_nat_dec (TPlength t1 E n) 1); intro H1.
 rewrite TPithdel_t1_Pr; trivial. 
 rewrite TPithdel_Pr_le; trivial; simpl; trivial.
 assert (Q: term_size (TPithdel i t1 E n) < term_size t1). apply IHt1; trivial. omega.
 case (eq_nat_dec (TPlength t2 E n) 1); intro H1.
 rewrite TPithdel_t2_Pr; try omega. simpl; omega.
 rewrite TPithdel_Pr_gt; try omega; simpl.
 assert (Q: term_size (TPithdel (i - TPlength t1 E n) t2 E n) < term_size t2). apply IHt2; trivial. omega.
 assert (Q:term_size t > 0). auto.
 case ((n0,n1) ==np (E,n)); intro H0.
 inverts H0. case (eq_nat_dec (TPlength t E n) 1); intro H0.
 rewrite TPithdel_TPlength_1; autorewrite with tuples; simpl; try omega; trivial.
 rewrite TPithdel_Fc_eq; trivial. simpl. 
 assert (Q': term_size (TPithdel i t E n) < term_size t). apply IHt; trivial. omega.
 rewrite TPithdel_Fc_diff; trivial. simpl. omega.
 simpl in H. omega.
Qed.

Hint Resolve term_size_TPithdel.

Lemma term_size_TPithdel' : forall i t E n, term_size (TPithdel i t E n) <= term_size t.
Proof.
  intros. case (eq_nat_dec (TPlength t E n) 1); intro H.
  rewrite TPithdel_TPlength_1; trivial. simpl.
  assert (Q : term_size t > 0). auto. omega.
  assert (Q : term_size (TPithdel i t E n) < term_size t).
   apply term_size_TPithdel; trivial. 
  omega.
Qed. 

Hint Resolve term_size_TPithdel'.


Lemma Fc_TPithdel_neq : forall i E n t, TPithdel i (Fc E n t) E n <> Fc E n t. 
Proof.
  intros. case (eq_nat_dec (TPlength (Fc E n t) E n) 1); intro H.
  rewrite TPithdel_TPlength_1; trivial. discriminate.
  rewrite TPlength_Fc_eq in H. rewrite TPithdel_Fc_eq; trivial.
  intro H0. inverts H0. 
  assert (Q : term_size (TPithdel i t E n) < term_size t).
   apply term_size_TPithdel; trivial. 
  rewrite H2 in Q.
  omega.
Qed.

Hint Resolve Fc_TPithdel_neq.

Lemma term_size_TPith_TPithdel : forall i t E n,
 TPlength t E n <> 1 ->
 term_size (TPith i t E n) + term_size (TPithdel i t E n) < term_size t.
Proof.
  intros. gen i. induction t; intro; simpl in H.
  false. false. false. 
  case (le_dec i (TPlength t1 E n)); intro H0.
  rewrite TPith_Pr_le; trivial.
  assert (Q0 : term_size (TPith i t1 E n) <= term_size t1). auto. 
  case (eq_nat_dec (TPlength t1 E n) 1); intro H1. 
  rewrite TPithdel_t1_Pr; trivial. simpl. omega.
  rewrite TPithdel_Pr_le; trivial; simpl; trivial.
  apply IHt1 with (i:=i) in H1. omega.
  rewrite TPith_Pr_gt; try omega.
  assert (Q0 : term_size (TPith (i - TPlength t1 E n) t2 E n) <= term_size t2). auto.  
  case (eq_nat_dec (TPlength t2 E n) 1); intro H1.
  rewrite TPithdel_t2_Pr; try omega. simpl; omega.
  rewrite TPithdel_Pr_gt; try omega; simpl. 
  apply IHt2 with (i := i - TPlength t1 E n) in H1. omega.
  gen H. case ((E, n) ==np (n0, n1)); intros. inverts e.
  rewrite TPith_Fc_eq. rewrite TPithdel_Fc_eq; trivial. simpl.
  apply IHt with (i:=i) in H. omega. false. false.
Qed.


(** About rpl_super, set_super, is_Pr, TPlength, TPith and TPithdel *)

Lemma rpl_super_is_Pr : forall s S E, is_Pr s <-> is_Pr (rpl_super S E s). 
Proof.
  split~; intros;
  destruct s; simpl in *|-*; try contradiction; trivial.
  gen H. case (set_In_dec Nat.eq_dec n S); simpl; intros; trivial.
Qed.
  
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
  case (eq_nat_dec (TPlength t1 E n) 1); intro H2.
  rewrite TPithdel_t1_Pr; trivial. simpl rpl_super.
  rewrite TPithdel_t1_Pr; try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Pr_le; trivial. simpl rpl_super.
  rewrite TPithdel_Pr_le; try rewrite TPlength_rpl_super; trivial. rewrite IHt1; trivial.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H2.
  rewrite TPithdel_t2_Pr; try omega. simpl rpl_super.
  rewrite TPithdel_t2_Pr; try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega. simpl rpl_super.
  rewrite TPithdel_Pr_gt; try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite IHt2; trivial.
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1. autorewrite with tuples.
  simpl. case (set_In_dec eq_nat_dec E S0); intro H1; try contradiction.
  case ((E, n) ==np (E, n)); intro H2.
  case (eq_nat_dec (TPlength t E n) 1); intro H3; trivial.
  rewrite TPithdel_TPlength_1;
  autorewrite with tuples; try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Fc_eq; try rewrite TPlength_rpl_super; trivial.
  simpl. case (set_In_dec eq_nat_dec E S0); intro H4; try contradiction.
  rewrite IHt; trivial. false. 
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
  case (eq_nat_dec (TPlength t1 E n) 1); intro H1.
  rewrite TPithdel_t1_Pr in H; trivial.
  apply set_union_intro2; trivial.
  rewrite TPithdel_Pr_le in H; trivial. simpl in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply (IHt1 i); trivial.
  apply set_union_intro2; trivial.
  case (eq_nat_dec (TPlength t2 E n) 1); intro H1.
  rewrite TPithdel_t2_Pr in H; try omega.
  apply set_union_intro1; trivial.
  rewrite TPithdel_Pr_gt in H; try omega. simpl in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  apply (IHt2 (i - TPlength t1 E n)); trivial.
  case ((n0,n1) ==np (E,n)); intro H1. inverts H1.
  case (eq_nat_dec (TPlength t E n) 1); intro H1.
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


(*******************************************)

Lemma TPith_TPith : forall i j t E n,
                    TPith i (TPith j t E n) E n = TPith j t E n .  
Proof.
  intros. gen i j. induction t; intros; simpl; trivial.
  case (le_dec j (TPlength t1 E n)); intro H.
  rewrite IHt1; trivial. rewrite IHt2; trivial.
  case ((E, n) ==np (n0, n1)); intro H. rewrite IHt; trivial.
  rewrite TPith_Fc_diff; trivial.
  intro H'. symmetry in H'. contradiction.
Qed.  


(** Lemmas about the counting of number of function symbols *)

Lemma func_symbols_perm : forall pi t, func_symbols_term (pi @ t) = func_symbols_term t.
Proof.
  intros. induction t; autorewrite with perm; simpl; trivial.
  rewrite IHt1. rewrite IHt2. trivial.
  rewrite IHt. trivial.
Qed.

Lemma func_symbols_term_TPith : forall i s E n,
    func_symbols_term (TPith i s E n) <= func_symbols_term s.
Proof.
  intros. gen i. induction s; intros; simpl; try omega.
  case (le_dec i (TPlength s1 E n)); intro H0.
  assert (Q : func_symbols_term (TPith i s1 E n) <= func_symbols_term s1). auto.
  omega.
  assert (Q : func_symbols_term (TPith (i - TPlength s1 E n) s2 E n) <= func_symbols_term s2). auto.
  omega.
  case ((E, n) ==np (n0, n1)); intro H0; auto.
  assert (Q : func_symbols_term (TPith i s E n) <= func_symbols_term s). auto. 
  omega.
Qed.


Lemma func_symbols_term_TPithdel : forall i s E n,
    func_symbols_term (TPithdel i s E n) <= func_symbols_term s.
Proof.
  intros. gen i. induction s; intros; simpl; try omega.
  case (le_dec i (TPlength s1 E n)); intro H0.
  case (eq_nat_dec (TPlength s1 E n) 1); intro H1. omega.
  simpl.
  assert (Q : func_symbols_term (TPithdel i s1 E n) <= func_symbols_term s1). auto.
  omega.
  case (eq_nat_dec (TPlength s2 E n) 1); intro H1. omega.
  simpl.
  assert (Q : func_symbols_term (TPithdel (i - TPlength s1 E n) s2 E n) <= func_symbols_term s2). auto.
  omega.
  case ((E, n) ==np (n0, n1)); intro H0.
  case (eq_nat_dec (TPlength s E n) 1); intro H1. simpl. omega.
  simpl.
  assert (Q : func_symbols_term (TPithdel i s E n) <= func_symbols_term s). auto. 
  omega.
  case (eq_nat_dec 1 1); intro H1. simpl; omega. false.
Qed.


(** Lemmas about Colections of arguments over terms *)

Lemma valid_col_nil : forall t E n, valid_col ([]) t E n.
Proof.
  intros. unfold valid_col.
  split~; intros. apply NoDup_nil.
  simpl in H. contradiction.
Qed.
  
Lemma valid_col_cons : forall a L t E n,
      valid_col (a :: L) t E n -> (valid_col L t E n /\ a >= 1 /\ a <= TPlength t E n).
Proof.
  intros. split~.
  unfold valid_col in *|-*.
  destruct H. split~; intros. inverts H; trivial.
  apply H0. right~.
  apply H. left~.
Qed.

Lemma length_nat_seq : forall n, length (nat_seq n) = n.
Proof.
  intros. induction n; simpl; omega.
Qed.  
  

Lemma nat_seq_limit : forall n k, In n (nat_seq k) <-> ((n <> 0) /\ n <= k).
Proof.
  intros. gen n. induction k; intro; simpl; split~; intro.
  contradiction. destruct H. omega.
  destruct H. split~; omega.
  apply IHk in H. destruct H. split~.
  case (eq_nat_dec n (S k)); intro H'.
  left~. right~. apply IHk.
  destruct H. split~. omega.
Qed.

Lemma NoDup_nat_seq : forall n, NoDup (nat_seq n).
Proof.
  intros. induction n; simpl.
  apply NoDup_nil. apply NoDup_cons; trivial.
  intro H. apply nat_seq_limit in H.
  destruct H. omega.
Qed.  
  
Lemma valid_col_nat_seq : forall L t E n,
      valid_col L t E n <-> (NoDup L /\ (forall a, In a L -> In a (nat_seq (TPlength t E n)))).
Proof.
  intros. unfold valid_col.
  split~; intros. destruct H.
  split~; intros. apply nat_seq_limit.
  apply H0 in H1. destruct H1.
  split~; omega.
  destruct H. split~; intros.
  apply H0 in H1. apply nat_seq_limit in H1.
  destruct H1. split~; omega.
Qed.


Lemma valid_col_length_limit : forall t E n L,
      valid_col L t E n ->
      length L <= TPlength t E n  .
Proof.
  intros. replace (TPlength t E n) with (length (nat_seq (TPlength t E n))).
  apply subset_list.
  apply eq_nat_dec. apply H.
  intros. apply valid_col_nat_seq in H.  
  destruct H. apply H1 in H0; trivial.
  apply  length_nat_seq.
Qed.  

Lemma valid_col_In_nat_seq : forall t E n L,
      valid_col L t E n ->
      length L = TPlength t E n ->
      forall a, In a (nat_seq (TPlength t E n)) -> In a L .
Proof.
  intros t E n L H H0.
  unfold valid_col in H.
  destruct H.  
  apply subset_list_eq'; trivial.
  apply eq_nat_dec.
  apply NoDup_nat_seq.
  rewrite <- H0.
  rewrite length_nat_seq; trivial.
  intros. apply H1 in H2.
  destruct H2.
  apply nat_seq_limit.
  split~. omega.
Qed.  


Lemma Args_col_list_length : forall L t E n,
                                    
      length (Args_col_list L t E n) = length L .

Proof.
  intros. induction L; simpl; omega.
Qed.


Lemma Args_col_list_TPith : forall L t t0 E n,
      In t0 (Args_col_list L t E n) ->
      exists i, In i L /\ t0 = TPith i t E n.
Proof.
  intros. induction L; simpl in H.
  contradiction. destruct H.
  exists a. split~. left~.
  apply IHL in H. case H; clear H; intros i H.
  destruct H. exists i. split~. right~.
Qed.
  
Lemma Args_right_assoc_TPlength : forall L t E n,

      length L <> 0 ->
    
      TPlength (Args_right_assoc (Args_col_list L t E n)) E n

      = length L.
Proof.
  intros.
  gen_eq l : (length L). intro H0.
  gen H0 H. gen L t. 
  induction l using peano_induction; intros.
  destruct L. simpl in H0. contradiction.
  case (nil_eqdec _ L); intro H2.
  rewrite H2 in *|-*. simpl in *|-*.
  rewrite TPlength_TPith. symmetry. trivial.
  simpl in H0. simpl Args_col_list.
  assert (Q : Args_col_list L t E n <> []).
   intro H3. apply H2.
   assert (Q : length L = 0).
    rewrite <- Args_col_list_length
             with (t:=t) (E:=E) (n:=n).
    rewrite H3. simpl. trivial.
  rewrite length_zero_iff_nil in Q; trivial.
  gen_eq Lt : (Args_col_list L t E n); intro H3.
  simpl. destruct Lt. false.
  rewrite H3. simpl.
  rewrite TPlength_TPith.
  rewrite H with (m := length L); try omega.
  intro H4. apply length_zero_iff_nil in H4.   
  contradiction.
Qed.

                            
Lemma Args_right_assoc_cons : forall t L, 

      length L <> 0  ->

      Args_right_assoc (t :: L) = <|t, Args_right_assoc L|> .
Proof.
  intros. simpl. destruct L; trivial.
  simpl in H. false.
Qed.  

Lemma Agrs_right_assoc_TPlength_append : forall L0 L1 E n,
      
      length L0 <> 0 -> length L1 <> 0 ->

      TPlength (Args_right_assoc L0) E n +
      TPlength (Args_right_assoc L1) E n =

      TPlength (Args_right_assoc (L0 ++ L1)) E n .

Proof.
  intros.
  gen_eq l : (length L0 + length L1).
  intro H1. gen H1 H H0. gen L0 L1.
  induction l using peano_induction; intros.
  destruct L0. simpl in H0. false.
  simpl in H1. simpl app.
  case (nil_eqdec _ L0); intro H3.
  rewrite H3. simpl app.
  rewrite Args_right_assoc_cons with (L:=L1); trivial.
  assert (Q : length L0 <> 0).
   intro H4. apply H3.
   apply length_zero_iff_nil. trivial.
  rewrite 2 Args_right_assoc_cons; trivial.
  simpl. rewrite <- H with (m := length L0 + length L1); simpl;
         try omega.
  destruct L0. simpl; trivial.
  simpl. omega.
Qed.


Lemma assoc_TPlength : forall L L' E n,
      TPlength (Args_right_assoc L) E n = TPlength (Args_assoc L' L) E n.
Proof.
  intros. gen_eq l : (length L).
  intro H. gen H. gen L L'.
  induction l using peano_induction; intros.
  destruct L; simpl. destruct L'; simpl; trivial.
  destruct n0; trivial.
  destruct L. destruct L'; simpl; trivial.
  destruct n0; trivial.
  gen_eq Lt : (t0 :: L); intro H1. simpl in H0.
  destruct L'. simpl.
  destruct Lt. inverts H1. simpl; trivial.
  destruct n0. simpl.
  destruct Lt. inverts H1. simpl; trivial.
  simpl. case (lt_dec n0 (length Lt)); intro H2.
  simpl. Focus 2. destruct Lt. inverts H1. simpl; trivial.
  destruct n0. simpl.
  rewrite <- H with (m := 1); simpl; trivial.
  rewrite H1 in H0. simpl in H0. omega.
  gen_eq L0 : (head_list term (S n0) Lt).
  gen_eq L1 : (tail_list term (S n0) Lt).
  intros H3 H4. 
  rewrite <- H with (m := S (length L0)); simpl; trivial.
  destruct L0.
  symmetry in H4.
  apply head_list_not_nil in H4; try omega.
  gen_eq L2 : (t1 :: L0); intro H5.
  simpl. replace Lt with (L2 ++ L1).
  rewrite <- Agrs_right_assoc_TPlength_append. omega.
  destruct L2. inverts H5. simpl. omega.
  assert (Q : length L1 = length Lt - S n0).
   rewrite H3. apply tail_list_length. omega.
  omega. symmetry. apply head_tail_append with (n:=S n0); trivial.
  assert (Q : length L0 = S n0).
   rewrite H4. apply head_list_length. omega.
  omega. 
Qed.
  
  
Lemma Args_col_TPlength : forall L L' t E n,
      length L <> 0 ->
      TPlength (Args_col L L' t E n) E n = length L.
Proof.
  intros. unfold Args_col.
  rewrite <- assoc_TPlength.
  rewrite  Args_right_assoc_TPlength; trivial.
Qed.
