(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Tuples.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation

 Description : This file contains specification of the operators 
               length, selection and deletion of tuple arguments, 
               and other definitions and results about tuples. 
 
 Last Modified On: Set 17, 2018.
 ============================================================================
 *)

Require Export Perm.


(** Computes the length of a tuple regarding the nth E function symbol *)

Fixpoint TPlength (t: term) (E n: nat) : nat :=
match t with 
 | (<|t1,t2|>)    => (TPlength t1 E n) + (TPlength t2 E n) 
 | (Fc E0 n0 t1)  => if eq_nat_rec E E0 && eq_nat_rec n n0
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

 | (Fc E0 n0 t0) => if eq_nat_rec E E0 && eq_nat_rec n n0
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
                      if eq_nat_rec l1 1
                      then t2 
                      else <|(TPithdel i t1 E n),t2|>
                    else
                      let ii := i-l1 in   
                        if eq_nat_rec l2 1
                        then t1
                        else <|t1,(TPithdel ii t2 E n)|> 

 | (Fc E0 n0 t0) => if eq_nat_rec (TPlength (Fc E0 n0 t0) E n) 1
                    then <<>>
                    else Fc E0 n0 (TPithdel i t0 E n)                          
                               
 | _ => <<>>
end.

  

(** Replaces all superscripts m in S0 by m0 *) 

Fixpoint rpl_super (S0 : set nat) (E0: nat) (t:term) : term :=
match t with
  | Fc E n s  => if (set_In_dec nat_eqdec E S0) then
                   Fc (E + E0 + 1) n (rpl_super S0 E0 s)
                 else Fc E n (rpl_super S0 E0 s)  
  | [a]^s     => [a]^(rpl_super S0 E0 s)
  | <|s1,s2|> => <|rpl_super S0 E0 s1, rpl_super S0 E0 s2|>
  | _         => t
end.                   


(** Computes the set of superscripts that occur in t *)

Fixpoint set_super (t:term) : set nat :=
  match t with
    | Fc E n s => set_add nat_eqdec E (set_super s)
    | [a]^s => set_super s
    | <|s1,s2|> => set_union nat_eqdec (set_super s1) (set_super s2)
    | _ => []                                                  
  end.



(** Generates a colection of arguments of a given funcion symbol based in a 
    list of indexes *)

              
Fixpoint Args_col_list (L : list nat) (t : term) (E n: nat) : list term :=

  match L with

   | [] => []
            
   | i::L0 => TPith i t E n :: (Args_col_list L0 t E n) 
             
  end.

(** Build a tuple right associative based in a list of terms *)

Fixpoint Args_right_assoc (Lt : list term) : term :=

  match Lt with

  | [] => <<>>

  | |[t]| => t

  | t :: Lt0 => <| t, Args_right_assoc Lt0 |>

  end.                                      

(** Build a tuple with an arbitrary associativity based in a list of 
    indexes and a list of terms *)

 Fixpoint Args_assoc (i : nat) (L : list nat) (Lt : list term) : term :=

  match L with

  | n :: L0  => <| Args_right_assoc (head_list _ (n - i) Lt),
                   Args_assoc n L0 (tail_list _ (n - i) Lt) |>
                                                      
  | _   => Args_right_assoc Lt
                                                                       
  end.

(** Verifies if a list of naturals L is sorted *) 

 Fixpoint sorted_nat_list (L : list nat) : Prop :=

   match L with
     
   | [] => True          

   | n0 :: L0 => if le_dec n0 (hd 0 L0)
                 then sorted_nat_list L0
                 else False

   end.                     

(** A valid associativity of t is a sorted list of 
    of naturals without duplicates and where the elements 
    are between 1 and TPlength t E n *)
 
Definition valid_assoc (L : list nat) (t : term) (E n : nat) :=

  NoDup L /\ sorted_nat_list L /\

  forall a, In a L -> a >= 1 /\ a < TPlength t E n .

(** A valid collection of indexes of t is a list of 
    naturals without duplicates and where the elements
    are  between 1 and TPlength t E n *) 


Definition valid_col (L : list nat) (t : term) (E n : nat) :=

  NoDup L /\

  forall a, In a L -> a >= 1 /\ a <= TPlength t E n .


(** A collection of arguments of t is defined based 
    on two list of indexes, one for the associativity L' and
    other for the selected arguments L *)

Definition Args_col (L L' : list nat) (t : term) (E n : nat) :=

  Args_assoc 0 L' (Args_col_list L t E n) . 



(* TPlength properties *)

Lemma TPlength_1_le : forall t E n, 1 <= TPlength t E n .
Proof.
  intros; induction t; 
  simpl; try apply le_n. 
  apply le_trans' with (l := TPlength t1 E n); trivial. apply le_plus. 
  case (nat_eqdec E n0); intro H0. rewrite <- H0. rewrite eq_nat_refl.
  case (nat_eqdec n n1); intro H1. rewrite <- H1. rewrite eq_nat_refl.
  simpl; trivial. apply eq_nat_diff in H1. rewrite H1.
  simpl. apply le_n.
  apply eq_nat_diff in H0. rewrite H0. simpl. apply le_n. 
Defined.

Lemma TPlength_ge_1 : forall t E n, TPlength t E n >= 1.
Proof.
  intros. unfold ge. apply TPlength_1_le.
Defined.

Hint Resolve TPlength_1_le.
Hint Resolve TPlength_ge_1.

Lemma TPlength_Fc_eq : forall E n t,
      TPlength (Fc E n t) E n = TPlength t E n.
Proof.
  intros; simpl.
  rewrite 2 eq_nat_refl.
  simpl; trivial.
Defined. 
  
Hint Rewrite TPlength_Fc_eq : tuples.

Lemma TPlength_Fc_diff : forall E E' n n' t,
      (E, n) <> (E', n') ->
      TPlength (Fc E n t) E' n' = 1.
Proof.
  intros; simpl.
  case (nat_eqdec E' E); intro H0.
  case (nat_eqdec n' n); intro H1.
  rewrite H0 in H. rewrite H1 in H.
  apply False_ind. apply H. trivial.
  rewrite eq_nat_diff in H1. rewrite H1.
  rewrite andb_false_r; trivial.
  rewrite eq_nat_diff in H0. rewrite H0.
  simpl; trivial.
Defined.

Hint Resolve TPlength_Fc_diff.

Lemma Perm_TPlength : forall t E n pi, 
 TPlength (pi @@ t) E n = TPlength t E n. 
Proof.
  intros. induction t.
  simpl; trivial. simpl; trivial. simpl; trivial.  
  simpl. rewrite IHt1. rewrite IHt2. trivial.
  simpl perm_act. 
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H.
  inverts H. rewrite 2 TPlength_Fc_eq; trivial.
  rewrite 2 TPlength_Fc_diff; trivial.
  simpl; trivial. 
Defined.

Hint Rewrite Perm_TPlength : tuples.

Lemma TPith_Fc_eq : forall i t E n,
      TPith i (Fc E n t) E n = TPith i t E n.
Proof.
  intros. simpl.
  rewrite 2 eq_nat_refl.
  simpl; trivial.
Defined.

Hint Rewrite TPith_Fc_eq : tuples.

Lemma TPith_Fc_diff : forall i t E E' n n',
      (E, n) <> (E', n') ->
      TPith i (Fc E n t) E' n' = Fc E n t.
Proof.
  intros. simpl.
  case (nat_eqdec E' E); intro H0.
  case (nat_eqdec n' n); intro H1.
  rewrite H0 in H. rewrite H1 in H.
  apply False_ind. apply H. trivial.
  rewrite eq_nat_diff in H1. rewrite H1.
  rewrite andb_false_r; trivial.
  rewrite eq_nat_diff in H0. rewrite H0.
  simpl; trivial.
Defined.


Lemma TPlength_TPith : forall t E n i, TPlength (TPith i t E n) E n = 1.
Proof.
  intros t E n. induction t; intros.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl. case (le_dec i (TPlength t1 E n)); intro H. 
  rewrite IHt1; trivial. rewrite IHt2; trivial.
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H.
  inverts H. rewrite TPith_Fc_eq. apply IHt.
  rewrite TPith_Fc_diff; trivial.
  rewrite TPlength_Fc_diff; trivial.
  simpl. trivial.
Defined.

Hint Rewrite TPlength_TPith : tuples.


Lemma TPith_0 : forall t E n,
      TPith 0 t E n = TPith 1 t E n.
Proof.
  intros. induction t; simpl; trivial.
  case (le_dec 1 (TPlength t1 E n)); intro H; trivial.
  apply False_ind. apply H. apply TPlength_1_le.
  rewrite IHt; trivial.
Defined.

Hint Rewrite TPith_0 : tuples.

Lemma TPith_Pr_le : forall i t1 t2 E n, 
 i <= TPlength t1 E n -> TPith i (<|t1,t2|>) E n = TPith i t1 E n. 
Proof.
 intros; simpl; 
 case (le_dec i (TPlength t1 E n)); 
 intro H0; try contradiction; trivial. 
Defined.

Hint Resolve TPith_Pr_le.

Lemma TPith_Pr_gt : forall i t1 t2 E n,
 i >  TPlength t1 E n -> 
 TPith i (<|t1,t2|>) E n = TPith (i - (TPlength t1 E n)) t2 E n.
Proof.
 intros; simpl; 
 case (le_dec i (TPlength t1 E n)); intro H0; trivial. 
 unfold gt in H. unfold lt in H.
 assert (Q : S (TPlength t1 E n) <= (TPlength t1 E n)).
  apply le_trans' with (l:=i); trivial.
 apply Sn_le in Q. contradiction.
Defined.

Hint Resolve TPith_Pr_gt.


Lemma TPith_TPith : forall i j t E n,
                    TPith i (TPith j t E n) E n = TPith j t E n .  
Proof.
  intros. gen i j. induction t; intros.
  simpl; trivial. simpl; trivial. simpl; trivial.
  case (le_dec j (TPlength t1 E n)); intro H.
  rewrite TPith_Pr_le; trivial.
  apply neg_le in H. rewrite TPith_Pr_gt; trivial.
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H.
  inverts H. autorewrite with tuples; trivial.
  rewrite 2 TPith_Fc_diff; trivial.
  simpl; trivial.
Qed. 

Hint Rewrite TPith_TPith : tuples.

Lemma Perm_TPith : forall t pi E n i,
 pi @ (TPith i t E n) = TPith i (pi @ t) E n.
Proof.
  intros. gen i. induction t; intros.
  simpl; trivial. simpl; trivial.
  simpl; trivial. simpl.
  rewrite Perm_TPlength.
  case (le_dec i (TPlength t1 E n)); intro H.
  rewrite IHt1; trivial. rewrite IHt2; trivial.
  replace (pi @ Fc n0 n1 t) with (Fc n0 n1 (pi @ t)).    
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H.
  inverts H. rewrite 2 TPith_Fc_eq. apply IHt.
  rewrite 2 TPith_Fc_diff; trivial. simpl; trivial.
  simpl; trivial.
Defined.

Hint Rewrite Perm_TPith : tuples.

Lemma TPithdel_TPlength_1 : forall i t E n, 
 TPlength t E n = 1 -> TPithdel i t E n = <<>>.
Proof.
 intros. destruct t; simpl; trivial. 
 apply False_ind. simpl in H.
 assert (Q: 1 <= TPlength t1 E n /\ 1 <= TPlength t2 E n).
 split; apply TPlength_1_le. destruct Q.
 inversion H0. 
 rewrite <- H3 in H.
 inversion H1.
 rewrite <- H4 in H.
 simpl in H. inversion H.
 rewrite <- H2 in H. simpl in H. inversion H. 
 rewrite <- H2 in H.
 inversion H1. rewrite <- H5 in H. simpl in H.
 rewrite plus_com in H. simpl in H. inversion H.
 rewrite <- H4 in H. simpl in H.
 rewrite plus_com in H. simpl in H. inversion H.
 generalize H. clear H. simpl.
 case (nat_eqdec E n0); intro H. rewrite <- H. rewrite eq_nat_refl.
 case (nat_eqdec n n1); intro H0. rewrite <- H0. rewrite eq_nat_refl.
 simpl; intro H1. rewrite H1. rewrite eq_nat_refl; trivial.
 apply eq_nat_diff in H0. rewrite H0. simpl. intro; trivial.
 apply eq_nat_diff in H. rewrite H. simpl. intro; trivial.  
Defined.

Lemma TPithdel_Fc_eq : forall i t E n, 
 TPlength t E n <> 1 ->
 TPithdel i (Fc E n t) E n = Fc E n (TPithdel i t E n).
Proof. 
 intros. simpl.
 rewrite 2 eq_nat_refl. simpl.
 apply eq_nat_diff in H. rewrite H. trivial.
Defined.

Lemma TPithdel_Fc_diff : forall i t E E' n n',
      (E, n) <> (E', n') ->
      TPithdel i (Fc E n t) E' n' = <<>>.
Proof.
  intros. rewrite TPithdel_TPlength_1; trivial.
  rewrite TPlength_Fc_diff; trivial.
Defined.

Lemma TPithdel_0 : forall t E n, TPithdel 0 t E n = TPithdel 1 t E n.
Proof.
  intros. induction t.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl. case (nat_eqdec (TPlength t1 E n) 1); intro H.
  rewrite H. rewrite eq_nat_refl. case (le_dec 1 1); intro H0; trivial.
  apply False_ind. apply H0. apply le_n.
  apply eq_nat_diff in H. rewrite H.
  case (le_dec 1 (TPlength t1 E n)); intro H0.
  rewrite IHt1. trivial.
  assert (Q : 1 <= TPlength t1 E n). apply TPlength_1_le.
  contradiction.
  case (nat_eqdec (TPlength (Fc n0 n1 t) E n) 1); intro H.
  rewrite 2 TPithdel_TPlength_1; trivial.  
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H0.
  generalize H; clear H.
  inversion H0; intro H.
  rewrite TPlength_Fc_eq in H.
  rewrite 2 TPithdel_Fc_eq; trivial.
  f_equal; trivial.
  rewrite TPlength_Fc_diff in H; trivial.
  apply False_ind. apply H; trivial.
  simpl; trivial.
Defined. 

Hint Rewrite TPithdel_0 : tuples.

Lemma TPithdel_t1_Pr : forall i t1 t2 E n,
      i <= TPlength t1 E n -> TPlength t1 E n = 1 ->
      TPithdel i (<|t1,t2|>) E n = t2. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try contradiction.
  rewrite H0. rewrite eq_nat_refl. trivial.
Defined.

Hint Resolve TPithdel_t1_Pr.

Lemma TPithdel_t2_Pr : forall i t1 t2 E n,
      i > TPlength t1 E n -> TPlength t2 E n = 1 ->
      TPithdel i (<|t1,t2|>) E n = t1. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1.
  assert (Q : S (TPlength t1 E n) <=  TPlength t1 E n).
   apply le_trans' with (l:=i); trivial.
  apply Sn_le in Q. contradiction.
  case (nat_eqdec (TPlength t2 E n) 1); intro H2.
  rewrite H2. rewrite eq_nat_refl; trivial.
  contradiction.
Defined.

Hint Resolve TPithdel_t2_Pr.

Lemma TPithdel_Pr_le : forall i t1 t2 E n,
      i <= TPlength t1 E n -> TPlength t1 E n <> 1 ->
      TPithdel i (<|t1,t2|>) E n = <|(TPithdel i t1 E n),t2|>. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1; try contradiction.
  apply eq_nat_diff in H0. rewrite H0; trivial.
Defined.

Hint Resolve TPithdel_Pr_le.

Lemma TPithdel_Pr_gt : forall i t1 t2 E n,
      i > TPlength t1 E n -> TPlength t2 E n <> 1 ->
      TPithdel i (<|t1,t2|>) E n =
      <|t1,(TPithdel (i - TPlength t1 E n) t2 E n)|>. 
Proof.
  intros; simpl.
  case (le_dec i (TPlength t1 E n)); intro H1.
  assert (Q : S (TPlength t1 E n) <=  TPlength t1 E n).
   apply le_trans' with (l:=i); trivial.
  apply Sn_le in Q. contradiction.
  apply eq_nat_diff in H0. rewrite H0; trivial.
Defined.

Hint Resolve TPithdel_Pr_gt.


Lemma Perm_TPithdel : forall t pi E n i,
 pi @ (TPithdel i t E n) = TPithdel i (pi @ t) E n.
Proof.
  intros. gen i. induction t; intro.
  simpl; trivial. simpl; trivial.
  simpl; trivial.
  replace (pi @ (<|t1, t2|>)) with (<|pi @ t1, pi @ t2|>).
  case (le_dec i (TPlength t1 E n)); intro H. 
  case (nat_eqdec (TPlength t1 E n) 1); intro H0.
  rewrite 2 TPithdel_t1_Pr; try rewrite Perm_TPlength; trivial.
  rewrite 2 TPithdel_Pr_le; try rewrite Perm_TPlength; trivial.
  simpl. rewrite IHt1; trivial.
  apply neg_le in H.
  case (nat_eqdec (TPlength t2 E n) 1); intro H0.
  rewrite 2 TPithdel_t2_Pr; try rewrite Perm_TPlength; trivial.
  rewrite 2 TPithdel_Pr_gt; try rewrite Perm_TPlength; trivial.
  simpl. rewrite IHt2; trivial. simpl; trivial.
  replace (pi @ Fc n0 n1 t) with (Fc n0 n1 (pi @ t)).
  case (nat_pair_eqdec (n0,n1) (E,n)); intro H.
  inverts H. 
  case (nat_eqdec (TPlength t E n) 1); intro H.
  rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_eq;
    try rewrite Perm_TPlength; trivial.
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_Fc_eq;
    try rewrite Perm_TPlength; trivial.
  simpl. rewrite IHt; trivial.
  rewrite 2 TPithdel_Fc_diff; trivial. simpl; trivial. 
  simpl; trivial.    
Defined. 

Hint Rewrite Perm_TPithdel : tuples. 


(** About term_size, TPlength, TPith and TPithdel *)

Lemma term_size_TPith : forall i t E n,
 term_size (TPith i t E n) <= term_size t.
Proof.
 intros. generalize i. clear i. induction t; intro i.
 simpl; trivial. simpl; trivial. simpl; trivial.
 case (le_dec i (TPlength t1 E n)); intro H.
 rewrite TPith_Pr_le; trivial. simpl.
 apply le_S. apply le_trans' with (l := term_size t1).
 apply IHt1. apply le_plus.
 apply neg_le in H. rewrite TPith_Pr_gt; trivial. simpl.
 apply le_S. apply le_trans' with (l := term_size t2).
 apply IHt2. rewrite plus_com. apply le_plus.
 case (nat_pair_eqdec (n0, n1) (E, n)); intro H.
 inverts H. rewrite TPith_Fc_eq. simpl.
 apply le_S. apply IHt.
 rewrite TPith_Fc_diff; trivial.
 simpl; trivial.
Defined.

Lemma term_size_TPithdel : forall i t E n,
 TPlength t E n <> 1 ->   
 term_size (TPithdel i t E n) < term_size t.
Proof.
 intros. unfold lt.
 generalize i. clear i. induction t; intro i.
 simpl in H. apply False_ind. apply H; trivial.
 simpl in H. apply False_ind. apply H; trivial.
 simpl in H. apply False_ind. apply H; trivial.
 clear H. 
 case (le_dec i (TPlength t1 E n)); intro H.
 case (nat_eqdec (TPlength t1 E n) 1); intro H0.
 rewrite TPithdel_t1_Pr; trivial.
 simpl. apply -> le_Sn. rewrite plus_com. apply le_plus.
 rewrite TPithdel_Pr_le; trivial. simpl.
 apply -> le_Sn. 
 replace (S (term_size (TPithdel i t1 E n) + term_size t2)) with
     (S (term_size (TPithdel i t1 E n)) +  term_size t2). 
 apply le_plus'. apply IHt1; trivial. 
 simpl. trivial.
 apply neg_le in H.
 case (nat_eqdec (TPlength t2 E n) 1); intro H0.
 rewrite TPithdel_t2_Pr; trivial.
 simpl. apply -> le_Sn. apply le_plus.
 rewrite TPithdel_Pr_gt; trivial. simpl.
 apply -> le_Sn. 
 replace (S (term_size t1 +
            term_size (TPithdel (i - TPlength t1 E n) t2 E n))) with
           (term_size t1 +
             S (term_size (TPithdel (i - TPlength t1 E n) t2 E n))).
 rewrite plus_com. rewrite plus_com with (m:=term_size t1).
 apply le_plus'. apply IHt2; trivial. 
 rewrite plus_com. rewrite plus_com with (m:=term_size t1). simpl. trivial.
 case (nat_pair_eqdec (n0, n1) (E, n)); intro H0.
 generalize H; clear H.  inversion H0.
 rewrite TPlength_Fc_eq. intro H.
 rewrite TPithdel_Fc_eq; trivial. simpl.
 apply -> le_Sn. apply IHt; trivial.
 rewrite TPlength_Fc_diff in H; trivial.
 apply False_ind. apply H; trivial. 
 apply False_ind. apply H; trivial.
Defined.


Lemma term_size_TPithdel_le : forall i t E n,
 term_size (TPithdel i t E n) <= term_size t.
Proof.
  intros. case (nat_eqdec (TPlength t E n) 1); intro H.
  rewrite TPithdel_TPlength_1; simpl; trivial.
  apply term_size_1_le.
  apply term_size_TPithdel with (i:=i) in H.
  unfold lt in H.
  apply le_trans' with (l:=S (term_size (TPithdel i t E n))); trivial.
  apply le_S. apply le_n.
Defined.  

Lemma term_size_TPith_TPithdel : forall i t E n,
 TPlength t E n <> 1 ->
 term_size (TPith i t E n) + term_size (TPithdel i t E n) < term_size t.
Proof.
  intros. unfold lt. generalize i. clear i.
  induction t; intro.
  simpl in H; apply False_ind. apply H; trivial.
  simpl in H; apply False_ind. apply H; trivial.
  simpl in H; apply False_ind. apply H; trivial. 
  clear H. 
  case (le_dec i (TPlength t1 E n)); intro H.
  rewrite TPith_Pr_le; trivial.
  case (nat_eqdec (TPlength t1 E n) 1); intro H0. 
  rewrite TPithdel_t1_Pr; trivial. simpl.
  apply -> le_Sn. apply le_plus'.
  apply term_size_TPith.
  rewrite TPithdel_Pr_le; trivial.
  simpl. apply -> le_Sn.
  replace (S (term_size (TPithdel i t1 E n) + term_size t2))
  with ((S (term_size (TPithdel i t1 E n)) + term_size t2)).          
  rewrite plus_assoc.
  replace (term_size (TPith i t1 E n) + S (term_size (TPithdel i t1 E n)))
    with (S (term_size (TPith i t1 E n) + term_size (TPithdel i t1 E n))).
  apply le_plus'. apply IHt1; trivial.
  rewrite plus_com with (n:=S (term_size (TPithdel i t1 E n))). simpl.
  rewrite plus_com with (n:=term_size (TPithdel i t1 E n)); trivial.
  simpl; trivial. 
  apply neg_le in H. rewrite TPith_Pr_gt; trivial.
  case (nat_eqdec (TPlength t2 E n) 1); intro H0.
  rewrite TPithdel_t2_Pr; trivial. simpl.
  apply -> le_Sn. rewrite plus_com with (m:=term_size t1).
  apply le_plus'. apply term_size_TPith.
  rewrite TPithdel_Pr_gt; trivial. simpl.
  apply -> le_Sn. 
  replace (S (term_size t1 +
              term_size (TPithdel (i - TPlength t1 E n) t2 E n)))
    with (term_size t1 +
          S (term_size (TPithdel (i - TPlength t1 E n) t2 E n))).
  rewrite 2 plus_com with (m:=term_size t1).   
  rewrite plus_assoc.
  replace (term_size (TPith (i - TPlength t1 E n) t2 E n) +
           S (term_size (TPithdel (i - TPlength t1 E n) t2 E n)))
    with (S (term_size (TPith (i - TPlength t1 E n) t2 E n) +
             term_size (TPithdel (i - TPlength t1 E n) t2 E n))) .     
  apply le_plus'. apply IHt2; trivial.
  rewrite plus_com with
      (n:= S (term_size (TPithdel (i - TPlength t1 E n) t2 E n))).
  simpl.
  rewrite plus_com with
      (m:=term_size (TPithdel (i - TPlength t1 E n) t2 E n)); trivial.
  rewrite plus_com with
      (n:=S (term_size (TPithdel (i - TPlength t1 E n) t2 E n))).
  simpl.
  rewrite plus_com with
      (m:=term_size (TPithdel (i - TPlength t1 E n) t2 E n)); trivial.  
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H0.
  generalize H; clear H.  inversion H0.
  rewrite TPlength_Fc_eq. intro H.
  rewrite TPith_Fc_eq; trivial.
  rewrite TPithdel_Fc_eq; trivial. simpl.
  apply -> le_Sn. rewrite plus_com. simpl. rewrite plus_com.
  apply IHt; trivial.
  rewrite TPlength_Fc_diff in H; trivial.
  apply False_ind. apply H; trivial. 
  apply False_ind. apply H; trivial.  
Defined.


Lemma TPlength_leq_term_size : forall t E n,
      TPlength t E n <= term_size t.
Proof.
  intros. induction t.
  simpl; trivial. simpl; trivial.
  simpl; trivial. apply le_S. apply term_size_1_le.
  simpl. apply le_S.
  apply le_trans' with (l:=term_size t1 + TPlength t2 E n).
  apply le_plus'; trivial. rewrite plus_com.
  rewrite plus_com with (m:=term_size t1).
  apply le_plus'; trivial.
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H0.
  inverts H0. rewrite TPlength_Fc_eq. simpl.
  apply le_S; trivial. rewrite TPlength_Fc_diff; trivial.
  simpl. apply le_S. apply term_size_1_le.
  simpl. trivial.
Defined.

Hint Resolve TPlength_leq_term_size.


Require Import Omega.

Lemma TPlength_TPithdel : forall i t E n,
      (TPlength t E n) <> 1 ->
       TPlength (TPithdel i t E n) E n = (TPlength t E n) - 1.
Proof.
  intros. gen i. induction t; intros.
  simpl in H. false. simpl in H; trivial. false.
  simpl in H. false. clear H.
  case (le_dec i (TPlength t1 E n)); intro H0.
  case (nat_eqdec (TPlength t1 E n) 1); intro H1.
  rewrite TPithdel_t1_Pr; trivial.
  simpl. rewrite H1. simpl. omega.
  rewrite TPithdel_Pr_le; trivial.
  simpl. rewrite IHt1; trivial.
  assert (Q:TPlength t1 E n >= 1). auto. omega.
  case (nat_eqdec (TPlength t2 E n) 1); intro H1.
  rewrite TPithdel_t2_Pr; try omega.
  simpl. rewrite H1. omega.
  rewrite TPithdel_Pr_gt; try omega.
  simpl. rewrite IHt2; trivial. 
  assert (Q:TPlength t1 E n >= 1). auto. 
  assert (Q': TPlength t2 E n >= 1). auto. omega.
  case (nat_pair_eqdec (E, n) (n0, n1)); intro H0.
  inverts H0. rewrite TPlength_Fc_eq in *|-*.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite TPlength_Fc_eq. apply IHt; trivial.
  rewrite TPlength_Fc_diff in H; trivial. false.
  intro H1. apply H0. inverts H1. trivial.
  simpl in H. false.
Qed.

Hint Resolve TPlength_TPithdel.

Lemma TPith_overflow: forall i t E n, i >= TPlength t E n ->
      TPith i t E n = TPith (TPlength t E n) t E n.
Proof.
  intros. generalize i H. clear i H.
  induction t; intros.
  simpl; trivial. simpl; trivial. simpl; trivial.  
  generalize H; clear H. simpl; intro H.
  assert (Q : 1 <= TPlength t2 E n). apply TPlength_1_le.  
  case (le_dec i (TPlength t1 E n)); intro H0.
  omega.
  case (le_dec (TPlength t1 E n + TPlength t2 E n) (TPlength t1 E n));
    intro H1.
  omega.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega.       
  apply IHt2; omega.
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H0.
  generalize H. clear H. inversion H0. rewrite TPlength_Fc_eq.
  intro H. rewrite 2 TPith_Fc_eq. apply IHt; trivial.
  rewrite TPlength_Fc_diff; trivial.
  rewrite 2 TPith_Fc_diff; trivial.
  simpl; trivial.
Qed.

Hint Resolve TPith_overflow.

Lemma TPithdel_overflow: forall i t E n, i >= TPlength t E n ->
      TPithdel i t E n = TPithdel (TPlength t E n) t E n.
Proof.
  intros. generalize i H. clear i H.
  induction t; intros.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl in H. simpl.
  assert (Q : 1 <= TPlength t2 E n). apply TPlength_1_le.
  case (le_dec i (TPlength t1 E n)); intro H0.
  omega.
  case (nat_eqdec (TPlength t2 E n) 1); intro H1.
  rewrite H1. simpl.
  case (le_dec (TPlength t1 E n + 1) (TPlength t1 E n)); intro H2.
  omega. trivial.
  apply eq_nat_diff in H1. rewrite H1.
  case (le_dec (TPlength t1 E n + TPlength t2 E n) (TPlength t1 E n));
    intro H2.
  omega.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n) with
      (TPlength t2 E n); try omega.
  f_equal. apply IHt2; omega.
  case (nat_eqdec (TPlength (Fc n0 n1 t) E n) 1); intro H0.
  rewrite 2 TPithdel_TPlength_1; trivial.  
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H1.
  generalize H H0; clear H H0.
  inversion H1. intros H3 H4.
  rewrite TPlength_Fc_eq in *|-*.
  rewrite 2 TPithdel_Fc_eq; trivial.
  f_equal; trivial. apply IHt; trivial.
  rewrite TPlength_Fc_diff in H0; trivial.
  apply False_ind. apply H0; trivial.
  simpl; trivial.
Qed.

Hint Resolve TPithdel_overflow.

Lemma TPith_TPithdel_leq_1 : forall t E n i j,
      i <= 1 -> j <= 1 -> TPlength t E n <> 1 ->
      TPith i (TPithdel j t E n) E n = TPith 2 t E n.
Proof.
  intros. induction t.
  simpl; trivial. simpl in H1. false.
  simpl in H1. false.
  case (nat_eqdec (TPlength t1 E n) 1); intro H2.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPith_Pr_gt; try omega.
  rewrite H2. simpl.
  case (nat_eqdec i 0); intro H3. rewrite H3. apply TPith_0.
  assert (Q : i = 1). omega. rewrite Q; trivial.
  assert (Q : TPlength t1 E n >= 1). auto.
  rewrite TPithdel_Pr_le; try omega.
  rewrite 2 TPith_Pr_le; try omega.
  apply IHt1; trivial. rewrite TPlength_TPithdel; omega.
  case (nat_pair_eqdec (E, n) (n0, n1)); intro H2.
  inverts H2. rewrite TPlength_Fc_eq in H1.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. apply IHt; trivial. 
  rewrite TPlength_Fc_diff in H1. false.
  intro H3. inverts H3. false.
  simpl in H1. false.
Qed.

Hint Resolve TPith_TPithdel_leq_1.


Lemma TPith_TPithdel_geq_TPlength :
      forall t E n i j,
      TPlength t E n <> 1 ->  
      i >= TPlength t E n - 1 -> j >= TPlength t E n  ->
      TPith i (TPithdel j t E n) E n = TPith (TPlength t E n - 1) t E n.
Proof.
  intros. gen i j H0 H1. induction t; intros. 
  simpl in H. false. simpl in H. false.
  simpl in H. false. clear H. simpl in H0. simpl in H1.
  assert (Q : TPlength t1 E n >= 1). auto.
  assert (Q' : TPlength t2 E n >= 1). auto.
  case (nat_eqdec (TPlength t2 E n) 1); intro H2. 
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPith_Pr_le; try omega.
  simpl. replace (TPlength t1 E n + TPlength t2 E n - 1) with
          (TPlength t1 E n); try omega.
  rewrite TPith_overflow; try omega; trivial.
  simpl. omega. rewrite TPithdel_Pr_gt; try omega.
  simpl TPlength.
  rewrite 2 TPith_Pr_gt; try omega.
  rewrite IHt2; try omega.
  replace (TPlength t1 E n + TPlength t2 E n - 1 - TPlength t1 E n)
   with (TPlength t2 E n - 1); try omega. trivial.
  case (nat_pair_eqdec (E, n) (n0, n1)); intro H2. inverts H2.
  rewrite TPlength_Fc_eq in *|-*.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; trivial.
  rewrite TPlength_Fc_diff in H. false.
  intro H3. apply H2. symmetry. trivial.
  simpl in H. false.
Qed.


Lemma TPith_TPithdel_geq_TPlength' : forall t E n i j,
      TPlength t E n <> 1 ->  
      i >= TPlength t E n - 1 -> j < TPlength t E n  ->
      TPith i (TPithdel j t E n) E n = TPith (TPlength t E n) t E n.
Proof.
  intros. gen i j H0 H1. induction t; intros.
  simpl in H. false. simpl in H. false.
  simpl in H. false. clear H.
  simpl in H0. simpl in H1.
  assert (Q : TPlength t1 E n >= 1). auto.
  assert (Q' : TPlength t2 E n >= 1). auto.
  case (le_dec j (TPlength t1 E n)); intro H2. 
  case (nat_eqdec (TPlength t1 E n) 1); intro H3.
  rewrite TPithdel_t1_Pr; trivial.
  rewrite TPith_Pr_gt; simpl TPlength; try omega.
  rewrite 1 TPith_overflow; try omega. 
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega; trivial.
  rewrite TPithdel_Pr_le; trivial.
  rewrite 2 TPith_Pr_gt; simpl TPlength; try omega.
  rewrite TPlength_TPithdel; trivial.
  rewrite TPith_overflow; try omega. 
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega; trivial.  
  rewrite TPlength_TPithdel; try omega.
  case (nat_eqdec (TPlength t2 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite 2 TPith_Pr_gt; simpl TPlength; try omega.
  rewrite IHt2; try omega.
  replace (TPlength t1 E n + TPlength t2 E n - TPlength t1 E n)
    with (TPlength t2 E n); try omega; trivial.
  case (nat_pair_eqdec (E, n) (n0, n1)); intro H2.
  inverts H2.
  rewrite TPlength_Fc_eq in *|-*.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; try omega; trivial.
  rewrite TPlength_Fc_diff in H. false.
  intro H3. apply H2. symmetry. trivial.
  simpl in H. false.
Qed.


Lemma TPith_TPithdel_lt : forall t E n i j,
      i > 0 -> i < j -> i < TPlength t E n ->  
      TPith i (TPithdel j t E n) E n = TPith i t E n.
Proof.
  intros t E n. 
  induction t; intros.
  simpl in H1. omega. simpl in H1. omega.
  simpl in H1. omega. simpl in H1.
  case (le_dec j (TPlength t1 E n)); intro H2.
  rewrite TPith_Pr_le; try omega.
  case (nat_eqdec (TPlength t1 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPith_Pr_le; try omega.
  rewrite IHt1; try omega; trivial.
  rewrite TPlength_TPithdel; try omega; trivial.
  case (nat_eqdec (TPlength t2 E n) 1); intro H3.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  rewrite TPith_Pr_le; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega.
  case (le_dec i (TPlength t1 E n)); intro H4. 
  rewrite 2 TPith_Pr_le; try omega; trivial.
  rewrite 2 TPith_Pr_gt; try omega; trivial.
  rewrite IHt2; try omega; trivial.
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H2.
  inverts H2. rewrite TPlength_Fc_eq in H1.
  rewrite TPith_Fc_eq.
  case (nat_eqdec (TPlength t E n) 1); intro H2. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite TPith_Fc_eq. rewrite IHt; trivial.
  rewrite TPlength_Fc_diff in H1; trivial. omega.
  simpl in H1. omega.
Qed.

Hint Resolve TPith_TPithdel_lt.

  
Lemma TPith_TPithdel_geq : forall t E n i j,
      i > 0 -> i >= j -> i < TPlength t E n ->
      TPith i (TPithdel j t E n) E n = TPith (i + 1) t E n.
Proof.
  intros t E n. induction t; intros.
  simpl in H1. omega. simpl in H1. omega.
  simpl in H1. omega. simpl in H1.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (nat_eqdec (TPlength t1 E n) 1); intro H3.
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
  case (nat_eqdec (TPlength t2 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite 2 TPith_Pr_gt; try omega.
  gen_eq ii : (i - TPlength t1 E n); intro Hii.
  replace (i + 1 - TPlength t1 E n) with (ii + 1); try omega.
  rewrite IHt2; try omega; trivial.
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H2.
  inverts H2. rewrite TPlength_Fc_eq in H1.
  case (nat_eqdec (TPlength t E n) 1); intro H2. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite 2 TPith_Fc_eq. rewrite IHt; trivial.
  rewrite TPlength_Fc_diff in H1; trivial. omega.
  simpl in H1. omega.
Qed.

Hint Resolve TPith_TPithdel_geq.

Lemma TPith_TPithdel_exists : forall i j t E n,
      TPlength t E n <> 1 ->
      exists k, TPith i (TPithdel j t E n) E n = TPith k t E n .
Proof.
  intros. case (le_dec j i); intro H0.
  case (nat_eqdec i 0); intro H1.
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
  case (nat_eqdec i 0); intro H1. rewrite H1.
  rewrite TPith_0. case (nat_eqdec j 1); intro H2.
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

Lemma TPithdel_lt_comm : forall t E n i j,
      i > 0 -> i < j -> j <= TPlength t E n ->
      TPithdel i (TPithdel j t E n) E n =
      TPithdel (j - 1) (TPithdel i t E n) E n.
Proof.
  intros t E n.
  induction t; intros. simpl in H1. omega.
  simpl in H1. omega. simpl in H1. omega.
  simpl in H1.
  case (le_dec j (TPlength t1 E n)); intro H2.
  case (nat_eqdec (TPlength t1 E n) 1); intro H3; try omega.
  rewrite TPithdel_Pr_le with (i:=j); try omega.
  rewrite TPithdel_Pr_le with (t1:=t1); try omega.
  case (nat_eqdec (TPlength t1 E n) 2); intro H4.
  rewrite 2 TPithdel_t1_Pr;
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite 2 TPithdel_Pr_le;
  try rewrite TPlength_TPithdel; try omega; trivial. fequals. 
  rewrite IHt1; try omega; trivial.
  case (nat_eqdec (TPlength t2 E n) 1); intro H3.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  case (le_dec i (TPlength t1 E n)); intro H4.
  case (nat_eqdec (TPlength t1 E n) 1); intro H5.
  rewrite TPithdel_t1_Pr with (t1 := t1); try omega.
  rewrite 2 TPithdel_TPlength_1; try omega; trivial.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPithdel_t2_Pr; try omega; trivial.
  rewrite TPlength_TPithdel; try omega. omega.  
  rewrite TPithdel_Pr_gt; try omega.
  case (le_dec i (TPlength t1 E n)); intro H4.
  case (nat_eqdec (TPlength t1 E n) 1); intro H5.
  rewrite 2 TPithdel_t1_Pr with (i:=i); trivial.
  rewrite H5. trivial.
  rewrite 2 TPithdel_Pr_le with (i:=i); trivial.  
  rewrite TPithdel_Pr_gt;
  try rewrite TPlength_TPithdel; try omega. fequals.
  replace (j - 1 - (TPlength t1 E n - 1)) with
  (j - TPlength t1 E n); try omega; trivial.
  case (nat_eqdec (TPlength t2 E n) 2); intro H5. 
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
  case (nat_pair_eqdec (n0, n1) (E, n)); intro H2.
  inverts H2. rewrite TPlength_Fc_eq in H1.
  case (nat_eqdec (TPlength t E n) 1); intro H2. omega.
  rewrite TPithdel_Fc_eq; trivial.
  rewrite TPithdel_Fc_eq with (t:=t); trivial.
  case (nat_eqdec (TPlength t E n) 2); intro H3.
  rewrite TPithdel_TPlength_1 with (i:=i);
  autorewrite with tuples;
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite TPithdel_TPlength_1 with (i:=j-1);
    autorewrite with tuples; try rewrite TPlength_TPithdel;
  try omega; trivial.  
  rewrite 2 TPithdel_Fc_eq;
  try rewrite TPlength_TPithdel; try omega; trivial.
  rewrite IHt; trivial.
  rewrite TPlength_Fc_diff in H1; trivial. omega.  
  simpl in H1. omega.
Qed.

Lemma TPithdel_geq_comm : forall t E n i j,
      i > 0 -> j <= i -> i < TPlength t E n ->
      TPithdel i (TPithdel j t E n) E n =
      TPithdel j (TPithdel (i + 1) t E n) E n.
Proof.
  intros. gen_eq ii : (i + 1); intro H2.
  replace i with (ii - 1); try omega.
  case (nat_eqdec j 0); intro H3;
    try rewrite H3; repeat rewrite TPithdel_0.  
  rewrite <- TPithdel_lt_comm; try omega; trivial.
  rewrite <- TPithdel_lt_comm; try omega; trivial.
Qed.  
   


(** About rpl_super, set_super, is_Pr, TPlength, TPith and TPithdel *)

Lemma rpl_super_is_Pr : forall s S E, is_Pr s <-> is_Pr (rpl_super S E s). 
Proof.
  destruct s; split~; intros;
  simpl in *|-*; try contradiction.
  gen H. case (set_In_dec nat_eqdec n S); intros H0 H; simpl in H; trivial.
Qed.
  
Lemma rpl_super_perm : forall S0 m pi t,
                      rpl_super S0 m (pi @ t) = pi @ (rpl_super S0 m t).
Proof.
  intros.
  induction t; intros; simpl;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; trivial.
  case (set_In_dec nat_eqdec n S0); intro H; simpl; trivial.
Qed.

Lemma TPlength_rpl_super : forall S0 E0 E n t,
      ~ set_In E S0 -> E0 >= E ->
      TPlength (rpl_super S0 E0 t) E n  = TPlength t E n.
Proof.
  intros. induction t.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl. rewrite IHt1. rewrite IHt2; trivial.
  case (nat_pair_eqdec (n0,n1) (E,n)); intro H1. inverts H1.
  autorewrite with tuples. simpl.
  case (set_In_dec nat_eqdec E S0);
  intro H1; try contradiction.
  autorewrite with tuples; trivial.
  rewrite TPlength_Fc_diff; trivial.
  simpl. case (set_In_dec nat_eqdec n0 S0); intro H2.
  case (nat_pair_eqdec (n0 + E0 + 1, n1) (E, n)); intro H3; try omega.
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
  case (nat_pair_eqdec (n0,n1) (E,n)); intro H1.
  inverts H1. autorewrite with tuples.
  simpl. case (set_In_dec nat_eqdec E S0); intro H1; try contradiction.
  autorewrite with tuples. rewrite IHt; trivial.
  rewrite TPith_Fc_diff; trivial. simpl.
  case (set_In_dec nat_eqdec n0 S0); intro H2.
  case (nat_pair_eqdec (n0 + E0 + 1, n1) (E,n));
    intro H3. inverts H3; try omega.
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
  case (nat_eqdec (TPlength t1 E n) 1); intro H2.
  rewrite TPithdel_t1_Pr; trivial. simpl rpl_super.
  rewrite TPithdel_t1_Pr; try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Pr_le; trivial. simpl rpl_super.
  rewrite TPithdel_Pr_le; try rewrite TPlength_rpl_super; trivial.
  rewrite IHt1; trivial.
  case (nat_eqdec (TPlength t2 E n) 1); intro H2.
  rewrite TPithdel_t2_Pr; try omega. simpl rpl_super.
  rewrite TPithdel_t2_Pr;
    try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite TPithdel_Pr_gt; try omega. simpl rpl_super.
  rewrite TPithdel_Pr_gt;
    try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite IHt2; trivial.
  case (nat_pair_eqdec (n0,n1) (E,n)); intro H1.
  inverts H1. case (nat_eqdec (TPlength t E n) 1); intro H1.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; trivial.
  rewrite TPlength_rpl_super; autorewrite with tuples; trivial.
  rewrite TPithdel_Fc_eq; trivial. simpl rpl_super.
  case (set_In_dec nat_eqdec E S0); intro H2; try contradiction.
  rewrite TPithdel_Fc_eq. f_equal; trivial.
  rewrite TPlength_rpl_super; autorewrite with tuples; trivial.  
  rewrite TPithdel_Fc_diff; trivial.
  simpl. case (set_In_dec nat_eqdec n0 S0); intro H2; try contradiction.
  case (nat_pair_eqdec (n0 + E0 + 1, n1) (E,n)); intro H3.
  inverts H3; try omega.
  rewrite TPithdel_Fc_diff; trivial.
  rewrite TPithdel_Fc_diff; trivial. 
  simpl; trivial.
Qed.


(** The following are results about the manipulation of 
    superscripts of function symbols *) 

Lemma set_super_TPith : forall i E0 E n t,
      set_In E0 (set_super (TPith i t E n)) ->
      set_In E0 (set_super t).
Proof.
  intros. gen i. induction t; intros.
  simpl; trivial. simpl; trivial. simpl; trivial.
  simpl. case (le_dec i (TPlength t1 E n)); intro H0.
  rewrite TPith_Pr_le in H; trivial.
  apply set_union_intro1. apply (IHt1 i); trivial.
  rewrite TPith_Pr_gt in H; try omega.
  apply set_union_intro2. apply (IHt2 (i - TPlength t1 E n)); trivial.
  case (nat_pair_eqdec (n0,n1) (E,n)); intro H1. inverts H1.
  autorewrite with tuples in H. simpl. apply set_add_intro1.
  apply (IHt i); trivial.
  rewrite TPith_Fc_diff in H; trivial.
  simpl; trivial.
Qed.

Lemma set_super_TPithdel : forall i E0 E n t,
      set_In E0 (set_super (TPithdel i t E n)) ->
      set_In E0 (set_super t).
Proof.
  intros. gen i. induction t; intros.
  simpl; trivial. simpl; trivial. simpl in H. contradiction.
  simpl. case (le_dec i (TPlength t1 E n)); intro H0.
  case (nat_eqdec (TPlength t1 E n) 1); intro H1.
  rewrite TPithdel_t1_Pr in H; trivial.
  apply set_union_intro2; trivial.
  rewrite TPithdel_Pr_le in H; trivial. simpl in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply (IHt1 i); trivial.
  apply set_union_intro2; trivial.
  case (nat_eqdec (TPlength t2 E n) 1); intro H1.
  rewrite TPithdel_t2_Pr in H; try omega.
  apply set_union_intro1; trivial.
  rewrite TPithdel_Pr_gt in H; try omega. simpl in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  apply (IHt2 (i - TPlength t1 E n)); trivial.
  case (nat_pair_eqdec (n0,n1) (E,n)); intro H1. inverts H1.
  case (nat_eqdec (TPlength t E n) 1); intro H1.
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
  case (set_In_dec nat_eqdec n0 S0); intro H1; simpl.
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


Notation "S1 |U S2" := (set_union nat_eqdec S1 S2) (at level 67).
Notation "S1 |I S2" := (set_inter nat_eqdec S1 S2) (at level 67).

Definition subset (A : Set) (S1 S2 : set A) :=
  forall m, set_In m S1 -> set_In m S2.

Lemma nil_empty_set : forall (A: Set) (S: set A),
      S = [] <-> (forall k, ~ set_In k S).
Proof.
  intros. split~; intros. rewrite H.
  intro H'. simpl in H'. trivial.
  destruct S; trivial.
  assert (Q:~set_In a (a :: S)). apply H.
  false. apply Q. simpl. left~.
Qed.


(** The following are results about valid collection and valid 
    associativity *)

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
  
Lemma valid_col_seq : forall L t E n,
      valid_col L t E n <->
      (NoDup L /\ (forall a, In a L -> In a (seq 1 (TPlength t E n)))).
Proof.
  intros. unfold valid_col.
  split~; intros. destruct H.
  split~; intros. apply in_seq. 
  apply H0 in H1. destruct H1. omega.
  destruct H. split~; intros.
  apply H0 in H1. apply in_seq in H1.
  destruct H1. split~; omega.
Qed.


Lemma valid_col_length_limit : forall t E n L,
      valid_col L t E n ->
      length L <= TPlength t E n  .
Proof.
  intros. replace (TPlength t E n) with (length (seq 1 (TPlength t E n))).
  apply subset_list.
  apply nat_eqdec. apply H.
  intros. apply valid_col_seq in H.  
  destruct H. apply H1 in H0; trivial.
  apply seq_length.
Qed.  

Lemma valid_col_In_nat_seq : forall t E n L,
      valid_col L t E n ->
      length L = TPlength t E n ->
      forall a, In a (seq 1 (TPlength t E n)) -> In a L .
Proof.
  intros t E n L H H0.
  unfold valid_col in H.
  destruct H.  
  apply subset_list_eq'; trivial.
  apply nat_eqdec.
  apply seq_NoDup.
  rewrite <- H0.
  rewrite seq_length; trivial.
  intros. apply H1 in H2.
  destruct H2.
  apply in_seq.
  split~. omega.
Qed.  


Lemma Args_col_list_length : forall L t E n,
      length (Args_col_list L t E n) = length L .
Proof.
  intros. induction L; simpl; omega.
Qed.


Lemma Args_assoc_nil : forall L i,
      Args_assoc i ([]) L = Args_right_assoc L.
Proof.
  intros. simpl. trivial.
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
  case (nil_eqdec _ nat_eqdec L); intro H2.
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
  case (nil_eqdec _ term_eqdec L0); intro H3.
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


Lemma sorted_nat_list_cons : forall a L,
      sorted_nat_list (a :: L) ->
      forall b,  In b L -> a <= b.
Proof.
  intros. simpl in H.
  gen H. case (le_dec a (hd 0 L)); intros H1 H2; try contradiction.
  gen a b. induction L; intros; simpl in *|-; try contradiction.
  destruct H0. rewrite <- H. trivial.
  gen H2. case (le_dec a (hd 0 L)); intros H2 H3; try contradiction.
  apply IHL; try omega; trivial.
Qed.

Lemma sorted_nat_list_cons' : forall a L,
      ~ In a L ->
      sorted_nat_list (a :: L) ->
      forall b,  In b L -> a < b.
Proof.
  intros. apply sorted_nat_list_cons with (b:=b) in H0; trivial.
  assert (Q : a <> b).
   intro H2. rewrite H2 in H. contradiction.
  omega.
Qed.

Lemma assoc_TPlength : forall L L' E i n,

      NoDup L' ->    

      sorted_nat_list L' ->

      (forall j, In j L' -> (j - i >= 1 /\ j - i < length L)) ->
    
      TPlength (Args_assoc i L' L) E n = TPlength (Args_right_assoc L) E n.

Proof.
  intros. gen_eq l : (length L').
  intro H2. gen H2 H H0 H1. gen i L L'.
  induction l using peano_induction; intros.
  destruct L'. simpl in *|-*; trivial.
  inverts H0.
  assert (Q0 : forall b, In b L' -> n0 < b).
   intros. apply sorted_nat_list_cons' with (L:=L'); trivial. 
  assert (Q1 : n0 - i >= 1 /\ n0 - i < length L).
   apply H3. left~.
  destruct Q1.
  simpl in *|-*.
  gen H1. case (le_dec n0 (hd 0 L')); intros H8 H9; try contradiction.
  assert (Q1 : length (head_list term (n0 - i) L) <> 0).
   rewrite head_list_length; simpl; try omega.
  assert (Q2 : length (tail_list term (n0 - i) L) <> 0).
   rewrite tail_list_length; simpl length; try omega. 
  rewrite H with (m:= length L'); simpl; try omega; trivial.
  rewrite Agrs_right_assoc_TPlength_append; trivial.
  rewrite <- head_tail_append with (L:=L) (n:=n0-i); trivial.
  intros.
  assert (Q3 : j - i >= 1 /\ j - i < length L).
   apply H3. right~.
  destruct Q3. split~; try omega.
  apply Q0 in H1. omega.
  rewrite tail_list_length; simpl length; omega.
Qed.
  
  
Lemma Args_col_TPlength : forall L L' t E n,
    
      length L <> 0 ->

      NoDup L' ->    

      sorted_nat_list L' ->
      
      (forall j, In j L' -> j >= 1 /\ j < length L) ->
      
      TPlength (Args_col L L' t E n) E n = length L.

Proof.
  intros. unfold Args_col.
  rewrite assoc_TPlength; trivial.
  rewrite Args_right_assoc_TPlength; trivial.
  rewrite Args_col_list_length; trivial.
  intros. apply H2 in H3.
  destruct H3. split~; omega. 
Qed.


Lemma Args_col_TPith_TPithdel  : forall L s E n,

      valid_col L s E n ->

      length L <> 0 ->
      
      exists i,

        TPith 1 (Args_col L ([]) s E n) E n = TPith i s E n /\

        exists L',

          TPithdel 1 (Args_col L ([]) s E n) E n =
                   
                      Args_col L' ([]) (TPithdel i s E n) E n /\

                      length L' = length L - 1 /\

                      (forall k, In k L' ->
                        ((k < i /\ In k L) \/ (k >= i /\ In (k + 1) L))) /\
                   
                      valid_col L' (TPithdel i s E n) E n .
                  
Proof.
  intros. destruct L; simpl in H0. false.
  unfold Args_col. simpl Args_col_list.
  exists n0. rewrite Args_assoc_nil.
  
  case (nil_eqdec _ nat_eqdec L); intro H1.
  rewrite H1. simpl. rewrite TPith_TPith. split~.
  exists (nil (A:=nat)). simpl.
  rewrite TPithdel_TPlength_1.
  split~. split~. split~; intros. contradiction.
  apply valid_col_nil.
  rewrite TPlength_TPith. trivial.

  rewrite Args_right_assoc_cons.
  rewrite TPith_Pr_le. rewrite TPith_TPith. split~.
  rewrite TPithdel_t1_Pr. simpl.
  
  gen_eq l : (length L). clear H0.
  intro H2. gen H2 H1 H. gen L.
  induction l using peano_induction; intros.

  destruct L; simpl in *|-. contradiction.

  simpl Args_col_list. clear H1.
  unfold valid_col in H0.
  destruct H0. inverts H0. inverts H6.
  
  assert (Q0 : n1 <> n0).
   intro H8. apply H5. left~. 
  assert (Q1 : n0 >= 1 /\ n0 <= TPlength s E n).
   apply H1. left~.
  assert (Q2 : n1 >= 1 /\ n1 <= TPlength s E n).
   apply H1. right~. left~.
  destruct Q1. destruct Q2.  

  assert (Q : exists k, ((n1 < n0 /\ k = n1) \/ (n1 > n0 /\ k = n1 - 1)) /\ 
              TPith k (TPithdel n0 s E n) E n = TPith n1 s E n).
   case (le_dec n1 n0); intro H9. 
   exists n1. split~. left~. split~. omega.
   rewrite TPith_TPithdel_lt; try omega. trivial.
   exists (n1-1). split~. right~. split~. omega.
   rewrite TPith_TPithdel_geq; try omega.
   replace (n1 - 1 + 1) with n1; try omega. trivial.

  case Q; clear Q; intros k Q. destruct Q. 

  case (nil_eqdec _ nat_eqdec L); intro H11.
  rewrite H11. exists (|[k]|).
  split~. split~.
  rewrite H2. rewrite H11. simpl. trivial.

  split~; intros. simpl in H12.
  destruct H12; try contradiction.
  rewrite <- H12.
  destruct H9; destruct H9; [left~ | right~]; rewrite H13.
  split~. right~. left~.
  split~. omega. right~. left~. omega.    
  
  unfold valid_col. split~; intros.
  apply NoDup_cons. simpl. intro; trivial.
  apply NoDup_nil. simpl in H12.
  destruct H12; try contradiction.
  rewrite <- H12. rewrite TPlength_TPithdel; try omega.

  case H with (m:=length L) (L:=L);
    try omega; trivial.
  unfold valid_col. split~.
  apply NoDup_cons; trivial.
  intro H12. apply H5. right~.
  intros. apply H1.
  simpl in *|-*. destruct H12.
  left~. right~.
  intros L0 H13.
  destruct H13. destruct H13. destruct H14.

  exists (k::L0). simpl Args_col_list.
  rewrite 2 Args_right_assoc_cons. 
  rewrite H10. split~.
  fequals. 

  split~. simpl. omega.

  split~; intros.
  simpl in H16. destruct H16.
  rewrite <- H16.
  destruct H9; destruct H9; simpl; [left~ | right~]; rewrite H17.
  split~. split~. omega. right~. left~. omega.
  apply H14 in H16.
  destruct H16; [left~ | right~].
  destruct H16. split~. destruct H17; [left~ | right~]. right~.
  destruct H16. split~. destruct H17; [left~ | right~]. right~.
     
  unfold valid_col. split~.
  2: { intros. simpl in H16.
  destruct H16. rewrite <- H16.
  rewrite TPlength_TPithdel; try omega.
  apply H15. trivial. }
  apply NoDup_cons.
  2: { apply H15. }

  intro H16. apply H14 in H16.
  destruct H16; destruct H16.
  destruct H17. omega.
  destruct H9; destruct H9; try omega.
  rewrite H18 in H17. contradiction.
  destruct H17; try omega.
  destruct H9; destruct H9; try omega.
  rewrite H18 in H17.
  replace (n1 - 1 + 1) with n1 in H17; try omega.
  contradiction.
  
  intro H16.
  rewrite Args_col_list_length in H16.
  rewrite H16 in H13.
  symmetry in H13.
  replace (length L - 0) with (length L) in H13; try omega.
  apply length_zero_iff_nil in H13. contradiction.
  intro H16. rewrite Args_col_list_length in H16.
  apply length_zero_iff_nil in H16. contradiction.
  rewrite TPlength_TPith. omega.
  rewrite TPlength_TPith. trivial.
  rewrite TPlength_TPith. omega.
  intro H2. rewrite Args_col_list_length in H2.
  apply length_zero_iff_nil in H2. contradiction.
  
Qed.