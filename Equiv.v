(***************************************************************************
 * Equiv.v                						   *		
***************************************************************************)

Require Export Tuples Alpha_Equiv.

Inductive equiv (S : set nat): Context -> term -> term -> Prop :=

 | equiv_Ut   : forall C, equiv S C (<<>>) (<<>>) 

 | equiv_At   : forall C a, equiv S C (%a) (%a)

 | equiv_Pr   : forall C t1 t2 t1' t2', (equiv S C t1 t1') -> (equiv S C t2 t2') -> 
                                          equiv S C (<|t1,t2|>) (<|t1',t2'|>)  

 | equiv_Fc   :  forall m n t t' C,  ~ set_In m S -> 
                                    (equiv S C t t') -> 
                              equiv S C (Fc m n t) (Fc m n t')

 | equiv_Ab_1 : forall C a t t', (equiv S C t t') -> 
                               equiv S C ([a]^t) ([a]^t')

 | equiv_Ab_2 : forall C a a' t t', 
                a <> a' -> (equiv S C t (|[(a,a')] @ t')) -> C |- a # t' -> 
                                    equiv S C ([a]^t) ([a']^t')

 | equiv_Su   : forall (C: Context) p p' (X: Var), 
               (forall a, (In_ds p p' a) -> set_In ((a,X)) C) ->
               equiv S C (p\X) (p'\X)

(** The stop point of the following rules, 
    when the TPlength of the both sides is equal to 1  *)
                     
 | equiv_Fc_TPlength_1 : forall m, set_In m S ->
                         forall n t t' C,
                           TPlength t m n = 1 ->
                           TPlength t' m n = 1 ->
                           equiv S C (TPith 1 t m n) (TPith 1 t' m n) ->
                           equiv S C (Fc m n t) (Fc m n t')

(** Checks only for Associative-alpha equivalence *)  

 | equiv_A    : forall m, 
         (m = 0) ->
         set_In m S -> 
         forall n t t' C, 
         (let l := TPlength t m n in 
          let l' := TPlength t' m n in (l <> 1 /\ l' <> 1)) ->
         (equiv S C (TPith 1 t m n) (TPith 1 t' m n))  ->
         (equiv S C (Fc m n (TPithdel 1 t m n)) (Fc m n (TPithdel 1 t' m n))) ->
             (equiv S C (Fc m n t) (Fc m n t'))

(** Checks for AC-alpha equivalence *)

 | equiv_AC   : forall m,
         set_In m S -> 
         (m = 1) ->
         forall n t t' i C,
         (let l := (TPlength t m n) in let l' := TPlength t' m n in 
         (l <> 1 /\ l' <> 1 /\ i > 0 /\ i <= l')) -> 
         (equiv S C (TPith 1 t m n) (TPith i t' m n))  ->
         (equiv S C (Fc m n (TPithdel 1 t m n)) (Fc m n (TPithdel i t' m n))) ->
             (equiv S C (Fc m n t) (Fc m n t'))  
.

Hint Constructors equiv.

Notation "C |- t ~e t'" := (equiv ([]) C t t') (at level 67).
Notation "C |- t ~a t'" := (equiv (|[0]) C t t') (at level 67). 
Notation "C |- t ~ac t'" := (equiv (|[1]) C t t') (at level 67). 


Lemma alpha_equiv_eq_equiv : forall C t t',
 C |- t ~alpha t' <-> C |- t ~e t'.
Proof.
 intros. split; intro H; induction H; auto;
 simpl in H; try contradiction.
Qed.

Hint Resolve alpha_equiv_eq_equiv.


Lemma alpha_equiv_TPlength : forall C t1 t2 m n, 
 C |- t1 ~alpha t2 -> TPlength t1 m n = TPlength t2 m n. 
Proof.
 intros. induction H; trivial. simpl; auto.
 case (m0 === m); case (n0 === n); intros H0 H1.
 rewrite H0. rewrite H1. autorewrite with tuples; trivial.
 rewrite 2 TPlength_Fc_diff_n; trivial. 
 rewrite 2 TPlength_Fc_diff_m; trivial.
 rewrite 2 TPlength_Fc_diff_n; trivial.
Qed.

Lemma alpha_equiv_TPith : forall C t t' i m n, 
  C |- t ~alpha t' -> C |- TPith i t m n ~alpha TPith i t' m n.
Proof. 
 intros. gen i. induction H; intro i.
 apply alpha_equiv_refl. apply alpha_equiv_refl.
 apply alpha_equiv_TPlength with (m:=m) (n:=n) in H.
 case (le_dec i (TPlength t1 m n)); intro H1. 
 rewrite 2 TPith_Pr_le; try omega; auto.
 rewrite 2 TPith_Pr_gt; try omega. rewrite H; auto.
 case (i === 0); intro H1. rewrite H1. rewrite 2 TPith_0. apply alpha_equiv_refl.
 generalize H; intro H'. apply alpha_equiv_TPlength with (m:=m) (n:=n) in H.
 case (le_dec i (TPlength (Fc m0 n0 t) m n)); intro H2.
 case (m0 === m); intro H3. case (n0 === n); intro H4.
 rewrite H3. rewrite H4. autorewrite with tuples; auto.
 rewrite TPlength_Fc_diff_n in H2; trivial.
 rewrite 2 TPith_Fc_diff_n; auto. 
 rewrite TPlength_Fc_diff_m in H2; trivial.
 rewrite 2 TPith_Fc_diff_m; auto. 
 rewrite 2 TPith_overflow; try omega. apply alpha_equiv_refl.
 simpl in *|-*; repeat case_nat; omega.
 simpl. case_nat; auto. simpl. case_nat; auto. simpl. case_nat; auto.
Qed. 

Lemma alpha_equiv_TPithdel : forall C t t' i m n, 
  C |- t ~alpha t' -> C |- TPithdel i t m n ~alpha TPithdel i t' m n.
Proof. 
 intros. gen i. induction H; intro i.
 apply alpha_equiv_refl. apply alpha_equiv_refl.
 generalize H H0. intros H' H'0.
 apply alpha_equiv_TPlength with (m:=m) (n:=n) in H.
 apply alpha_equiv_TPlength with (m:=m) (n:=n) in H0.
 case (le_dec i (TPlength t1 m n)); intro H1.
 case (i === 0); intro H2. rewrite H2. rewrite 2 TPithdel_0. auto.
 case (TPlength t1 m n === 1); intro H3. 
 assert (Q : i = 1). omega. rewrite Q.  
 rewrite 2 TPithdel_t1_Pr; try omega; trivial.
 rewrite 2 TPithdel_Pr_le; try omega; auto.
 case (le_dec i ((TPlength t1 m n) + (TPlength t2 m n))); intro H2.
 case (TPlength t2 m n === 1); intro H3.
 assert (Q : i = TPlength t1 m n + 1). omega. rewrite Q.  
 rewrite TPithdel_t2_Pr; try omega; trivial. rewrite H.
 rewrite TPithdel_t2_Pr; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try omega. rewrite H; auto.
 rewrite 2 TPithdel_overflow; simpl; try omega; auto.
 case (i === 0); intro H1. rewrite H1. rewrite 2 TPithdel_0; auto.
 generalize H; intro H'. apply alpha_equiv_TPlength with (m:=m) (n:=n) in H.
 case (le_dec i (TPlength (Fc m0 n0 t) m n)); intro H2.
 case (m0 === m); intro H3. case (n0 === n); intro H4.
 rewrite H3 in *|-*. rewrite H4 in *|-*. autorewrite with tuples in H2.
 case (TPlength t m n === 1); intro H5. assert (Q: i = 1). omega. rewrite Q.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq; try omega; auto.
 rewrite TPlength_Fc_diff_n in H2; trivial. assert (Q : i = 1). omega. rewrite Q. 
 rewrite 2 TPithdel_TPlength_1; auto. rewrite TPlength_Fc_diff_m in H2; trivial.
 assert (Q : i = 1). omega. rewrite Q. rewrite 2 TPithdel_TPlength_1; auto. 
 rewrite 2 TPithdel_overflow; try omega; auto. simpl in *|-*.
 repeat case_nat; omega. simpl; case_nat; auto. simpl; case_nat; auto.
 simpl; case_nat; auto.
Qed.

Lemma Fc_app_TPlength_1 : forall S C i j t t' m n,
                     set_In m S ->
                     i > 0 -> j > 0 -> 
                     TPlength t m n = 1 ->
                     TPlength t' m n = 1 ->
                     equiv S C (TPith 1 t m n) (TPith 1 t' m n) ->
                     equiv S C (Fc_app i m n t) (Fc_app j m n t').
Proof.
  intros. destruct i; destruct j; try omega.
  rewrite <- 2 Fc_app_Sn.
  apply equiv_Fc_TPlength_1 with (m := m) (n := n);
  autorewrite with tuples; trivial.
Qed.
