(***************************************************************************
 * Fresh.v                						   *		
***************************************************************************)

Require Import Tuples.
Require Export Disagr.

Definition Context := set (Atom * Var).

Inductive fresh : Context -> Atom -> term -> Prop :=

 | fresh_Ut   : forall C a, fresh C a Ut 

 | fresh_Pr   : forall C a t1 t2, (fresh C a t1) -> (fresh C a t2) -> 
                                  (fresh C a (<|t1,t2|>))  

 | fresh_Fc   : forall C a m n t, (fresh C a t) -> 
                               (fresh C a (Fc m n t))

 | fresh_Ab_1 : forall C a t, fresh C a (Ab a t)

 | fresh_Ab_2 : forall C a a' t, a <> a' -> (fresh C a t) -> 
                                 (fresh C a (Ab a' t))

 | fresh_At   : forall C a a', a <> a' -> 
                               (fresh C a (At a'))

 | fresh_Su   : forall C p a X, set_In (((!p $ a), X)) C -> 
                               fresh C a (Su p X)  
.

Hint Constructors fresh.

Notation "C |- a # t" := (fresh C a t) (at level 67).

(** Basic lemmas *)

Lemma fresh_At_elim : forall C a b, (C |- a # At b) -> a <> b.
Proof. intros. inversion H; trivial. Qed.

Hint Resolve fresh_At_elim.

Lemma fresh_Pr_elim : forall C a t u, 
(C |- a # <|t,u|>) -> ((C |- a # t) /\ (C |- a # u)).  
Proof. intros. inversion H; split; trivial. Qed.

Hint Resolve fresh_Pr_elim.

Lemma fresh_Fc_elim : forall C a m n t,
(C |- a # Fc m n t) -> C |- a # t.
Proof. intros. inversion H; trivial. Qed. 

Hint Resolve fresh_Fc_elim.

Lemma fresh_Ab_elim : forall C a b t, 
(C |- a # Ab b t) -> (a = b \/ ((a <> b) /\ (C |- a # t))).
Proof. 
 intros. inversion H. 
 left; trivial.
 right; split; trivial.
Qed.

Hint Resolve fresh_Ab_elim.

Lemma fresh_Su_elim : forall C p a X, 
(C |- a # Su p X) -> set_In (((!p $ a), X)) C.
Proof. intros. inversion H; trivial. Qed.

Hint Resolve fresh_Su_elim.


Lemma fresh_lemma_1 : forall C pi a t, 
(C |- a # (pi @ t)) -> (C |- ((!pi) $ a) # t).
Proof. 
 intros. induction t.
 apply fresh_Ut.
 apply fresh_At. rewrite perm_At in H. 
 inversion H. intro H'. apply H3.
 symmetry. apply perm_inv_side_atom.
 symmetry. trivial. case (((!pi) $ a) ==at a0). 
 intro H'. rewrite H'. apply fresh_Ab_1. 
 intro H'. apply fresh_Ab_2; trivial.
 apply IHt. rewrite perm_Ab in H.
 clear IHt. inversion H. symmetry in H3.
 apply perm_inv_side_atom in H3. symmetry in H3.
 contradiction. trivial.
 rewrite perm_Pr in H. inversion H. 
 apply fresh_Pr; [apply IHt1; trivial | apply IHt2; trivial].
 rewrite perm_Fc in H. inversion H.
 apply fresh_Fc. apply IHt; trivial.
 rewrite perm_Su in H. inversion H.
 apply fresh_Su. rewrite perm_comp_atom. 
 rewrite <- distr_rev. trivial.
Qed.

Hint Resolve fresh_lemma_1.

Lemma fresh_lemma_2 : forall C pi a t, 
(C |- (pi $ a) # t) -> (C |- a # (!pi @ t)).
Proof. 
 intros. induction t.
 rewrite perm_Ut. apply fresh_Ut.
 rewrite perm_At. apply fresh_At.
 inversion H. intro H'. apply H3.
 apply perm_inv_side_atom. trivial.
 rewrite perm_Ab. case (a ==at ((!pi) $ a0)). 
 intro H'. rewrite H'. apply fresh_Ab_1. 
 intro H'. apply fresh_Ab_2; trivial.
 apply IHt. clear IHt. inversion H. 
 apply perm_inv_side_atom in H3. 
 contradiction. trivial.
 rewrite perm_Pr. inversion H. 
 apply fresh_Pr; [apply IHt1; trivial | apply IHt2; trivial].
 rewrite perm_Fc. inversion H.
 apply fresh_Fc. apply IHt; trivial.
 rewrite perm_Su. inversion H.
 apply fresh_Su. rewrite perm_comp_atom in H3. 
 rewrite distr_rev. rewrite rev_involutive.
 trivial.
Qed.

Hint Resolve fresh_lemma_2.

Lemma fresh_lemma_3 : forall C pi a t, 
(C |- a # t) <-> (C |- (pi $ a) # (pi @ t)).  
Proof. 
 intros. split; intro.
 gen_eq g : (!pi). intro H'.
 assert (Q : pi = !g). rewrite H'. rewrite rev_involutive. trivial.
 rewrite Q. apply fresh_lemma_2. rewrite <- Q. rewrite H'.
 rewrite perm_inv_atom. 
 trivial.
 apply fresh_lemma_1 in H.
 rewrite perm_inv_atom in H.
 trivial.
Qed.

Hint Resolve fresh_lemma_3.

(** Freshness and tuples *)
 
Lemma fresh_TPith_TPithdel : forall i a C t m n, 
 C |- a # t <-> (C |- a # TPith i t m n /\ C |- a # TPithdel i t m n).  
Proof.
 intros. gen i. induction t; intro.
 simpl; repeat case_nat; repeat split; auto.
 simpl; repeat case_nat; repeat split; try intro H; destruct H; auto.
 simpl; repeat case_nat; repeat split; try intro H; destruct H; auto. Focus 3.
 simpl; repeat case_nat; repeat split; try intro H; destruct H; auto.
 
 case (i === 0); intro H1.
 rewrite H1. rewrite TPith_0. rewrite TPithdel_0.
 split; intro H. split; auto. destruct H; trivial.
 case (le_dec i (TPlength t1 m n)); intro H2. rewrite TPith_Pr_le; trivial.
 case (TPlength t1 m n === 1); intro H3. assert (Qi:i=1). omega. rewrite Qi.
 rewrite TPithdel_t1_Pr; trivial. split; intro. apply fresh_Pr_elim in H. destruct H.
 split; trivial. apply IHt1; trivial. destruct H.
 apply fresh_Pr; trivial. apply (IHt1 1); try split; trivial. 
 rewrite TPithdel_TPlength_1; auto.
 rewrite TPithdel_Pr_le; try omega. split; intro. 
 apply fresh_Pr_elim in H. destruct H.
 split. apply IHt1; trivial. apply fresh_Pr; trivial. apply IHt1; trivial.
 destruct H. apply fresh_Pr_elim in H0. destruct H0. apply fresh_Pr; trivial. 
 apply (IHt1 i); try split; trivial.
 case (le_dec i (TPlength t1 m n + TPlength t2 m n)); intro H3.
 rewrite TPith_Pr_gt; try omega. case (TPlength t2 m n === 1); intro H4.
 assert (Qi:i=TPlength t1 m n + 1). omega. rewrite Qi.
 rewrite TPithdel_t2_Pr; trivial. 
 replace (TPlength t1 m n + 1 - TPlength t1 m n) with 1; try omega.
 split; intro. apply fresh_Pr_elim in H. destruct H.
 split; trivial. apply IHt2; trivial.
 destruct H. apply fresh_Pr; trivial. apply (IHt2 1); split; trivial.
 rewrite TPithdel_TPlength_1; auto. rewrite TPithdel_Pr_gt; try omega. 
 split; intro. apply fresh_Pr_elim in H. destruct H.
 split. apply IHt2; trivial. apply fresh_Pr; trivial. apply IHt2; trivial.
 destruct H. apply fresh_Pr_elim in H0. destruct H0. apply fresh_Pr; trivial.
 apply (IHt2 (i - TPlength t1 m n)); split; trivial.
 rewrite TPith_overflow; simpl TPlength; try omega.
 rewrite TPithdel_overflow; simpl TPlength; try omega.
 split; intro H. split; auto. apply H.

 case (i === 0); intro H1. rewrite H1. 
 rewrite TPith_0. rewrite TPithdel_0. 
 split; intro. split; auto. apply H.
 case (le_dec i (TPlength (Fc n0 n1 t) m n)); intro H2.
 case (n0 === m); intro H3. case (n1 === n); intro H4.
 rewrite H3 in *|-*. rewrite H4 in *|-*.
 autorewrite with tuples in *|-*. case (TPlength t m n === 1); intro H5.
 assert (Qi:i=1). omega. rewrite Qi.
 rewrite TPithdel_TPlength_1; autorewrite with tuples; trivial.
 split; intro. apply fresh_Fc_elim in H. split; auto.
 apply IHt; trivial. destruct H. apply fresh_Fc. apply (IHt 1).
 split; trivial. rewrite TPithdel_TPlength_1; trivial.
 rewrite TPithdel_Fc_eq; try omega.
 split; intro. apply fresh_Fc_elim in H.
 split; try apply fresh_Fc; try apply IHt; trivial.
 apply fresh_Fc. destruct H. apply (IHt i); trivial.
 apply fresh_Fc_elim in H0. split; trivial.
 rewrite TPlength_Fc_diff_n in H2; trivial.
 rewrite TPith_Fc_diff_n; try omega. assert (Qi:i=1). omega. rewrite Qi.
 rewrite TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_n; try omega.
 split; intro. split; auto. apply H.
 rewrite TPlength_Fc_diff_m in H2; trivial.
 rewrite TPith_Fc_diff_m; try omega. assert (Qi:i=1). omega. rewrite Qi.
 rewrite TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; try omega.
 split; intro. split; auto. apply H.
 rewrite TPith_overflow; try omega.
 rewrite TPithdel_overflow; try omega.
 split; intro. split; auto. apply H.
Qed.

