(***************************************************************************
 *AC_Equiv.v   
 
 This is a guideline how to deal with AC equivalence
 starting from the notion of alpha-equivalence for purely non AC
 nominal terms.  The idea is we've defined jet a notion of alpha-
 equivalence for nominal terms without AC function symbols. Now,
 the signature is extended allowing other AC function symbols.  *		

***************************************************************************)

Require Export AC_Equiv_Tuples.

Section ac_equiv_aph.

Lemma alpha_equiv_to_ac_equiv : forall C t t', 
 C |- t ~alpha t' -> C |- t ~ac t'.
Proof. 
 intros. induction H; auto; 
 simpl in H; try contradiction. 
 apply ac_equiv_Fc; trivial.
Qed.

Hint Resolve alpha_equiv_to_ac_equiv.

Lemma ac_equiv_alpha_equiv_trans : forall C t1 t2 t3, 
  C |- t1 ~ac t2 -> C |- t2 ~alpha t3 -> C |- t1 ~ac t3.
Proof.
 intros. gen t3 H0. induction H; intros; auto.
 inverts H1. apply equiv_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.
 inverts H1. apply equiv_Fc; auto. 
 inverts H0. apply equiv_Ab_1; apply IHequiv; trivial.
 apply equiv_Ab_2; trivial. apply IHequiv; trivial.
 inverts H2. apply equiv_Ab_2; trivial.
 apply IHequiv. apply alpha_equiv_eq_equiv.
 apply alpha_equiv_eq_equiv; trivial.
 apply alpha_equiv_equivariance; trivial.
 apply alpha_equiv_fresh with (t1 := t'); trivial.
 case (a ==at a'0); intro H10. rewrite H10.
 apply equiv_Ab_1. apply IHequiv. apply alpha_equiv_sym.
 apply alpha_equiv_swap_inv_side.
 apply alpha_equiv_trans with (t2 := (|[ (a', a)]) @ t'0).
 apply alpha_equiv_swap_comm. apply alpha_equiv_sym. rewrite H10; trivial.
 assert (Q : C |- a # t'0).
  apply alpha_equiv_fresh with (a := a) in H7; trivial.
  apply fresh_lemma_1 in H7. simpl rev in H7. 
  rewrite swap_neither in H7; auto.
 apply equiv_Ab_2; trivial. apply IHequiv.
 apply alpha_equiv_sym. apply alpha_equiv_swap_inv_side. apply alpha_equiv_sym.
 apply alpha_equiv_trans with (t2 := (|[ (a', a'0)]) @ t'0); trivial.
 apply alpha_equiv_trans with 
 (t2 := (|[ (|[(a, a')] $ a, |[(a, a')] $ a'0)]) @ ((|[ (a, a')]) @ t'0)); trivial.
 rewrite swap_left. rewrite swap_neither; auto.
 apply alpha_equiv_equivariance. apply alpha_equiv_sym. 
 apply alpha_equiv_swap_neither; trivial. apply alpha_equiv_sym. 
 apply alpha_equiv_pi_comm.

 inverts H0. apply equiv_Su. intros. unfold In_ds in *|-.
 case (a ==at (!p $ (p' $ a))); intro H1. rewrite H1. apply H5.
 rewrite <- H1. apply perm_inv_side_atom in H1. rewrite <- H1. trivial.
 rewrite perm_diff_atom with (p:=p) in H1. gen_eq g : (!p). intro H2.
 replace (p $ (g $ (p' $ a))) with (!g $ (g $ (p' $ a))) in H1.
 rewrite perm_inv_atom in H1. apply H; trivial. rewrite H2.
 rewrite perm_inv_inv_atom; trivial.

 inverts H3.
 apply equiv_Fc_TPlength_1; auto.
 apply alpha_equiv_TPlength with (m:=m) (n:=n) in H9. omega.
 apply IHequiv. apply alpha_equiv_TPith; trivial.

 simpl in H0. destruct H0; try omega.

 simpl in H. destruct H; try omega. rewrite <- H in *|-*. clear m H H0.
 destruct H1. destruct H0. destruct H1. inverts H4.
 apply equiv_AC with (i:=i); trivial.  
 simpl; left; trivial. (* left; trivial. *)
 apply alpha_equiv_TPlength with (m:=1) (n:=n) in H11. 
 repeat split; trivial; try omega.
 apply IHequiv1. apply alpha_equiv_TPith; trivial.
 apply IHequiv2. apply alpha_equiv_Fc. apply alpha_equiv_TPithdel; trivial.

Qed.

Lemma ac_equiv_equivariance : forall C t1 t2 pi,  
 C |- t1 ~ac t2 -> C |- (pi @ t1) ~ac (pi @ t2).
Proof.
 intros. induction H; intros;
 autorewrite with perm; auto.
 apply equiv_Ab_2. apply perm_diff_atom; trivial.
 apply ac_equiv_alpha_equiv_trans with (t2 :=  (pi @ ((|[(a, a')]) @ t'))); auto.
 apply alpha_equiv_pi_comm. apply fresh_lemma_3; trivial.
 apply equiv_Su. intros. apply H. intro. apply H0.
 rewrite <- 2 perm_comp_atom. rewrite H1; trivial. 

 rewrite 2 Perm_TPith in IHequiv; trivial.
 apply equiv_Fc_TPlength_1; autorewrite with tuples; trivial. 
 
 simpl in H0; destruct H0; omega.

 destruct H1. destruct H4. destruct H5.
 autorewrite with perm in *|-.
 apply equiv_AC with (i:=i) ; trivial. 
 repeat split; autorewrite with tuples; trivial.
 rewrite <- 2 Perm_TPith; trivial.
 rewrite <- 2 Perm_TPithdel; trivial.

Qed.


Lemma ac_equiv_swap_inv_side : forall C a a' t t', 
 C |- t ~ac ((|[ (a, a')]) @ t') -> C |- ((|[ (a', a)]) @ t) ~ac t'. 
Proof.
 intros. 
 apply ac_equiv_alpha_equiv_trans with 
 (t2 := (|[ (a', a)]) @ ((|[ (a, a')]) @ t')).
 apply ac_equiv_equivariance; trivial.
 apply alpha_equiv_trans with (t2 := (|[ (a, a')]) @ ((|[ (a, a')]) @ t')).
 apply  alpha_equiv_swap_comm. rewrite perm_comp. apply alpha_equiv_perm_inv.
Qed.


Lemma ac_equiv_fresh : forall C a t1 t2, C |- t1 ~ac t2 -> C |- a # t1 -> 
                                         C |- a # t2.
Proof.
 intros. induction H; trivial.
 apply fresh_Pr_elim in H0. destruct H0.
 apply fresh_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.
 apply fresh_Fc_elim in H0. apply fresh_Fc; apply IHequiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. rewrite H0. apply fresh_Ab_1.
 destruct H0. apply fresh_Ab_2; trivial. apply IHequiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. apply fresh_Ab_2.
 intro. apply H. rewrite <- H0. trivial. rewrite <- H0 in H2. trivial.
 destruct H0. case (a ==at a'); intros.
 rewrite e. apply fresh_Ab_1. apply fresh_Ab_2; trivial.
 assert (Q : C |- a # ((|[(a0, a')]) @ t')).  apply IHequiv; trivial.
 apply fresh_lemma_1 in Q. simpl rev in Q. rewrite swap_neither in Q; trivial.
 intro. apply H0. rewrite H4; trivial. intro. apply n. rewrite H4; trivial.
 apply fresh_Su. apply fresh_Su_elim in H0.
 case (((!p) $ a) ==at ((!p') $ a)); intros. rewrite <- e; trivial.
 apply H; intros. intro. apply n. gen_eq g : (!p'); intro. 
 replace p' with (!g) in H1. rewrite perm_inv_atom in H1. 
 replace ((!p) $ a) with ((!p) $ (p $ (g $ a))). rewrite perm_inv_atom. trivial.
 rewrite H1. trivial. rewrite H2. rewrite rev_involutive. trivial.

 apply fresh_Fc. apply fresh_Fc_elim in H0.
 apply fresh_TPith_TPithdel with (i:=1) (m:=m) (n:=n); trivial.
 split; trivial. apply IHequiv.
 apply fresh_TPith_TPithdel; trivial.
 rewrite TPithdel_TPlength_1; auto.
 
 simpl in H1. destruct H1; try omega.
  
 rewrite H1 in *|-*. clear H H1.
 destruct H2. destruct H1. destruct H2.
 apply fresh_TPith_TPithdel with (i:=i) (m := 1) (n := n).
 autorewrite with tuples. rewrite TPithdel_Fc_eq; try omega.
 split; [apply IHequiv1 | apply IHequiv2; apply fresh_Fc]; 
 apply fresh_TPith_TPithdel; apply fresh_Fc_elim in H0; trivial. 

Qed.

End ac_equiv_aph.


Section ac_equiv_equivalence.

Lemma ac_equiv_refl : forall C t, C |- t ~ac t.
Proof.
 intros. induction t; auto. 
 apply ac_equiv_Fc; trivial.
 apply equiv_Su. intros. false. 
 unfold In_ds in H. apply H. trivial. 
Qed.

Hint Resolve ac_equiv_refl.

Lemma ac_equiv_swap_comm : forall C t a a', 
  C |- (|[ (a, a')]) @ t ~ac ((|[ (a', a)]) @ t) .
Proof.
 intros. apply ac_equiv_alpha_equiv_trans with 
 (t2 := (|[ (a, a')]) @ t); auto. 
 apply alpha_equiv_swap_comm.
Qed.


Hint Resolve alpha_equiv_to_ac_equiv.
Hint Resolve ac_equiv_TPlength.


Lemma ac_equiv_trans : forall C t1 t2 t3,
 C |- t1 ~ac t2 -> C |- t2 ~ac t3 -> C |- t1 ~ac t3.
Proof.
 introv. gen_eq l : (size_term t1). gen t1 t2 t3.
 induction l using peano_induction; intros. 

 inverts H1; inverts H2; auto; simpl in *|-; try omega; try contradiction.
 
 simpl in H0. apply equiv_Pr. 
 apply H with (t2 := t1') (m := size_term t0); try omega; trivial.
 apply H with (t2 := t2') (m := size_term t4); try omega; trivial. 

 simpl in H0. apply equiv_Fc; trivial.
 apply H with (t2 := t') (m := size_term t); try omega; trivial.

 apply equiv_Ab_1. 
 apply H with (t2 := t') (m := size_term t); try omega; trivial.
 simpl in H0. apply equiv_Ab_2; trivial.
 apply H with (t2 := t') (m := size_term t); try omega; trivial. 
 simpl in H0. apply equiv_Ab_2; trivial.
 apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); try omega; trivial.
 apply ac_equiv_equivariance; trivial. 
 apply ac_equiv_fresh with (a:=a) in H9; trivial.

 case (a ==at a'0); intro H1. rewrite H1. 
 simpl in H0. apply equiv_Ab_1.
 apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); try omega; trivial.
 apply ac_equiv_swap_inv_side. rewrite H1. trivial.

 assert (Q:  C |- a # t'0). 
  apply ac_equiv_fresh with (a:=a) in H9; trivial.
  apply fresh_lemma_1 in H9. simpl rev in H9. 
  rewrite swap_neither in H9; auto.
 apply equiv_Ab_2; trivial.
 assert (Q' : C |- t ~ac ((|[ (a, a')]) @ ((|[ (a', a'0)]) @ t'0))). 
  apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); trivial. 
  simpl in H0. omega. apply ac_equiv_equivariance; trivial.
 apply ac_equiv_alpha_equiv_trans with 
 (t2 := ((|[ (a, a')]) @ ((|[ (a', a'0)]) @ t'0))); trivial. 
 apply alpha_equiv_trans with 
 (t2 := (|[ ((|[(a,a')]) $ a', (|[(a,a')]) $ a'0)]) @ ((|[ (a, a')]) @ t'0)). 
 apply alpha_equiv_pi_comm. rewrite swap_right. rewrite swap_neither; trivial.
 apply alpha_equiv_equivariance. apply alpha_equiv_swap_neither; trivial.

 apply equiv_Su; intros.
 case (In_ds_dec p p' a); intros. apply H3; trivial.
 apply H7. apply not_In_ds in H2. unfold In_ds in *|-*. 
 rewrite <- H2; trivial.
 
 apply equiv_Fc_TPlength_1; try omega; trivial.
 apply H with (t2:=TPith 1 t' m n) (m:=size_term (TPith 1 t m n)); trivial. 
 assert (Q1 : size_term (TPith 1 t m n) <= size_term t). auto. omega.

 clear H3 H9 H10. destruct H5. destruct H2. destruct H3.
 destruct H12. destruct H8. destruct H9.
 assert (Q: C |- Fc 1 n t' ~ac Fc 1 n t'0). 
  apply equiv_AC with (i:=i0); repeat split; trivial.
  simpl; left; trivial. 
 generalize Q; intro Q'.
 apply ac_equiv_TPlength with (m:=1) (n:=n) in Q. autorewrite with tuples in Q.
 apply ac_equiv_TPith_l with (i:=i) (m:=1) (n:=n) in Q';
 autorewrite with tuples; try omega.
 destruct Q'. destruct H11. destruct H12. destruct H13. autorewrite with tuples in *|-.
 rewrite 2 TPithdel_Fc_eq in H16; autorewrite with tuples; trivial.
 apply equiv_AC with (i:=x); try split; try omega; trivial.
 simpl; left; trivial. apply H with (t2:=TPith i t' 1 n) (m:=size_term (TPith 1 t 1 n)); trivial. 
 assert (Q1 : size_term (TPith 1 t 1 n) <= size_term t). auto. omega.
 apply H with (t2:=Fc 1 n (TPithdel i t' 1 n)) (m:=size_term (Fc 1 n (TPithdel 1 t 1 n))); trivial. 
 assert (Q0 : TPlength t 1 n <> 1). omega.
 assert (Q1 : size_term (TPithdel 1 t 1 n) < size_term t). auto. 
 simpl. omega.

Qed. 

Lemma ac_equiv_sym : forall C t1 t2, C |- t1 ~ac t2 -> C |- t2 ~ac t1 .
Proof.
 intros. induction H; auto; simpl in *|-; try omega; trivial. 

 assert (Q0 : C |- t' ~ac ((|[(a', a)]) @ t)).
  apply ac_equiv_trans with (t2 := (|[(a, a')]) @ t).
  apply ac_equiv_trans with (t2 := (|[(a, a')]) @ ((|[(a, a')]) @ t')).
  apply ac_equiv_alpha_equiv_trans with (t2 := t'). apply ac_equiv_refl.
  apply alpha_equiv_swap_inv_side. apply alpha_equiv_refl.
  apply ac_equiv_equivariance; trivial.  apply ac_equiv_swap_comm. 
 assert (Q1 : C |- a # ((|[(a', a)]) @ t)).
  apply ac_equiv_fresh with (t1 := t'); trivial.
 apply fresh_lemma_1 in Q1. simpl rev in Q1. rewrite swap_right in Q1.
 apply equiv_Ab_2; trivial; auto.
 
 apply equiv_Su. intros. apply H. apply ds_sym. trivial.

 destruct H1. destruct H4. destruct H5.
 destruct H; try omega. rewrite <- H in *|-*. clear H H0.
 apply ac_equiv_AC with (i:=i) (j:=1); try omega; trivial.
 assert (Q: TPlength t 1 n >= 1). auto. omega.

Qed.

End ac_equiv_equivalence.