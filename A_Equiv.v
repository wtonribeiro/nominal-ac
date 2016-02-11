(***************************************************************************
 *A_Equiv.v   
***************************************************************************)

Require Export Equiv.

Section a_equiv_tuples.
  
(** a_equiv and tuples *)
  
Lemma a_equiv_TPlength : forall C t1 t2 m n, 
 C |- t1 ~a t2 -> TPlength t1 m n = TPlength t2 m n. 
Proof.
 intros. induction H; trivial. simpl; auto.
 case (m0 === m); case (n0 === n); intros H1 H2.
 rewrite H1. rewrite H2. autorewrite with tuples; trivial.
 rewrite 2 TPlength_Fc_diff_n; trivial. 
 rewrite 2 TPlength_Fc_diff_m; trivial.
 rewrite 2 TPlength_Fc_diff_n; trivial.
 
 simpl in H. destruct H; try contradiction.
 rewrite <- H in *|-*. clear H.
 case (m === 0); intro H3. case (n0 === n); intro H4. 
 rewrite H3 in *|-*. rewrite <- H4 in *|-*;
 autorewrite with tuples; try omega; clear H3 H4.
 rewrite 2 TPlength_Fc_diff_n; trivial.
 rewrite 2 TPlength_Fc_diff_m; try omega; trivial.
 
 simpl in H0. destruct H0; try contradiction. clear H.
 rewrite <- H0 in *|-*.
 case (m === 0); intro H4. case (n0 === n); intro H5. 
 rewrite H4 in *|-*. rewrite H5 in *|-*. clear H2 H3.
 autorewrite with tuples in *|-*. destruct H1.
 assert (Q : TPlength t 0 n >= 1 /\ TPlength t' 0 n >= 1). auto.
 rewrite 2 TPlength_TPithdel in IHequiv2; try omega. 
 rewrite 2 TPlength_Fc_diff_n; auto. 
 rewrite 2 TPlength_Fc_diff_m; auto.
 
 simpl in H; false; destruct H; omega.

Qed.

Lemma a_equiv_TPith : forall C t t' i m n, 
  C |- t ~a t' -> C |- TPith i t m n ~a TPith i t' m n.
Proof. 
 intros. gen i. induction H; intro.
 simpl. case_nat; auto. simpl. case_nat; auto. Focus 3.
 simpl. case_nat; auto. Focus 3. simpl. case_nat; auto.
 Focus 3. simpl. case_nat; auto.

 apply a_equiv_TPlength with (m:=m) (n:=n) in H.
 case (le_dec i (TPlength t1 m n)); intro H1. 
 rewrite 2 TPith_Pr_le; try omega; auto.
 rewrite 2 TPith_Pr_gt; try omega. rewrite H; auto.
 case (i === 0); intro H1. rewrite H1. rewrite 2 TPith_0; auto.
 generalize H0; intro H0'. apply a_equiv_TPlength with (m:=m) (n:=n) in H0.
 case (le_dec i (TPlength (Fc m0 n0 t) m n)); intro H2.
 case (m0 === m); intro H3. case (n0 === n); intro H4.
 rewrite H3. rewrite H4. autorewrite with tuples; auto.
 rewrite TPlength_Fc_diff_n in H2; trivial.
 rewrite 2 TPith_Fc_diff_n; auto. 
 rewrite TPlength_Fc_diff_m in H2; trivial.
 rewrite 2 TPith_Fc_diff_m; auto. 
 rewrite 2 TPith_overflow; try omega; auto.
 simpl in *|-*; repeat case_nat; omega.

 simpl in H. destruct H; try contradiction. rewrite <- H in *|-*.
 case (i === 0); intro H3. rewrite H3.
 rewrite 2 TPith_0; auto. 
 case (i === 1); intro H4. rewrite H4.
 case (0 === m); intro H5. case (n0 === n); intro H6.
 rewrite <- H5. rewrite H6 in *|-*. autorewrite with tuples. trivial.
 rewrite 2 TPith_Fc_diff_n; try omega.
 apply equiv_Fc_TPlength_1; trivial. simpl; left; trivial. 
 rewrite 2 TPith_Fc_diff_m; try omega.
 apply equiv_Fc_TPlength_1; trivial. simpl; left; trivial.
 assert (Qi: i > 1). omega.
 assert (Q: TPlength (Fc 0 n0 t) m n = 1).
  gen_eq k : 0; intro H5. simpl. repeat case_nat; try omega.
  rewrite <- e. trivial.
 assert (Q': TPlength (Fc 0 n0 t) m n = TPlength (Fc 0 n0 t') m n).
  gen_eq k : 0; intro H5. simpl. repeat case_nat; try omega.
  rewrite <- e. omega.
 rewrite 2 TPith_overflow; try omega; auto.

 clear H. simpl in H0; destruct H0; try contradiction. rewrite <- H in *|-*.
 case (i === 0); intro H4. rewrite H4. rewrite 2 TPith_0; auto. destruct H1.
 generalize H3; intro H3'. apply a_equiv_TPlength with (m:=m) (n:=n) in H3.
 case (le_dec i (TPlength (Fc 0 n0 t) m n)); intro H5.
 case (m === 0); intro H6. case (n0 === n); intro H7.
 rewrite H6 in *|-*. rewrite H7 in *|-*. autorewrite with tuples; auto.
 case (i === 1); intro H8. rewrite H8; trivial. 
 assert (Q' : TPlength t 0 n >= 1). auto.
 assert (Q'' : TPlength t' 0 n >= 1). auto.
 assert (Q: C |- TPith (i-1) (Fc 0 n (TPithdel 1 t 0 n)) 0 n ~a
             TPith (i-1) (Fc 0 n (TPithdel 1 t' 0 n)) 0 n). apply IHequiv2.
 autorewrite with tuples in *|-. rewrite 2 TPlength_TPithdel in H3; try omega.
 autorewrite with tuples in Q. rewrite 2 TPith_TPithdel_geq in Q; try omega.
 replace (i - 1 + 1) with i in Q; try omega; trivial.
 rewrite TPlength_Fc_diff_n in H5; trivial.
 rewrite 2 TPith_Fc_diff_n; trivial. apply equiv_A; try split; trivial.
 left; trivial. (* simpl; left; trivial. *)
 rewrite TPlength_Fc_diff_m in H5; try omega; trivial.
 rewrite 2 TPith_Fc_diff_m; try omega; trivial. apply equiv_A; try split; trivial.
 left; trivial. (* simpl; left; trivial. *) 
 rewrite 2 TPith_overflow; try omega; auto.
 assert (Q' : TPlength t 0 n >= 1). auto.
 assert (Q'' : TPlength t' 0 n >= 1). auto.
 gen_eq n1 : 0. intro H6. simpl in H5|-*.  
 repeat case_nat; try omega. rewrite <- e in *|-*.
 autorewrite with tuples in *|-.
 rewrite 2 TPlength_TPithdel in H3; try omega.
 
 simpl in H; false; destruct H; omega.

Qed. 

Lemma a_equiv_TPithdel : forall C t t' i m n, 
  C |- t ~a t' -> C |- TPithdel i t m n ~a TPithdel i t' m n.
Proof. 
 intros. gen i. induction H; intro.
 simpl; case_nat; auto. simpl; case_nat; auto. Focus 3.
 simpl; case_nat; auto. Focus 3. simpl; case_nat; auto. Focus 3.
 simpl; case_nat; auto. 
 
 generalize H H0; intros H' H0'.
 apply a_equiv_TPlength with (m := m) (n := n) in H'. 
 apply a_equiv_TPlength with (m := m) (n := n) in H0'. 
 case (i === 0); intro H1. rewrite H1. rewrite 2 TPithdel_0; auto.
 case (le_dec i (TPlength t1 m n)); intro H2. 
 case (TPlength t1 m n === 1); intro H3. assert (Q:i=1). omega.
 rewrite Q. rewrite 2 TPithdel_t1_Pr; try omega; trivial.
 rewrite 2 TPithdel_Pr_le; try omega; trivial. auto.
 case (le_dec i (TPlength t1 m n + TPlength t2 m n)); intro H3.
 case (TPlength t2 m n === 1); intro H4. assert (Q:i=TPlength t1 m n + 1). omega.
 rewrite Q. rewrite TPithdel_t2_Pr; try omega; trivial. rewrite H'.
 rewrite TPithdel_t2_Pr; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try omega; trivial. rewrite H'. auto.
 rewrite 2 TPithdel_overflow; simpl; try omega; auto.
 
 generalize H0; intro H0'.
 apply a_equiv_TPlength with (m := m) (n := n) in H0'. 
 case (i === 0); intro H1. rewrite H1. rewrite 2 TPithdel_0; auto.
 case (m0 === m); intro H2. case (n0 === n); intro H3.
 rewrite H2. rewrite H3. case (le_dec i (TPlength t m n)); intro H4. 
 case (TPlength t m n === 1); intro H5. assert (Q:i=1). omega.
 rewrite Q. rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; 
 try omega; trivial. rewrite 2 TPithdel_Fc_eq; try omega; trivial.
 apply equiv_Fc. rewrite <- H2. trivial. apply IHequiv.
 rewrite 2 TPithdel_overflow; simpl; repeat case_nat; try omega.
 apply equiv_Fc; trivial. rewrite <- H2. trivial.
 case (i === 1); intro H4. rewrite H4. rewrite 2 TPithdel_TPlength_1; auto.
 rewrite 2 TPithdel_Fc_diff_n; auto.
 case (i === 1); intro H4. rewrite H4. rewrite 2 TPithdel_TPlength_1; auto.
 rewrite 2 TPithdel_Fc_diff_m; auto.

 simpl in H. destruct H; try contradiction. rewrite <- H in *|-*.
 case (i === 0); intro H3. rewrite H3. rewrite 2 TPithdel_0.
 apply equiv_Fc_TPlength_1; trivial. simpl. left. trivial.
 case (le_dec i (TPlength (Fc 0 n0 t) m n)); intro H4.
 case (0 === m); intro H5. case (n0 === n); intro H6.
 rewrite <- H5 in *|-*. rewrite H6 in *|-*.
 autorewrite with tuples in H4.
 assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; auto.
 rewrite TPlength_Fc_diff_n in H4; trivial. assert (Qi:i=1). omega.
 rewrite Qi. rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_n; trivial.
 rewrite TPlength_Fc_diff_m in H4; try omega; trivial. assert (Qi:i=1). omega.
 rewrite Qi. rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; trivial.
 rewrite 2 TPithdel_overflow; autorewrite  with tuples; try omega.
 apply equiv_Fc_TPlength_1; trivial. simpl. left; trivial. gen_eq k : 0; intro Hk.
 simpl in *|-*. repeat case_nat; try omega. rewrite <- e in *|-*. omega.

 simpl in H0. destruct H0; try contradiction. clear H.
 rewrite <- H0 in *|-*. destruct H1. generalize H3; intro H3'.
 apply a_equiv_TPlength with (m := m) (n := n) in H3'. 
 case (0 === m); intro H4. case (n0 === n); intro H5.
 rewrite <- H4 in *|-*. rewrite H5 in *|-*. autorewrite with tuples in H3'.
 assert (Q : TPlength t 0 n >= 1). auto.
 assert (Q' : TPlength t' 0 n >= 1). auto.
 rewrite 2 TPlength_TPithdel in H3'; try omega; trivial.
 case (i === 0); intro H6. rewrite H6. rewrite 2 TPithdel_0.
 apply equiv_A; repeat split; trivial. left; trivial. 
 case (le_dec i (TPlength t 0 n)); intro H7. 
 case (TPlength t 0 n === 1); intro H8. assert (Qi:i=1). omega.
 rewrite Qi. rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega.
 rewrite 2 TPithdel_Fc_eq; try omega; trivial. 
 case (i === 1); intro H9. rewrite H9; trivial.
 case (TPlength t 0 n === 2); intro H10. clear IHequiv1 IHequiv2. 
 assert (Qi : i = 2). omega. rewrite Qi in *|-*.
 assert (Q'' : TPlength t' 0 n = 2). omega.
 apply TPlength_2 in H10.
 case H10; clear H10. intros i0 H10.
 case H10; clear H10. intros t1 H10.
 case H10; clear H10. intros t2 H10. destruct H10. destruct H11.
 apply TPlength_2 in Q''.
 case Q''; clear Q''. intros i1 H13.
 case H13; clear H13. intros t'1 H13.
 case H13; clear H13. intros t'2 H13. destruct H13. destruct H14.
 rewrite H10. rewrite H13. rewrite 2 TPithdel_Fc_app; simpl TPlength; try omega.
 replace 2 with (TPlength t1 0 n + 1); try omega. rewrite TPithdel_t2_Pr; try omega.
 replace (TPlength t1 0 n) with (TPlength t'1 0 n); try omega. rewrite TPithdel_t2_Pr; try omega.
 rewrite H10 in H2. rewrite H13 in H2. rewrite 2 TPith_Fc_app in H2.
 rewrite 2 TPith_Pr_le in H2; try omega.  
 rewrite 2 Fc_app_Sn. apply Fc_app_TPlength_1; trivial; try omega.
 simpl; left; trivial. 
 apply equiv_A; trivial. left; trivial. (* simpl; left; trivial. *)
 repeat split; try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite 2 TPith_TPithdel_lt; try omega; trivial.
 rewrite 2 TPithdel_comm_lt with (i:=1); try omega; trivial.
 assert (Q0:  C |- TPithdel (i - 1) (Fc 0 n (TPithdel 1 t 0 n)) 0 n ~a
             TPithdel (i - 1) (Fc 0 n (TPithdel 1 t' 0 n)) 0 n). auto.
 rewrite 2 TPithdel_Fc_eq in Q0; autorewrite with tuples; 
 try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite 2 TPithdel_overflow; simpl; repeat case_nat; try omega; auto.
 apply equiv_A; trivial. left; trivial. (* simpl; left; trivial. *)
 repeat split; trivial. 
 case (i === 1); intro H6. rewrite H6. rewrite 2 TPithdel_TPlength_1; auto.
 rewrite 2 TPithdel_Fc_diff_n; auto.
 apply equiv_A; trivial. left; trivial. 
 repeat split; trivial.  
 case (i === 1); intro H5. rewrite H5. rewrite 2 TPithdel_TPlength_1; auto.
 rewrite 2 TPithdel_Fc_diff_m; auto.
 apply equiv_A; trivial. left; trivial.
 repeat split; trivial. 

 simpl in H; false; destruct H; omega.

Qed.
    

Lemma a_equiv_Fc : forall C t t' m n, C |- t ~a t' -> C |- Fc m n t ~a Fc m n t'.
Proof.
  intros. gen_eq l : (TPlength t m n); intro H0.
  gen t t' H0 H. induction l using peano_induction; intros.
  case (m === 0); intro Hm. Focus 2.
  apply equiv_Fc; trivial. intro. simpl in H2. destruct H2; try omega.
  rewrite Hm in *|-*. clear Hm.
  generalize H1; intro H1'. apply a_equiv_TPlength with (m:=0) (n:=n) in H1'.
  case (TPlength t 0 n === 1); intro H2.
  apply equiv_Fc_TPlength_1; try omega. simpl; left; trivial.
  apply a_equiv_TPith; trivial.  
  case (TPlength t 0 n === 2); intro H3. 
  assert (H4 : TPlength t' 0 n = 2). omega.
  apply TPlength_2 in H3. apply TPlength_2 in H4.
  destruct H3. destruct H4.
  case H3; clear H3; intros t1 H3.
  case H3; clear H3; intros t2 H3.  
  destruct H3. destruct H5.
  case H4; clear H4; intros t1' H4.
  case H4; clear H4; intros t2' H4.  
  destruct H4. destruct H7.
  rewrite H3 in H1|-*. rewrite H4 in H1|-*.
  apply equiv_A; trivial. left; trivial. (* simpl; left; trivial. *)
  repeat split; try rewrite TPlength_Fc_app; simpl; try omega.
  rewrite 2 TPith_Fc_app. rewrite 2 TPith_Pr_le; try omega.
  apply a_equiv_TPith with (i:=1) (m:=0) (n:=n) in H1.
  rewrite 2 TPith_Fc_app in H1.
  rewrite 2 TPith_Pr_le in H1; try omega; trivial.
  rewrite 2 TPithdel_Fc_app; simpl TPlength; try omega.
  rewrite 2 TPithdel_t1_Pr; try omega. rewrite 2 Fc_app_Sn.
  apply a_equiv_TPith with (i:=2) (m:=0) (n:=n) in H1.
  rewrite 2 TPith_Fc_app in H1.
  replace 2 with (TPlength t1 0 n + 1) in H1; try omega.  
  rewrite TPith_Pr_gt in H1; try omega.
  replace (TPlength t1 0 n) with (TPlength t1' 0 n) in H1; try omega.
  rewrite TPith_Pr_gt in H1; try omega.
  replace  (TPlength t1' 0 n + 1 - TPlength t1' 0 n) with 1 in H1; try omega.
  apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.
  assert (Q: TPlength t 0 n >= 1). auto.
  apply equiv_A; repeat split; try omega. left; trivial.
  apply a_equiv_TPith; trivial.
  apply H with (m:=TPlength t 0 n - 1);
  try rewrite TPlength_TPithdel; try omega.
  apply a_equiv_TPithdel; trivial.
Qed.


Hint Resolve a_equiv_TPlength.
Hint Resolve a_equiv_TPith.
Hint Resolve a_equiv_TPithdel.
Hint Resolve a_equiv_Fc.

End a_equiv_tuples.


Section a_equiv_aph.

Lemma alpha_equiv_to_a_equiv : forall C t t', 
 C |- t ~alpha t' -> C |- t ~a t'.
Proof.
   intros. induction H; auto; simpl in H;
   try contradiction. apply a_equiv_Fc; trivial.
Qed.

Hint Resolve alpha_equiv_to_a_equiv.


Lemma a_equiv_alpha_equiv_trans : forall C t1 t2 t3, 
  C |- t1 ~a t2 -> C |- t2 ~alpha t3 -> C |- t1 ~a t3.
Proof.
 intros. gen t3 H0. induction H; intros; auto.
 inverts H1. apply equiv_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.
 inverts H1. apply a_equiv_Fc; auto.
 inverts H0. apply equiv_Ab_1; apply IHequiv; auto.
 apply equiv_Ab_2; auto. 
 inverts H2. apply equiv_Ab_2; auto.
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

 inverts H3. simpl in H. destruct H; try omega.
 rewrite <- H in *|-*.  apply equiv_Fc_TPlength_1; trivial.
 simpl; left; trivial.
 apply alpha_equiv_TPlength with (m:=0) (n:=n) in H9. omega. 
 apply IHequiv. apply alpha_equiv_TPith; trivial.
 
 inverts H4. destruct H1. simpl in H0. destruct H0; try omega.
 rewrite <- H0 in *|-*.  clear H H0. apply equiv_A; trivial.
 left; trivial.  split; trivial. 
 apply alpha_equiv_TPlength with (m:=0) (n:=n) in H10. omega.
 apply IHequiv1. apply alpha_equiv_TPith; trivial.
 apply IHequiv2. apply alpha_equiv_Fc. apply alpha_equiv_TPithdel; trivial.
 
 simpl in H. destruct H; try omega.

Qed.


Lemma a_equiv_equivariance : forall C t1 t2 pi,  
 C |- t1 ~a t2 -> C |- (pi @ t1) ~a (pi @ t2).
Proof.
 intros. induction H; intros;
 autorewrite with perm; auto.
 apply equiv_Ab_2. apply perm_diff_atom; trivial.
 apply a_equiv_alpha_equiv_trans with (t2 :=  (pi @ ((|[(a, a')]) @ t'))); auto.
 apply alpha_equiv_pi_comm. apply fresh_lemma_3; trivial.
 apply equiv_Su. intros. apply H. intro. apply H0.
 rewrite <- 2 perm_comp_atom. rewrite H1; trivial. 

 rewrite 2 Perm_TPith in IHequiv; trivial.
 apply equiv_Fc_TPlength_1; autorewrite with tuples; trivial. 
 
 autorewrite with perm in *|-.
 destruct H1. simpl in H0. destruct H0; try omega.
 rewrite <- H0 in *|-*.  apply equiv_A; repeat split; 
 autorewrite with tuples; trivial. simpl; left; trivial.

 rewrite <- 2 Perm_TPith; trivial.
 rewrite <- 2 Perm_TPithdel; trivial.

 simpl in H; destruct H; try omega.

Qed.

Lemma a_equiv_swap_inv_side : forall C a a' t t', 
 C |- t ~a ((|[ (a, a')]) @ t') -> C |- ((|[ (a', a)]) @ t) ~a t'. 
Proof.
 intros. 
 apply a_equiv_alpha_equiv_trans with 
 (t2 := (|[ (a', a)]) @ ((|[ (a, a')]) @ t')).
 apply a_equiv_equivariance; trivial.
 apply alpha_equiv_trans with (t2 := (|[ (a, a')]) @ ((|[ (a, a')]) @ t')).
 apply  alpha_equiv_swap_comm. rewrite perm_comp. apply alpha_equiv_perm_inv.
Qed.

 
Lemma a_equiv_fresh : forall C a t1 t2, C |- t1 ~a t2 -> C |- a # t1 -> 
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
 simpl in H. destruct H; try omega. rewrite <- H in *|-*. clear H.
 apply fresh_TPith_TPithdel with (i:=1) (m:=0) (n:=n); trivial.
 split. apply IHequiv. apply fresh_TPith_TPithdel; trivial.
 rewrite TPithdel_TPlength_1; auto.
  
 apply fresh_Fc. apply fresh_Fc_elim in H0. 
 apply fresh_TPith_TPithdel with (i:=1) (m:=0) (n:=n).
 apply fresh_TPith_TPithdel with (i:=1) (m:=0) (n:=n) in H0.
 simpl in H1. destruct H1; try omega. rewrite <- H1 in *|-*. clear H H1.
 destruct H2. destruct H0. split. apply IHequiv1; trivial.
 apply fresh_Fc_elim with (m:=0) (n:=n).
 apply IHequiv2. apply fresh_Fc; trivial.

 simpl in H. destruct H; try omega.

Qed.

End a_equiv_aph.

Section a_equiv_equivalence.

Lemma a_equiv_refl : forall C t, C |- t ~a t.
Proof.
 intros. induction t; auto. apply a_equiv_Fc; trivial.
 apply equiv_Su. intros. false. 
 unfold In_ds in H. apply H. trivial. 
Qed.

Hint Resolve a_equiv_refl.

Lemma a_equiv_swap_comm : forall C t a a', 
  C |- (|[ (a, a')]) @ t ~a ((|[ (a', a)]) @ t) .
Proof.
 intros. apply a_equiv_alpha_equiv_trans with 
 (t2 := (|[ (a, a')]) @ t); auto. 
 apply alpha_equiv_swap_comm.
Qed.

Lemma a_equiv_trans : forall C t1 t2 t3,
 C |- t1 ~a t2 -> C |- t2 ~a t3 -> C |- t1 ~a t3.
Proof.
 introv. gen_eq l : (size_term t1). gen t1 t2 t3.
 induction l using peano_induction; intros. 

 inverts H1; inverts H2; try contradiction; simpl in *|-; try omega; auto.
 
 simpl in H0. apply equiv_Pr. 
 apply H with (t2 := t1') (m := size_term t0); try omega; trivial.
 apply H with (t2 := t2') (m := size_term t4); try omega; trivial. 

 simpl in H0. apply equiv_Fc; trivial.
 apply H with (t2 := t') (m := size_term t); try omega; trivial.

  simpl in H0. apply equiv_Ab_1. 
 apply H with (t2 := t') (m := size_term t); try omega; trivial.
 simpl in H0. apply equiv_Ab_2; trivial.
 apply H with (t2 := t') (m := size_term t); try omega; trivial. 
 simpl in H0. apply equiv_Ab_2; trivial.
 apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); try omega; trivial.
 apply a_equiv_equivariance; trivial. 
 apply a_equiv_fresh with (a:=a) in H9; trivial.

 case (a ==at a'0); intro H1. rewrite H1. 
 simpl in H0. apply equiv_Ab_1.
 apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); try omega; trivial.
 apply a_equiv_swap_inv_side. rewrite H1. trivial.

 assert (Q:  C |- a # t'0). 
  apply a_equiv_fresh with (a:=a) in H9; trivial.
  apply fresh_lemma_1 in H9. simpl rev in H9. 
  rewrite swap_neither in H9; auto.
 apply equiv_Ab_2; trivial.
 assert (Q' : C |- t ~a ((|[ (a, a')]) @ ((|[ (a', a'0)]) @ t'0))). 
  apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); trivial. 
  simpl in H0. omega. apply a_equiv_equivariance; trivial.
 apply a_equiv_alpha_equiv_trans with 
 (t2 := ((|[ (a, a')]) @ ((|[ (a', a'0)]) @ t'0))); trivial. 
 apply alpha_equiv_trans with 
 (t2 := (|[ ((|[(a,a')]) $ a', (|[(a,a')]) $ a'0)]) @ ((|[ (a, a')]) @ t'0)). 
 apply alpha_equiv_pi_comm. rewrite swap_right. rewrite swap_neither; trivial.
 apply alpha_equiv_equivariance. apply alpha_equiv_swap_neither; trivial. 

 apply equiv_Su; intros.
 case (In_ds_dec p p' a); intros. apply H3; trivial.
 apply H7. apply not_In_ds in H2. unfold In_ds in *|-*. 
 rewrite <- H2; trivial.

 simpl in H0. simpl in H3. destruct H3; try omega.
 rewrite <- H1 in *|-*.
 apply equiv_Fc_TPlength_1; try omega; trivial.
 apply H with (t2:=TPith 1 t' 0 n) (m:=size_term (TPith 1 t 0 n)); trivial. 
 assert (Q1 : size_term (TPith 1 t 0 n) <= size_term t). auto. omega.

 destruct H5. destruct H12. 
 apply equiv_A; try split; try omega; trivial. 
 apply H with (t2:=TPith 1 t' 0 n) (m:=size_term (TPith 1 t 0 n)); trivial. 
 assert (Q1 : size_term (TPith 1 t 0 n) <= size_term t). auto. omega.
 apply H with (t2:=Fc 0 n (TPithdel 1 t' 0 n)) 
 (m:=size_term (Fc 0 n (TPithdel 1 t 0 n))); trivial. 
 assert (Q1 : size_term (TPithdel 1 t 0 n) < size_term t). auto. 
 simpl. omega.
 
Qed.

Lemma a_equiv_sym : forall C t1 t2, C |- t1 ~a t2 -> C |- t2 ~a t1 .
Proof.
 intros. induction H; auto; trivial. 
  assert (Q0 : C |- t' ~a ((|[(a', a)]) @ t)).
  apply a_equiv_trans with (t2 := (|[(a, a')]) @ t).
  apply a_equiv_trans with (t2 := (|[(a, a')]) @ ((|[(a, a')]) @ t')).
  apply a_equiv_alpha_equiv_trans with (t2 := t'). apply a_equiv_refl.
  apply alpha_equiv_swap_inv_side. apply alpha_equiv_refl.
  apply a_equiv_equivariance; trivial.  apply a_equiv_swap_comm. 
 assert (Q1 : C |- a # ((|[(a', a)]) @ t)).
  apply a_equiv_fresh with (t1 := t'); trivial.
 apply fresh_lemma_1 in Q1. simpl rev in Q1. rewrite swap_right in Q1.
 apply equiv_Ab_2; trivial; auto. 
 apply equiv_Su. intros. apply H. apply ds_sym. trivial.
 destruct H1. apply equiv_A; trivial. simpl. split; trivial.

 simpl in H; try omega.


Qed.

Hint Resolve a_equiv_refl.
Hint Resolve a_equiv_trans.
Hint Resolve a_equiv_sym.

End a_equiv_equivalence.
