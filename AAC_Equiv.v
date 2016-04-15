(*
 ============================================================================
 Project     : Nominal AC Unification
 File        : AAC_Equiv.v 
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: April 15, 2016.

 This is a guideline how to deal with A and AC equivalence
 starting from the notion of alpha-equivalence for purely non A or AC
 nominal terms.  The idea is we've defined jet a notion of alpha-
 equivalence for nominal terms without A or AC function symbols. Now,
 the signature is extended allowing both.  

 ============================================================================
*)

Require Export Equiv_Tuples.


Lemma alpha_to_aac_equiv : forall C t t', 
 C |- t ~alpha t' -> C |- t ~aac t'.
Proof. 
 intros. induction H; auto; 
 simpl in H; try contradiction. 
 apply aac_equiv_Fc; trivial.
Qed.

Hint Resolve alpha_to_aac_equiv.

(** Intermediate transitiviy *)

Lemma aac_alpha_equiv_trans : forall C t1 t2 t3, 
  C |- t1 ~aac t2 -> C |- t2 ~alpha t3 -> C |- t1 ~aac t3.
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

 inverts H2. 
 apply equiv_A; simpl set_In; try omega.
 apply IHequiv1. apply alpha_equiv_TPith; auto.
 generalize H8; intro H8'.
 assert (Q : C |- Fc 0 n t ~aac Fc 0 n t').
  apply equiv_A; simpl set_In; try omega; trivial.              
 apply alpha_equiv_TPlength with (E:=0) (n:=n) in H8'.
 apply aac_equiv_TPlength with (E:=0) (n:=n) in Q.
 autorewrite with tuples in Q.
 case (TPlength t 0 n === 1); intro H9.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 apply IHequiv2.
 rewrite 2 TPithdel_Fc_eq; autorewrite with tuples; try omega.
 apply alpha_equiv_Fc. apply alpha_equiv_TPithdel; trivial.

 inverts H2. generalize H8; intro H8'.
 assert (Q : C |- Fc 1 n t ~aac Fc 1 n t').
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega; trivial.              
 apply alpha_equiv_TPlength with (E:=1) (n:=n) in H8'.
 apply aac_equiv_TPlength with (E:=1) (n:=n) in Q.
 autorewrite with tuples in Q.
  apply equiv_AC with (i:=i); simpl set_In; repeat split~; try omega.
 apply IHequiv1. apply alpha_equiv_TPith; auto.
 case (TPlength t 1 n === 1); intro H9.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 apply IHequiv2.
 rewrite 2 TPithdel_Fc_eq; autorewrite with tuples; try omega.
 apply alpha_equiv_Fc. apply alpha_equiv_TPithdel; trivial.
Qed.

(** Equivariance of ~aac *)

Lemma aac_equivariance : forall C t1 t2 pi,  
 C |- t1 ~aac t2 -> C |- (pi @ t1) ~aac (pi @ t2).
Proof.
 intros. induction H; intros;
         autorewrite with perm; auto.
 
 apply equiv_Ab_2. apply perm_diff_atom; trivial.
 apply aac_alpha_equiv_trans with
 (t2 :=  (pi @ ((|[(a, a')]) @ t'))); auto.
 apply alpha_equiv_pi_comm.
 apply fresh_lemma_3; trivial.

 apply equiv_Su. intros. apply H. intro. apply H0.
 rewrite <- 2 perm_comp_atom. rewrite H1; trivial. 
 apply equiv_A; simpl set_In;
 autorewrite with tuples in *|-*; try omega.
 rewrite <- 2 Perm_TPith; trivial.
 assert (Q : C |- Fc 0 n t ~aac Fc 0 n t').
  apply equiv_A; simpl set_In; try omega; autorewrite with tuples; trivial.              
 apply aac_equiv_TPlength with (E:=0) (n:=n) in Q.
 autorewrite with tuples in Q. 
 case (TPlength t 0 n === 1); intro H2.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega.
 autorewrite with perm in IHequiv2.
 rewrite 2 Perm_TPithdel in IHequiv2; trivial.


 apply equiv_AC with (i:=i); repeat split~; simpl set_In;
 autorewrite with tuples in *|-*; try omega.
 rewrite <- 2 Perm_TPith; trivial.
 assert (Q : C |- Fc 1 n t ~aac Fc 1 n t').
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega;
  autorewrite with tuples; trivial.              
 apply aac_equiv_TPlength with (E:=1) (n:=n) in Q.
 autorewrite with tuples in Q.
 case (TPlength t 1 n === 1); intro H4.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega.
 autorewrite with perm in IHequiv2.
 rewrite 2 Perm_TPithdel in IHequiv2; trivial.
Qed.


Lemma aac_equiv_swap_inv_side : forall C a a' t t', 
 C |- t ~aac ((|[ (a, a')]) @ t') -> C |- ((|[ (a', a)]) @ t) ~aac t'. 
Proof.
 intros. 
 apply aac_alpha_equiv_trans with 
 (t2 := (|[ (a', a)]) @ ((|[ (a, a')]) @ t')).
 apply aac_equivariance; trivial.
 apply alpha_equiv_trans with (t2 := (|[ (a, a')]) @ ((|[ (a, a')]) @ t')).
 apply alpha_equiv_swap_comm. rewrite perm_comp. apply alpha_equiv_perm_inv.
Qed.


Lemma aac_equiv_fresh : forall C a t1 t2,
                          C |- t1 ~aac t2 ->
                          C |- a # t1 ->
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
 apply fresh_TPith_TPithdel with (i:=1) (E:=0) (n:=n).
 apply fresh_TPith_TPithdel with (i:=1) (E:=0) (n:=n) in H0.
 destruct H0. split~. autorewrite with tuples in *|-. auto.
 assert (Q : C |- Fc 0 n t ~aac Fc 0 n t').
  apply equiv_A; simpl set_In; try omega; trivial.              
 apply aac_equiv_TPlength with (E:=0) (n:=n) in Q.
 autorewrite with tuples in Q. 
 case (TPlength t 0 n === 1); intro H4.
 rewrite TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-; autorewrite with tuples; try omega.
 apply fresh_Fc_elim with (E:=0) (n:=n).
 apply IHequiv2. apply fresh_Fc; trivial.

 apply fresh_Fc. apply fresh_Fc_elim in H0.
 apply fresh_TPith_TPithdel with (i:=i) (E:=1) (n:=n).
 apply fresh_TPith_TPithdel with (i:=1) (E:=1) (n:=n) in H0.
 destruct H0. split~. autorewrite with tuples in *|-. auto.
 assert (Q : C |- Fc 1 n t ~aac Fc 1 n t').
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega; trivial.              
 apply aac_equiv_TPlength with (E:=1) (n:=n) in Q.
 autorewrite with tuples in Q.
 case (TPlength t 1 n === 1); intro H7.
 rewrite TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-; autorewrite with tuples; try omega.
 apply fresh_Fc_elim with (E:=1) (n:=n).
 apply IHequiv2. apply fresh_Fc; trivial. 
Qed.


Lemma aac_equiv_refl : forall C t, C |- t ~aac t.
Proof.
 intros. induction t; auto. 
 apply aac_equiv_Fc; trivial.
 apply equiv_Su. intros. false. 
 unfold In_ds in H. apply H. trivial. 
Qed.

Hint Resolve aac_equiv_refl.

Lemma aac_equiv_swap_comm : forall C t a a', 
  C |- (|[ (a, a')]) @ t ~aac ((|[ (a', a)]) @ t) .
Proof.
 intros. apply aac_alpha_equiv_trans with 
 (t2 := (|[ (a, a')]) @ t); auto. 
 apply alpha_equiv_swap_comm.
Qed.


Lemma aac_equiv_TPith_l : forall C t t' i E n, C |- t ~aac t' -> 
                         i > 0 -> i <= TPlength t E n ->
               exists j, j > 0 /\ j <= TPlength t' E n /\
                         C |- TPith i t E n ~aac TPith j t' E n /\ 
                         C |- TPithdel i t E n ~aac TPithdel j t' E n.
Proof.
  intros. gen_eq l : (TPlength t E n).
  intro H2. gen i t t' H2 H0 H1. induction l using peano_induction; intros.
  destruct H0.
  
  exists 1. simpl. repeat split~; try omega; auto.
  exists 1. simpl. repeat split~; try omega; auto.
 
  simpl in H2. generalize H0_ H0_0. intros H0' H0_0'.
  apply aac_equiv_TPlength with (E:=E) (n:=n) in H0'.
  apply aac_equiv_TPlength with (E:=E) (n:=n) in H0_0'.
  assert (Q:TPlength t1 E n >= 1 /\ TPlength t2 E n >= 1). auto. destruct Q.
  case (le_dec i (TPlength t1 E n)); intro H5.
  case H with (m:=TPlength t1 E n) (i:=i) (t:=t1) (t':=t1'); try omega; trivial; clear H.
  intros j H6. destruct H6. destruct H6. destruct H7. exists j.
  rewrite 2 TPith_Pr_le; try omega. 
  case (TPlength t1 E n === 1); intro H9.
  rewrite 2 TPithdel_t1_Pr; try omega. simpl.
  repeat split~; try omega; trivial.
  rewrite 2 TPithdel_Pr_le; try omega.
  simpl; repeat split~; try omega; auto.
  case H with (m:=TPlength t2 E n)
              (i:=i - TPlength t1 E n) (t:=t2) (t':=t2'); try omega; trivial; clear H.
  intros j H6. destruct H6. destruct H6. destruct H7. exists (TPlength t1 E n + j).
  rewrite 2 TPith_Pr_gt; try omega. rewrite <- H0'.
  replace (TPlength t1 E n + j - TPlength t1 E n) with j; try omega. 
  case (TPlength t2 E n === 1); intro H9.
  rewrite 2 TPithdel_t2_Pr; try omega.
  repeat split~; try omega; trivial. simpl; omega.
  rewrite 2 TPithdel_Pr_gt; try omega.
  replace (TPlength t1 E n + j - TPlength t1' E n) with j; try omega.
  simpl; repeat split~; try omega; auto.

  exists i. generalize H4; intro H4'.
  generalize H4; intro H4''.
  apply aac_equiv_TPlength with (E:=E0) (n:=n0) in H4'.
  apply aac_equiv_TPith_E_diff_1 with (i:=i) (E:=E0) (n:=n0) in H4. destruct H4.
  case ((E0,n0) ==np (E,n)); intro H6. inverts H6. autorewrite with tuples in *|-*.
  repeat split~; try omega; trivial.
  case (TPlength t E n === 1); intro H6.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try omega. apply aac_equiv_Fc; trivial.
  rewrite TPlength_Fc_diff in *|-*; trivial.
  rewrite 2 TPith_Fc_diff; trivial.
  rewrite 2 TPithdel_Fc_diff; trivial.
  repeat split~; try omega; auto. intro H5. apply H0.
  simpl; omega.

  exists 1. simpl. repeat split~; try omega; auto.
  exists 1. simpl. repeat split~; try omega; auto.
  exists 1. simpl. repeat split~; try omega; auto.
  
  clear H0. case (E === 1); intro H4.
  exists 1. assert (Q:(0,n0) <> (E,n)). intro. inverts H0. omega.
  rewrite TPlength_Fc_diff in *|-*; trivial.
  rewrite 2 TPith_Fc_diff; trivial.
  rewrite 2 TPithdel_Fc_diff; trivial.
  repeat split~; try omega; auto. 
  apply equiv_A; simpl set_In; try omega; trivial.
  exists i. split~; auto.
  assert (Q: C |- Fc 0 n0 t ~aac Fc 0 n0 t').
   apply equiv_A; simpl set_In; try omega; trivial.
  generalize Q; intro Q'. apply aac_equiv_TPlength with (E:=E) (n:=n) in Q'.
  apply aac_equiv_TPith_E_diff_1 with (E:=E) (n:=n) (i:=i) in Q; trivial.
  destruct Q. repeat split~; try omega; trivial.

  clear H0. case ((1,n0) ==np (E,n)); intro H4. inverts H4.
  autorewrite with tuples in *|-*.  
  
  case (i === 1); intro H4. rewrite H4.
  case (le_dec i0 1); intro H5.
  exists 1. case (i0 === 0); intro H6; repeat rewrite H6 in *|-;
  repeat rewrite TPith_0 in *|-; repeat rewrite TPithdel_0 in *|-. 
  repeat split~; trivial; autorewrite with tuples; auto.
  assert (Qi0:i0=1). omega. rewrite Qi0 in *|-.
  repeat split~; trivial; autorewrite with tuples; auto.

  case (le_dec i0 (TPlength t' 1 n)); intro H6.

  exists i0. repeat split~; autorewrite with tuples; try omega; trivial.
  exists (TPlength t' 1 n).
  rewrite TPith_overflow with (i:=i0) in H0_; autorewrite with tuples; try omega.
  rewrite TPithdel_overflow with (i:=i0) in H0_0; autorewrite with tuples; try omega.
  repeat split~; try omega; autorewrite with tuples in *|-*; auto.
  
  assert (Q0 : C |- Fc 1 n t ~aac Fc 1 n t').
   apply equiv_AC with (i:=i0); repeat split~; simpl set_In;
   autorewrite with tuples; try omega; trivial.              
  apply aac_equiv_TPlength with (E:=1) (n:=n) in Q0.
  autorewrite with tuples in Q0. 
  assert (Q: TPlength t 1 n >=1). auto.
  case (TPlength t 1 n === 1); intro H5; try omega.
  rewrite 2 TPithdel_Fc_eq in H0_0; try omega. 
  
  case H with (m  := TPlength (Fc 1 n (TPithdel 1 t 1 n)) 1 n) (i := i-1)
              (t  := Fc 1 n (TPithdel 1 t 1 n))
              (t' := Fc 1 n (TPithdel i0 t' 1 n));
              autorewrite with tuples;
              try rewrite TPlength_TPithdel; try omega; trivial; clear H.
     
  intros j Hj. destruct Hj. destruct H0 . destruct H6.  
  autorewrite with tuples in H6.
  apply aac_equiv_TPlength with (E:=1) (n:=n) in H0_0.
  autorewrite with tuples in H0_0.
  rewrite 2 TPlength_TPithdel in H0_0; try omega.

  case (le_dec i0 j); intro H8.
 
  exists (j + 1). autorewrite with tuples.
  rewrite 2 TPith_TPithdel_geq in H6; try omega.
  replace (i - 1 + 1) with i in *|-; try omega.
  rewrite 2 TPithdel_Fc_eq; try omega. 
  repeat split~; try omega; trivial.
  case (i0 === 0); intro H9. rewrite H9 in *|-.
  rewrite TPith_0 in H0_. rewrite TPithdel_0 in H7.
  
  apply equiv_AC with (i:=1); simpl set_In;
  repeat split~; try rewrite TPlength_TPithdel; try omega; trivial. 
  autorewrite with tuples. 
  rewrite 2 TPith_TPithdel_lt; try omega; trivial.
  case (TPlength t 1 n === 2); intro H10.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_TPithdel; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPithdel_Fc_eq in H7; try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_geq_comm in H7; try omega.
  rewrite TPithdel_geq_comm with (i:=j) in H7; try omega.
  replace (i - 1 + 1) with i in H7; try omega; trivial.

  apply equiv_AC with (i:=i0); simpl set_In;
  repeat split~; try rewrite TPlength_TPithdel; try omega; trivial. 
  autorewrite with tuples. 
  rewrite 2 TPith_TPithdel_lt; try omega; trivial.
  case (TPlength t 1 n === 2); intro H10.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_TPithdel; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPithdel_Fc_eq in H7; try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_geq_comm in H7; try omega.
  rewrite TPithdel_geq_comm with (i:=j) in H7; try omega.
  replace (i - 1 + 1) with i in H7; try omega; trivial.
  
  exists j.
  rewrite TPith_TPithdel_geq in H6; try omega.
  rewrite TPith_TPithdel_lt in H6; try omega.
  replace (i - 1 + 1) with i in *|-; try omega.
  rewrite 2 TPithdel_Fc_eq; try omega. autorewrite with tuples.
  repeat split~; try omega; trivial.

  case (le_dec i0 (TPlength t' 1 n)); intro H9.
  
  apply equiv_AC with (i:=i0-1); simpl set_In;
  repeat split~; try rewrite TPlength_TPithdel; try omega; trivial. 
  autorewrite with tuples. rewrite TPith_TPithdel_lt; try omega; trivial.
  rewrite TPith_TPithdel_geq; try omega; trivial.
  replace (i0 - 1 + 1) with i0; try omega; trivial.
  case (TPlength t 1 n === 2); intro H10.
  assert (Qi0:i0=2). omega. rewrite Qi0.
  replace (2-1) with 1; try omega.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_TPithdel; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPithdel_Fc_eq in H7; try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_geq_comm in H7; try omega.
  rewrite TPithdel_lt_comm with (i:=j) in H7; try omega.
  replace (i - 1 + 1) with i in H7; try omega; trivial.

  rewrite TPithdel_overflow with (i:=i0) in H7; try omega.
  rewrite TPith_overflow with (i:=i0) in H0_; try omega.

  apply equiv_AC with (i:=TPlength t' 1 n -1); simpl set_In;
  repeat split~; try rewrite TPlength_TPithdel; try omega; trivial. 
  autorewrite with tuples. rewrite TPith_TPithdel_lt; try omega; trivial.
  rewrite TPith_TPithdel_geq; try omega; trivial.
  replace (TPlength t' 1 n - 1 + 1) with (TPlength t' 1 n); try omega; trivial.
  case (TPlength t 1 n === 2); intro H10.
  assert (Qi0:TPlength t' 1 n=2). omega. rewrite Qi0.
  replace (2-1) with 1; try omega.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_TPithdel; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPithdel_Fc_eq in H7; try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_geq_comm in H7; try omega.
  rewrite TPithdel_lt_comm with (i:=j) in H7; try omega.
  replace (i - 1 + 1) with i in H7; try omega; trivial.
  
  exists 1. 
  rewrite TPlength_Fc_diff;
  try rewrite 2 TPith_Fc_diff; 
  try rewrite 2 TPithdel_Fc_diff; trivial.
  repeat split~; try omega.
  apply equiv_AC with (i:=i0); simpl set_In; try omega; trivial.  
Qed.

Lemma aac_equiv_TPith_l' : forall C t t' E n,  C |- t ~aac t' -> 
                           forall i, exists j, C |- TPith i t E n ~aac TPith j t' E n /\ 
                                               C |- TPithdel i t E n ~aac TPithdel j t' E n.
Proof.
  intros. case (i === 0); intro H0.
  rewrite H0. rewrite TPith_0. rewrite TPithdel_0.
  apply aac_equiv_TPith_l with (i:=1) (E:=E) (n:=n) in H; try omega; auto.
  destruct H. destruct H. destruct H1. destruct H2.
  exists x. split~.
  case (le_dec i (TPlength t E n)); intro H1.
  apply aac_equiv_TPith_l with (i:=i) (E:=E) (n:=n) in H; try omega.
  destruct H. destruct H. destruct H2. destruct H3.
  exists x. split~. 
  rewrite TPith_overflow; try omega.
  rewrite TPithdel_overflow; try omega.
  apply aac_equiv_TPith_l with (i:=TPlength t E n) (E:=E) (n:=n) in H; try omega; auto.
  destruct H. destruct H. destruct H2. destruct H3.
  exists x. split~.
Qed.
  
Lemma aac_equiv_AC : forall C t t' i j n,
      C |- TPith i (Fc 1 n t) 1 n ~aac TPith j (Fc 1 n t') 1 n  ->
      C |- TPithdel i (Fc 1 n t) 1 n ~aac TPithdel j (Fc 1 n t') 1 n ->
                           C |- Fc 1 n t ~aac Fc 1 n t'.
Proof.
  intros. gen_eq l : (TPlength t 1 n); intro H1.
  gen t t' H1 i j. induction l using peano_induction; intros.
  case (i === 1); intro Qi. rewrite Qi in *|-.
  apply equiv_AC with (i:=j); repeat split~; simpl set_In;
  try omega; trivial. 
  case (i === 0); intro Qi'. rewrite Qi' in *|-.
  repeat rewrite TPith_0 in *|-; repeat rewrite TPithdel_0 in *|-.
  apply equiv_AC with (i:=j); simpl set_In; try omega; trivial.  
  
  case (TPlength t 1 n === 1); case (TPlength t' 1 n === 1); intros H3 H4.
  apply equiv_AC with (i:=j); simpl set_In; try omega.
  autorewrite with tuples in *|-*. 
  try rewrite TPith_overflow with (i:=i) in H0; try omega.
  rewrite H4 in H0; trivial.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; trivial.
  rewrite TPithdel_TPlength_1 in H2; autorewrite with tuples; trivial.
  rewrite TPithdel_Fc_eq in H2; trivial. inverts H2.
  rewrite TPithdel_Fc_eq in H2; trivial.
  rewrite TPithdel_TPlength_1 with (t:= (Fc 1 n t'))in H2;
  autorewrite with tuples; trivial. inverts H2.  
  rewrite 2 TPithdel_Fc_eq in H2; try omega.
  autorewrite with tuples in H0.  
  generalize H2; intro H2'.
  apply aac_equiv_TPlength with (E:=1) (n:=n) in H2'.
  autorewrite with tuples in H2'.
  rewrite 2 TPlength_TPithdel in H2'; try omega; trivial.
  apply aac_equiv_TPith_l1 with (E:=1) (n:=n) in H2.
  destruct H2. destruct H2. destruct H5. destruct H6.
  autorewrite with tuples in *|-.
  rewrite TPlength_TPithdel in *|-; try omega.

  case (le_dec j x); intro H8.
   
  rewrite TPith_TPithdel_lt in H6; try omega.
  rewrite TPith_TPithdel_geq in H6; try omega.
  apply equiv_AC with (i:=x+1); 
  repeat split~; simpl set_In; try omega; trivial;
  try rewrite 2 TPithdel_Fc_eq; try omega.
  autorewrite with tuples; trivial.
  apply H with (i:=i-1) (j:=j) (m:=TPlength (TPithdel 1 t 1 n) 1 n);
  try rewrite TPlength_TPithdel; autorewrite with tuples; try omega.

  case (le_dec i (TPlength t 1 n)); intro H9.
  rewrite TPith_TPithdel_geq; try omega.

  case (j === 0); intro H10; try rewrite H10 in *|-*;
  repeat rewrite TPith_0 in *|-*;
  rewrite TPith_TPithdel_lt; try omega;
  replace (i -1 + 1) with i; try omega; trivial.
  rewrite TPith_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPith_overflow with (i:=i) in H0; try omega.
  rewrite TPith_TPithdel_geq; try omega.
  case (j === 0); intro H10; try rewrite H10 in *|-*;
  repeat rewrite TPith_0 in *|-*;
  rewrite TPith_TPithdel_lt; try omega;
  replace (TPlength t 1 n -1 + 1) with (TPlength t 1 n); try omega; trivial.  
  
  case (TPlength t 1 n === 2); intro H9.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; 
  try rewrite TPlength_TPithdel; try omega; auto.
  
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPithdel_Fc_eq in H7;
  try rewrite TPlength_TPithdel; try omega.

  case (le_dec i (TPlength t 1 n)); intro H10.
  
  rewrite TPithdel_lt_comm in H7; try omega.
  rewrite TPithdel_geq_comm with (i:=x) in H7; try omega; trivial.

  rewrite TPithdel_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_overflow with (i:=i) in H7; try omega.  
  rewrite TPithdel_lt_comm in H7; try omega.
  rewrite TPithdel_geq_comm with (i:=x) in H7; try omega; trivial.
  
  rewrite 2 TPith_TPithdel_lt in H6; try omega.
  apply equiv_AC with (i:=x); 
  repeat split~; simpl set_In; try omega; trivial;
  try rewrite 2 TPithdel_Fc_eq; try omega. autorewrite with tuples; trivial.
  
  apply H with (i:=i-1) (j:=j-1) (m:=TPlength (TPithdel 1 t 1 n) 1 n);
  try rewrite TPlength_TPithdel; try omega.
  autorewrite with tuples.
  
  case (le_dec i (TPlength t 1 n));
  case (le_dec j (TPlength t 1 n)); intros H9 H10.
  
  rewrite 2 TPith_TPithdel_geq; try omega.
  replace (i -1 + 1) with i; try omega.
  replace (j -1 + 1) with j; try omega; trivial.

  rewrite TPith_overflow with (i:=j-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPith_overflow with (i:=j) in H0; try omega.
  rewrite 2 TPith_TPithdel_geq; try omega.
  replace (i -1 + 1) with i; try omega.
  replace (TPlength t' 1 n -1 + 1) with (TPlength t' 1 n); try omega; trivial.

  rewrite TPith_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPith_overflow with (i:=i) in H0; try omega.
  rewrite 2 TPith_TPithdel_geq; try omega.
  replace (j -1 + 1) with j; try omega.
  replace (TPlength t 1 n -1 + 1) with (TPlength t 1 n); try omega; trivial.

  rewrite TPith_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPith_overflow with (i:=j-1);
  try rewrite TPlength_TPithdel; try omega.  
  rewrite TPith_overflow with (i:=i) in H0; try omega.
  rewrite TPith_overflow with (i:=j) in H0; try omega.
  rewrite 2 TPith_TPithdel_geq; try omega.
  replace (TPlength t' 1 n -1 + 1) with (TPlength t' 1 n); try omega; trivial.
  replace (TPlength t 1 n -1 + 1) with (TPlength t 1 n); try omega; trivial.
  
  case (TPlength t 1 n === 2); intro H10.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; 
  try rewrite TPlength_TPithdel; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPithdel_Fc_eq in H7;
  try rewrite TPlength_TPithdel; try omega.

  case (le_dec i (TPlength t 1 n));
  case (le_dec j (TPlength t 1 n)); intros H11 H12.
  
  rewrite TPithdel_lt_comm in H7; try omega.
  rewrite TPithdel_lt_comm with (i:=x) in H7; try omega; trivial.

  rewrite TPithdel_overflow with (i:=j-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_overflow with (i:=j) in H7; try omega.
  rewrite TPithdel_lt_comm in H7; try omega.
  rewrite TPithdel_lt_comm with (i:=x) in H7; try omega; trivial.

  rewrite TPithdel_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_overflow with (i:=i) in H7; try omega.
  rewrite TPithdel_lt_comm in H7; try omega.
  rewrite TPithdel_lt_comm with (i:=x) in H7; try omega; trivial.

  rewrite TPithdel_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPithdel_overflow with (i:=j-1);
  try rewrite TPlength_TPithdel; try omega.  
  rewrite TPithdel_overflow with (i:=i) in H7; try omega.
  rewrite TPithdel_overflow with (i:=j) in H7; try omega.
  rewrite TPithdel_lt_comm in H7; try omega.
  rewrite TPithdel_lt_comm with (i:=x) in H7; try omega; trivial.
Qed.




Lemma aac_equiv_trans : forall C t1 t2 t3,
 C |- t1 ~aac t2 -> C |- t2 ~aac t3 -> C |- t1 ~aac t3.
Proof.
 introv. gen_eq l : (size_term t1). gen t1 t2 t3.
 induction l using peano_induction; intros. 

 inverts H1; inverts H2; auto; simpl size_term in *|-; try omega; try contradiction.
 
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
 apply aac_equivariance; trivial. 
 apply aac_equiv_fresh with (a:=a) in H9; trivial.

 case (a ==at a'0); intro H1. rewrite H1. 
 simpl in H0. apply equiv_Ab_1.
 apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); try omega; trivial.
 apply aac_equiv_swap_inv_side. rewrite H1. trivial.

 assert (Q:  C |- a # t'0). 
  apply aac_equiv_fresh with (a:=a) in H9; trivial.
  apply fresh_lemma_1 in H9. simpl rev in H9. 
  rewrite swap_neither in H9; auto.
 apply equiv_Ab_2; trivial.
 assert (Q' : C |- t ~aac ((|[ (a, a')]) @ ((|[ (a', a'0)]) @ t'0))). 
  apply H with (t2 := ((|[ (a, a')]) @ t')) (m := size_term t); trivial. 
  simpl in H0. omega. apply aac_equivariance; trivial.
 apply aac_alpha_equiv_trans with 
 (t2 := ((|[ (a, a')]) @ ((|[ (a', a'0)]) @ t'0))); trivial. 
 apply alpha_equiv_trans with 
 (t2 := (|[ ((|[(a,a')]) $ a', (|[(a,a')]) $ a'0)]) @ ((|[ (a, a')]) @ t'0)). 
 apply alpha_equiv_pi_comm. rewrite swap_right. rewrite swap_neither; trivial.
 apply alpha_equiv_equivariance. apply alpha_equiv_swap_neither; trivial.

 apply equiv_Su; intros.
 case (In_ds_dec p p' a); intros. apply H3; trivial.
 apply H7. apply not_In_ds in H2. unfold In_ds in *|-*. 
 rewrite <- H2; trivial.

 apply equiv_A; simpl set_In; try omega.
 autorewrite with tuples in *|-*.
 apply H with (m:=size_term (TPith 1 t 0 n))
              (t2:=  TPith 1 t' 0 n); trivial.
 assert (Q: size_term (TPith 1 t 0 n) <= size_term t). auto. omega.
 assert (Q0: C |- Fc 0 n t ~aac Fc 0 n t'). 
  apply equiv_A; simpl set_In; try omega; trivial.
 assert (Q1: C |- Fc 0 n t' ~aac Fc 0 n t'0). 
  apply equiv_A; simpl set_In; try omega; trivial.
 apply aac_equiv_TPlength with (E:=0) (n:=n) in Q0. 
 apply aac_equiv_TPlength with (E:=0) (n:=n) in Q1.
 autorewrite with tuples in *|-.
 case (TPlength t 0 n === 1); intro H8.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega.
 apply H with (t2:=Fc 0 n (TPithdel 1 t' 0 n)) 
              (m:=size_term (Fc 0 n (TPithdel 1 t 0 n))); trivial.
 assert (Q2 : size_term (TPithdel 1 t 0 n) < size_term t). auto. 
 simpl. omega.

 assert (Q0: C |- Fc 1 n t ~aac Fc 1 n t'). 
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega; trivial.
 assert (Q1: C |- Fc 1 n t' ~aac Fc 1 n t'0). 
  apply equiv_AC with (i:=i0); repeat split~; simpl set_In; try omega; trivial.
 generalize Q1; intro Q2.
 apply aac_equiv_TPlength with (E:=1) (n:=n) in Q0. autorewrite with tuples in Q0.
 apply aac_equiv_TPlength with (E:=1) (n:=n) in Q1. autorewrite with tuples in Q1.
 apply aac_equiv_TPith_l' with (i:=i) (E:=1) (n:=n) in Q2;
 autorewrite with tuples; try omega.
 destruct Q2. destruct H1. 
 apply equiv_AC with (i:=x); try split~; simpl set_In; try omega;
 autorewrite with tuples in *|-*; trivial. 
 apply H with (t2:=TPith i t' 1 n) (m:=size_term (TPith 1 t 1 n)); trivial. 
 assert (Q2 : size_term (TPith 1 t 1 n) <= size_term t). auto. omega.
 case (TPlength t 1 n === 1); intro H12.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega. 
 apply H with (t2:=Fc 1 n (TPithdel i t' 1 n)) (m:=size_term (Fc 1 n (TPithdel 1 t 1 n))); trivial. 
 assert (Q2 : size_term (TPithdel 1 t 1 n) < size_term t). auto. 
 simpl. omega.
Qed. 

Lemma aac_equiv_sym : forall C t1 t2, C |- t1 ~aac t2 -> C |- t2 ~aac t1 .
Proof.
 intros. induction H; auto; try omega; trivial. 

 assert (Q0 : C |- t' ~aac ((|[(a', a)]) @ t)).
  apply aac_equiv_trans with (t2 := (|[(a, a')]) @ t).
  apply aac_equiv_trans with (t2 := (|[(a, a')]) @ ((|[(a, a')]) @ t')).
  apply aac_alpha_equiv_trans with (t2 := t'). apply aac_equiv_refl.
  apply alpha_equiv_swap_inv_side. apply alpha_equiv_refl.
  apply aac_equivariance; trivial.  apply aac_equiv_swap_comm. 
 assert (Q1 : C |- a # ((|[(a', a)]) @ t)).
  apply aac_equiv_fresh with (t1 := t'); trivial.
 apply fresh_lemma_1 in Q1. simpl rev in Q1. rewrite swap_right in Q1.
 apply equiv_Ab_2; trivial; auto.
 
 apply equiv_Su. intros. apply H. apply ds_sym. trivial.

 apply aac_equiv_AC with (i:=i) (j:=1); try omega; trivial.
Qed.

Lemma aac_equivalence : forall C, Equivalence (equiv (0::|[1]) C).
Proof.
  split~.
  unfold Symmetric; intros. apply aac_equiv_sym; trivial.
  unfold Transitive; intros. apply aac_equiv_trans with (t2:=y); trivial.
Qed.

Lemma a_equivalence : forall C, Equivalence (equiv (|[0]) C).
Proof.
  intros. apply subset_equivalence with (S2:=0::|[1]).
  unfold subset. simpl; intros. omega.
  unfold proper_equiv_Fc; intros. apply aac_equiv_Fc; trivial.
  apply aac_equivalence.
Qed.

Lemma ac_equivalence : forall C, Equivalence (equiv (|[1]) C).
Proof.
  intros. apply subset_equivalence with (S2:=0::|[1]).
  unfold subset. simpl; intros. omega.
  unfold proper_equiv_Fc; intros. apply aac_equiv_Fc; trivial.
  apply aac_equivalence.
Qed.