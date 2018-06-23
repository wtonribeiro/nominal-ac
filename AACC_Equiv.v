(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : AAAC_Equiv.v 
 Authors     : Washington Luis R. de Carvalho Segundo and
               Mauricio Ayala Rincon 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 3, 2017.
 ============================================================================
*)

Require Export Equiv_Tuples.


Lemma alpha_to_aacc_equiv : forall C t t', 
 C |- t ~alpha t' -> C |- t ~aacc t'.
Proof. 
 intros. induction H; auto; 
 simpl in H; try contradiction. 
 apply aacc_equiv_Fc; trivial.
Qed.

Hint Resolve alpha_to_aacc_equiv.


(** Some auxiliary lemmas about is_Pr *)

Lemma alpha_neg_is_Pr : forall C t t', C |- t ~alpha t' -> (~ is_Pr t <-> ~ is_Pr t').
Proof.
  intros. inverts H; simpl in *|-*; split~; intros; trivial.
Qed.

Lemma aacc_neg_is_Pr : forall C t t', C |- t ~aacc t' -> (~ is_Pr t <-> ~ is_Pr t').
Proof.
  intros. inverts H; simpl in *|-*; split~; intros; trivial.
Qed.

Lemma perm_neg_is_Pr : forall pi t, ~ is_Pr (pi @ t) <-> ~ is_Pr t.
Proof.
  intros. destruct t; autorewrite with perm; simpl; split~; intros; trivial. 
Qed.

(** Intermediate transitivity for aacc_equiv with alpha_equiv *)

Lemma aacc_alpha_equiv_trans : forall C t1 t3, 
  (exists t2, C |- t1 ~aacc t2 /\ C |- t2 ~alpha t3) <-> C |- t1 ~aacc t3.
Proof.
  intros. split~; intro.
  case H; clear H; intros t2 H. destruct H.

  (* -> *)
  
  gen t3 H0. induction H; intros; auto.
  inverts H1. apply equiv_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.
  inverts H1. apply equiv_Fc; auto. destruct H.
  left~. destruct H. right~. split~. destruct H1. left~.
  right~. apply alpha_neg_is_Pr in H7. apply H7; trivial.
  inverts H0. apply equiv_Ab_1; apply IHequiv; trivial.
  apply equiv_Ab_2; trivial. apply IHequiv; trivial.
  inverts H2. apply equiv_Ab_2; trivial.
  apply IHequiv. apply alpha_equiv_eq_equiv.
  apply alpha_equiv_eq_equiv; trivial.
  apply alpha_equiv_equivariance; trivial.
  apply alpha_equiv_fresh with (t1 := t'); trivial.
  case (a ==at a'0); intro H10. rewrite H10.
  apply equiv_Ab_1. apply IHequiv. apply alpha_equiv_sym.
  replace ([(a, a')]) with (! ([(a, a')])). apply perm_inv_side.
  apply alpha_equiv_trans with (t2 := ([ (a', a)]) @ t'0).
  apply alpha_equiv_pi. intros b H11. false. apply H11. apply swap_comm.
  apply alpha_equiv_sym. rewrite H10; trivial. simpl; trivial.
  assert (Q : C |- a # t'0).
   apply alpha_equiv_fresh with (a := a) in H7; trivial.
   apply fresh_lemma_1 in H7. simpl rev in H7. 
   rewrite swap_neither in H7; auto.
  apply equiv_Ab_2; trivial. apply IHequiv.
  replace ([(a, a')]) with (!([(a, a')])). 
  apply perm_inv_side'. simpl.
  apply alpha_equiv_trans with (t2 := ([ (a', a'0)]) @ t'0); trivial.
  apply alpha_equiv_trans with 
  (t2 := ([ ([(a, a')] $ a, [(a, a')] $ a'0)]) @ (([ (a, a')]) @ t'0)); trivial.
  rewrite swap_left. rewrite swap_neither; auto.
  apply alpha_equiv_equivariance. apply alpha_equiv_sym. 
  apply alpha_equiv_swap_neither; trivial. apply alpha_equiv_sym. 
  apply alpha_equiv_pi_comm. simpl; trivial.

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
  assert (Q : C |- Fc 0 n t ~aacc Fc 0 n t').
   apply equiv_A; simpl set_In; try omega; trivial.              
  apply alpha_equiv_TPlength with (E:=0) (n:=n) in H8'.
  apply aacc_equiv_TPlength with (E:=0) (n:=n) in Q.
  autorewrite with tuples in Q.
  case (eq_nat_dec (TPlength t 0 n) 1); intro H9.
  rewrite 2 TPithdel_TPlength_1;
  autorewrite with tuples; try omega; auto.
  apply IHequiv2.
  rewrite 2 TPithdel_Fc_eq; autorewrite with tuples; try omega.
  apply alpha_equiv_Fc. apply alpha_equiv_TPithdel; trivial.

  inverts H2. generalize H8; intro H8'.
  assert (Q : C |- Fc 1 n t ~aacc Fc 1 n t').
   apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega; trivial.              
  apply alpha_equiv_TPlength with (E:=1) (n:=n) in H8'.
  apply aacc_equiv_TPlength with (E:=1) (n:=n) in Q.
  autorewrite with tuples in Q.
  apply equiv_AC with (i:=i); simpl set_In; repeat split~; try omega.
  apply IHequiv1. apply alpha_equiv_TPith; auto.
  case (eq_nat_dec (TPlength t 1 n) 1); intro H9.
  rewrite 2 TPithdel_TPlength_1;
  autorewrite with tuples; try omega; auto.
  apply IHequiv2.
  rewrite 2 TPithdel_Fc_eq; autorewrite with tuples; try omega.
  apply alpha_equiv_Fc. apply alpha_equiv_TPithdel; trivial.
 
  inverts H2. inverts H8.
  apply IHequiv1 in H5.
  apply IHequiv2 in H7.
  apply equiv_C1; trivial.

  inverts H2. inverts H8.
  apply IHequiv1 in H7.
  apply IHequiv2 in H5.
  apply equiv_C2; trivial.

  (* <- *)

  induction H.
  exists (<<>>). split~.
  exists (%a). split~.
  case IHequiv1; clear IHequiv1; intros t1'' IH1.
  case IHequiv2; clear IHequiv2; intros t2'' IH2.
  destruct IH1. destruct IH2. exists (<|t1'',t2''|>). split~.
  case IHequiv; clear IHequiv; intros t'' H1. destruct H1.
  exists (Fc E n t''). split~. apply equiv_Fc; trivial.
  destruct H. left~. right~. destruct H. split~.
  destruct H3. left~. left~. apply aacc_neg_is_Pr in H0. apply H0; trivial.
  case IHequiv; clear IHequiv; intros t'' H0. destruct H0.
  exists ([a]^t''). split~.
  case IHequiv; clear IHequiv; intros t'' H2. destruct H2.
  exists ([a]^t''). split~.
  exists (p|.X). split~. apply equiv_Su; intros. false.
  case IHequiv1; clear IHequiv1; intros t3 H2.
  case IHequiv2; clear IHequiv2; intros t4 H3.
  destruct H2. destruct H3.
  assert (Q : C |- Fc 0 n t ~aacc Fc 0 n t').
   apply equiv_A; trivial.
  exists (Fc 0 n t'). split~. apply alpha_equiv_refl.
  assert (Q : C |- Fc 1 n t ~aacc Fc 1 n t').
   apply equiv_AC with (i:=i); trivial.
  exists (Fc 1 n t'). split~. apply alpha_equiv_refl.  
  assert (Q : C |- Fc 2 n (<| s0, s1 |>) ~aacc Fc 2 n (<| t0, t1 |>)).
   apply equiv_C1; trivial.
  exists (Fc 2 n (<| t0, t1 |>)). split~. apply alpha_equiv_refl.
  assert (Q : C |- Fc 2 n (<| s0, s1 |>) ~aacc Fc 2 n (<| t0, t1 |>)).
   apply equiv_C2; trivial.
  exists (Fc 2 n (<| t0, t1 |>)). split~. apply alpha_equiv_refl.
  
Qed.


(** Equivariance of aacc_equiv *)

Lemma aacc_equivariance : forall C t1 t2 pi,  
 C |- t1 ~aacc t2 -> C |- (pi @ t1) ~aacc (pi @ t2).
Proof.
 intros. induction H; intros;
         autorewrite with perm; auto.

 destruct H. apply equiv_Fc; trivial.
 left~. destruct H. apply equiv_Fc; trivial.
 right~; intros. split~; intros.
 destruct H1; [left~ | right~]; apply perm_neg_is_Pr; trivial.
 
 apply equiv_Ab_2. apply perm_diff_atom; trivial.
 apply aacc_alpha_equiv_trans.
 exists (pi @ (([(a, a')]) @ t')). split~.
 apply alpha_equiv_pi_comm.
 apply fresh_lemma_3; trivial.

 apply equiv_Su. intros. apply H. intro. apply H0.
 rewrite <- 2 perm_comp_atom. rewrite H1; trivial. 
 apply equiv_A; simpl set_In;
 autorewrite with tuples in *|-*; try omega.
 rewrite <- 2 Perm_TPith; trivial.
 assert (Q : C |- Fc 0 n t ~aacc Fc 0 n t').
  apply equiv_A; simpl set_In; try omega; autorewrite with tuples; trivial.              
 apply aacc_equiv_TPlength with (E:=0) (n:=n) in Q.
 autorewrite with tuples in Q. 
 case (eq_nat_dec (TPlength t 0 n) 1); intro H2.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega.
 autorewrite with perm in IHequiv2.
 rewrite 2 Perm_TPithdel in IHequiv2; trivial.


 apply equiv_AC with (i:=i); repeat split~; simpl set_In;
 autorewrite with tuples in *|-*; try omega.
 rewrite <- 2 Perm_TPith; trivial.
 assert (Q : C |- Fc 1 n t ~aacc Fc 1 n t').
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega;
  autorewrite with tuples; trivial.              
 apply aacc_equiv_TPlength with (E:=1) (n:=n) in Q.
 autorewrite with tuples in Q.
 case (eq_nat_dec (TPlength t 1 n) 1); intro H4.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega.
 autorewrite with perm in IHequiv2.
 rewrite 2 Perm_TPithdel in IHequiv2; trivial.
Qed.


(** A corollary about the swapping inversion of side in aacc_equiv *) 

Lemma aacc_equiv_swap_inv_side : forall C a a' t t', 
 C |- t ~aacc (([ (a, a')]) @ t') -> C |- (([ (a', a)]) @ t) ~aacc t'. 
Proof.
 intros. 
 apply aacc_alpha_equiv_trans.
 exists (([ (a', a)]) @ (([ (a, a')]) @ t')). split~.
 apply aacc_equivariance; trivial.
 apply perm_inv_side'. simpl.
 apply alpha_equiv_pi. intros b H11. false. apply H11. apply swap_comm.
Qed.

(** Freshness preservation under aacc_equiv *) 

Lemma aacc_equiv_fresh : forall C a t1 t2,
                          C |- t1 ~aacc t2 ->
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
 assert (Q : C |- a # (([(a0, a')]) @ t')).  apply IHequiv; trivial.
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
 assert (Q : C |- Fc 0 n t ~aacc Fc 0 n t').
  apply equiv_A; simpl set_In; try omega; trivial.              
 apply aacc_equiv_TPlength with (E:=0) (n:=n) in Q.
 autorewrite with tuples in Q. 
 case (eq_nat_dec (TPlength t 0 n) 1); intro H4.
 rewrite TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-; autorewrite with tuples; try omega.
 apply fresh_Fc_elim with (E:=0) (n:=n).
 apply IHequiv2. apply fresh_Fc; trivial.

 apply fresh_Fc. apply fresh_Fc_elim in H0.
 apply fresh_TPith_TPithdel with (i:=i) (E:=1) (n:=n).
 apply fresh_TPith_TPithdel with (i:=1) (E:=1) (n:=n) in H0.
 destruct H0. split~. autorewrite with tuples in *|-. auto.
 assert (Q : C |- Fc 1 n t ~aacc Fc 1 n t').
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega; trivial.              
 apply aacc_equiv_TPlength with (E:=1) (n:=n) in Q.
 autorewrite with tuples in Q.
 case (eq_nat_dec (TPlength t 1 n) 1); intro H7.
 rewrite TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-; autorewrite with tuples; try omega.
 apply fresh_Fc_elim with (E:=1) (n:=n).
 apply IHequiv2. apply fresh_Fc; trivial. 

 apply fresh_Fc. apply fresh_Fc_elim in H0.
 apply fresh_Pr_elim in H0. destruct H0.
 apply fresh_Pr; [apply IHequiv1 | apply IHequiv2]; trivial. 

 apply fresh_Fc. apply fresh_Fc_elim in H0.
 apply fresh_Pr_elim in H0. destruct H0.
 apply fresh_Pr; [apply IHequiv2 | apply IHequiv1]; trivial. 

Qed.


(** Reflexivity of aacc_equiv *)
  
Lemma aacc_equiv_refl : forall C t, C |- t ~aacc t.
Proof.
  intros. induction t; auto.
  apply aacc_equiv_Fc; trivial.
  apply equiv_Su; intros. false.
Qed.

Hint Resolve aacc_equiv_refl.


(** A Corollary: the order of the atoms inside a swapping doesn't matter in aacc_equiv *)

Corollary aacc_equiv_swap_comm : forall C t a a', 
  C |- ([ (a, a')]) @ t ~aacc (([ (a', a)]) @ t) .
Proof.
 intros. apply aacc_alpha_equiv_trans. 
 exists (([ (a, a')]) @ t). split~.
 apply alpha_equiv_pi. intros b H11. false. apply H11. apply swap_comm.
Qed.


(** Combination of AC arguments *)

Lemma aacc_equiv_TPith_l : forall C t t' i E n, C |- t ~aacc t' -> 
                         i > 0 -> i <= TPlength t E n ->
               exists j, j > 0 /\ j <= TPlength t' E n /\
                         C |- TPith i t E n ~aacc TPith j t' E n /\ 
                         C |- TPithdel i t E n ~aacc TPithdel j t' E n.
Proof.
  intros. gen_eq l : (term_size t).
  intro H2. gen i t t' H2 H0 H1. induction l using peano_induction; intros.
  destruct H0.
  
  exists 1. simpl. repeat split~; try omega; auto.
  exists 1. simpl. repeat split~; try omega; auto.
 
  simpl in H2. generalize H0_ H0_0. intros H0' H0_0'.
  apply aacc_equiv_TPlength with (E:=E) (n:=n) in H0'.
  apply aacc_equiv_TPlength with (E:=E) (n:=n) in H0_0'.
  assert (Q:TPlength t1 E n >= 1 /\ TPlength t2 E n >= 1). auto. destruct Q.
  case (le_dec i (TPlength t1 E n)); intro H5.
  case H with (m:=term_size t1) (i:=i) (t:=t1) (t':=t1'); try omega; trivial; clear H.
  intros j H6. destruct H6. destruct H6. destruct H7. exists j.
  rewrite 2 TPith_Pr_le; try omega. 
  case (eq_nat_dec (TPlength t1 E n) 1); intro H9.
  rewrite 2 TPithdel_t1_Pr; try omega. simpl.
  repeat split~; try omega; trivial.
  rewrite 2 TPithdel_Pr_le; try omega.
  simpl; repeat split~; try omega; auto.
  case H with (m:=term_size t2)
              (i:=i - TPlength t1 E n) (t:=t2) (t':=t2'); try omega; trivial; clear H.
  simpl in H3. omega.
  intros j H6. destruct H6. destruct H6. destruct H7. exists (TPlength t1 E n + j).
  rewrite 2 TPith_Pr_gt; try omega. rewrite <- H0'.
  replace (TPlength t1 E n + j - TPlength t1 E n) with j; try omega. 
  case (eq_nat_dec (TPlength t2 E n) 1); intro H9.
  rewrite 2 TPithdel_t2_Pr; try omega.
  repeat split~; try omega; trivial. simpl; omega.
  rewrite 2 TPithdel_Pr_gt; try omega.
  replace (TPlength t1 E n + j - TPlength t1' E n) with j; try omega.
  simpl; repeat split~; try omega; auto.

  case ((E0,n0) ==np (E,n)); intro H5. inverts H5.
  generalize H4; intro H4'.
  apply aacc_equiv_TPlength with (E:=E) (n:=n) in H4'.
  case (eq_nat_dec (TPlength t E n) 1); intro H5. exists 1.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
  assert (i=1). autorewrite with tuples in H3. omega. rewrite H6 in *|-*.
  repeat split~; try omega; trivial.
  apply aacc_equiv_TPith_l1 with (E:=E) (n:=n) in H4.
  destruct H4. destruct H4. destruct H7. destruct H8.
  assert (x = 1). omega. rewrite H10 in H8; trivial.  
  destruct H0. exists i.
  autorewrite with tuples in *|-*.
  generalize H4; intro H4''.
  apply aacc_equiv_TPith_E_diff_1_2 with (i:=i) (E:=E) (n:=n) in H4. destruct H4.
  rewrite 2 TPithdel_Fc_eq; try omega.
  repeat split~; try omega; trivial.
  simpl in *|-*. omega.
  destruct H0. rewrite H0 in *|-*.
  autorewrite with tuples in H3. simpl in H2.
  case H with (m := term_size t) (i := i) (t := t) (t' := t'); try omega; trivial.
  intros j Hj. exists j. autorewrite with tuples.
  rewrite 2 TPithdel_Fc_eq; try omega.
  destruct Hj. destruct H8. destruct H9. repeat split~.
  apply equiv_Fc_c; trivial.
  exists 1. rewrite TPlength_Fc_diff in *|-*; trivial.
  rewrite 2 TPith_Fc_diff; trivial.
  rewrite 2 TPithdel_Fc_diff; trivial.
  repeat split~; try omega; auto.
  
  exists 1. simpl. repeat split~; try omega; auto.
  exists 1. simpl. repeat split~; try omega; auto.
  exists 1. simpl. repeat split~; try omega; auto.
  
  clear H0. case (set_In_dec eq_nat_dec E (1::([2]))); intro H4.
  exists 1. assert (Q:(0,n0) <> (E,n)). intro. inverts H0.
  simpl in H4. omega.
  rewrite TPlength_Fc_diff in *|-*; trivial.
  rewrite 2 TPith_Fc_diff; trivial.
  rewrite 2 TPithdel_Fc_diff; trivial.
  repeat split~; try omega; auto. 
  apply equiv_A; simpl set_In; try omega; trivial.
  exists i. split~; auto.
  assert (Q: C |- Fc 0 n0 t ~aacc Fc 0 n0 t').
   apply equiv_A; simpl set_In; try omega; trivial.
  generalize Q; intro Q'. apply aacc_equiv_TPlength with (E:=E) (n:=n) in Q'.
  apply aacc_equiv_TPith_E_diff_1_2 with (E:=E) (n:=n) (i:=i) in Q; trivial.
  destruct Q. repeat split~; try omega; trivial.

  clear H0. case ((1,n0) ==np (E,n)); intro H4. inverts H4.
  autorewrite with tuples in *|-*.  
  
  case (eq_nat_dec i 1); intro H4. rewrite H4.
  case (le_dec i0 1); intro H5.
  exists 1. case (eq_nat_dec i0 0); intro H6; repeat rewrite H6 in *|-;
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
  
  assert (Q0 : C |- Fc 1 n t ~aacc Fc 1 n t').
   apply equiv_AC with (i:=i0); repeat split~; simpl set_In;
   autorewrite with tuples; try omega; trivial.              
  apply aacc_equiv_TPlength with (E:=1) (n:=n) in Q0.
  autorewrite with tuples in Q0. 
  assert (Q: TPlength t 1 n >=1). auto.
  case (eq_nat_dec (TPlength t 1 n) 1); intro H5; try omega.
  rewrite 2 TPithdel_Fc_eq in H0_0; try omega. 
  
  case H with (m  := term_size (Fc 1 n (TPithdel 1 t 1 n))) (i := i-1)
              (t  := Fc 1 n (TPithdel 1 t 1 n))
              (t' := Fc 1 n (TPithdel i0 t' 1 n));
              autorewrite with tuples;
              try rewrite TPlength_TPithdel; try omega; trivial; clear H.
     
  simpl. simpl in H2.
  assert (Q1: term_size (TPithdel 1 t 1 n) < term_size t).
   apply term_size_TPithdel; trivial. omega.
  intros j Hj. destruct Hj. destruct H0 . destruct H6.  
  autorewrite with tuples in H6.
  apply aacc_equiv_TPlength with (E:=1) (n:=n) in H0_0.
  autorewrite with tuples in H0_0.
  rewrite 2 TPlength_TPithdel in H0_0; try omega.

  case (le_dec i0 j); intro H8.
 
  exists (j + 1). autorewrite with tuples.
  rewrite 2 TPith_TPithdel_geq in H6; try omega.
  replace (i - 1 + 1) with i in *|-; try omega.
  rewrite 2 TPithdel_Fc_eq; try omega. 
  repeat split~; try omega; trivial.
  case (eq_nat_dec i0 0); intro H9. rewrite H9 in *|-.
  rewrite TPith_0 in H0_. rewrite TPithdel_0 in H7.
  
  apply equiv_AC with (i:=1); simpl set_In;
  repeat split~; try rewrite TPlength_TPithdel; try omega; trivial. 
  autorewrite with tuples. 
  rewrite 2 TPith_TPithdel_lt; try omega; trivial.
  case (eq_nat_dec (TPlength t 1 n) 2); intro H10.
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
  case (eq_nat_dec (TPlength t 1 n) 2); intro H10.
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
  case (eq_nat_dec (TPlength t 1 n) 2); intro H10.
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
  case (eq_nat_dec (TPlength t 1 n) 2); intro H10.
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

  simpl in H2. clear H0. case ((2,n0) ==np (E,n)); intro H4.
  inverts H4. autorewrite with tuples in H3|-*. simpl in H3.
  case H with (m := term_size (<|s0,s1|>)) (i:=i) (t:=<| s0, s1 |>) (t':=<| t0, t1 |>);
    simpl TPlength; simpl term_size; try omega.
  apply equiv_Pr; trivial. intros j Hj. exists j. autorewrite with tuples.
  rewrite 2 TPithdel_Fc_eq. destruct Hj. destruct H4. destruct H5.
  repeat split~. apply equiv_Fc_c; trivial.
  assert (Q: TPlength t0 2 n >=1 /\ TPlength t1 2 n >=1). split~. simpl. omega.
  assert (Q: TPlength s0 2 n >=1 /\ TPlength s1 2 n >=1). split~. simpl. omega.
  exists 1. rewrite TPlength_Fc_diff in *|-*; trivial.
  assert (i=1). omega. rewrite H0. rewrite 2 TPith_Fc_diff; trivial.
  rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff; trivial.
  repeat split~. apply equiv_C1; trivial. simpl. right~.

  simpl in H2. clear H0. case ((2,n0) ==np (E,n)); intro H4.
  inverts H4. autorewrite with tuples in H3. simpl in H3.
 
  generalize H0_ H0_0. intros H' H''.
  apply aacc_equiv_TPlength with (E:=2) (n:=n) in H'.
  apply aacc_equiv_TPlength with (E:=2) (n:=n) in H''.
  assert (Q: TPlength s0 2 n >=1 /\ TPlength s1 2 n >=1). split~. 

  case (le_dec i (TPlength s0 2 n)); intro H7.

  case H with (m := term_size (<|s0,s1|>)) (i:=TPlength s1 2 n + i) (t:=<| s1, s0 |>) (t':=<| t0, t1 |>);
    simpl term_size; try omega; clear H.
  apply equiv_Pr; trivial.
  simpl; omega. intros j Hj. destruct Hj. destruct H0. destruct H4.
  exists j. autorewrite with tuples.
  
  rewrite 2 TPithdel_Fc_eq; simpl TPlength; try omega.
  case (le_dec j (TPlength t0 2 n)); intro H8.
  repeat split~; try omega. 
  rewrite 2 TPith_Pr_le; trivial.
  rewrite TPith_Pr_gt in H4; try omega. rewrite TPith_Pr_le in H4; trivial.
  replace (TPlength s1 2 n + i - TPlength s1 2 n) with i in H4;try omega; trivial.
  case (eq_nat_dec (TPlength s0 2 n) 1); intro H9.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPithdel_t2_Pr in H5; try omega.
  apply equiv_Fc_c; trivial.
  rewrite TPithdel_Pr_le; trivial.
  rewrite TPithdel_Pr_gt in H5; try omega.
  replace (TPlength s1 2 n + i - TPlength s1 2 n) with i in H5; try omega.
  case (eq_nat_dec (TPlength t0 2 n) 1); intro H10.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPithdel_t1_Pr in H5; try omega. inverts H5.
  apply equiv_C2; trivial. simpl; right~.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPithdel_Pr_le in H5; try omega. inverts H5.
  apply equiv_C2; trivial. simpl; right~.

  repeat split~; try omega. 
  rewrite TPith_Pr_le; trivial.
  rewrite TPith_Pr_gt; try omega.
  rewrite TPith_Pr_gt in H4; try omega. rewrite TPith_Pr_gt in H4; try omega.
  replace (TPlength s1 2 n + i - TPlength s1 2 n) with i in H4;try omega; trivial.
  case (eq_nat_dec (TPlength s0 2 n) 1); intro H9.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPithdel_t2_Pr in H5; try omega.
  apply equiv_Fc_c; trivial.
  rewrite TPithdel_Pr_le; trivial.
  rewrite TPithdel_Pr_gt in H5; try omega.
  replace (TPlength s1 2 n + i - TPlength s1 2 n) with i in H5; try omega.
  case (eq_nat_dec (TPlength t1 2 n) 1); intro H10.
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite TPithdel_Pr_gt in H5; try omega. inverts H5.
  apply equiv_C2; trivial. simpl; right~.


  case H with (m := term_size (<|s0,s1|>)) (i:=i - TPlength s0 2 n) (t:=<| s1, s0 |>) (t':=<| t0, t1 |>);
    simpl term_size; try omega; clear H.
  apply equiv_Pr; trivial.
  simpl; omega. intros j Hj. destruct Hj. destruct H0. destruct H4.
  exists j. autorewrite with tuples.
  
  rewrite 2 TPithdel_Fc_eq; simpl TPlength; try omega.
  case (le_dec j (TPlength t0 2 n)); intro H8.
  repeat split~; try omega. 
  rewrite TPith_Pr_gt; try omega.
  rewrite TPith_Pr_le; try omega.
  rewrite 2 TPith_Pr_le in H4; try omega; trivial.
   case (eq_nat_dec (TPlength s1 2 n) 1); intro H9.
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPithdel_t1_Pr in H5; try omega.
  apply equiv_Fc_c; trivial.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite TPithdel_Pr_le in H5; try omega.
  case (eq_nat_dec (TPlength t0 2 n) 1); intro H10.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPithdel_Pr_le; try omega.
  rewrite TPithdel_Pr_le in H5; try omega. inverts H5.
  apply equiv_C2; trivial. simpl; right~.

  repeat split~; try omega. 
  rewrite 2 TPith_Pr_gt; try omega.
  rewrite TPith_Pr_le in H4; try omega. rewrite TPith_Pr_gt in H4; try omega; trivial.
   case (eq_nat_dec (TPlength s1 2 n) 1); intro H9.
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPithdel_t1_Pr in H5; try omega.
  apply equiv_Fc_c; trivial.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite TPithdel_Pr_le in H5; try omega.
   case (eq_nat_dec (TPlength t1 2 n) 1); intro H10.
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPithdel_t2_Pr in H5; try omega. inverts H5.
  apply equiv_C2; trivial. simpl; right~.
  rewrite TPithdel_Pr_gt; try omega.
  rewrite TPithdel_Pr_gt in H5; try omega. inverts H5.
  apply equiv_C2; trivial. simpl. right~.
  
  exists 1. rewrite TPlength_Fc_diff in *|-*; trivial.
  assert (i=1). omega. rewrite H0. rewrite 2 TPith_Fc_diff; trivial.
  rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff; trivial.
  repeat split~. apply equiv_C2; trivial. simpl. right~.
  
Qed.

Lemma aacc_equiv_TPith_l' : forall C t t' E n,  C |- t ~aacc t' -> 
                           forall i, exists j, C |- TPith i t E n ~aacc TPith j t' E n /\ 
                                               C |- TPithdel i t E n ~aacc TPithdel j t' E n.
Proof.
  intros. case (eq_nat_dec i 0); intro H0.
  rewrite H0. rewrite TPith_0. rewrite TPithdel_0.
  apply aacc_equiv_TPith_l with (i:=1) (E:=E) (n:=n) in H; try omega; auto.
  destruct H. destruct H. destruct H1. destruct H2.
  exists x. split~.
  case (le_dec i (TPlength t E n)); intro H1.
  apply aacc_equiv_TPith_l with (i:=i) (E:=E) (n:=n) in H; try omega.
  destruct H. destruct H. destruct H2. destruct H3.
  exists x. split~. 
  rewrite TPith_overflow; try omega.
  rewrite TPithdel_overflow; try omega.
  apply aacc_equiv_TPith_l with (i:=TPlength t E n) (E:=E) (n:=n) in H; try omega; auto.
  destruct H. destruct H. destruct H2. destruct H3.
  exists x. split~.
Qed.
  


(** Transitivity of aacc_equiv *)

Lemma aacc_equiv_trans : forall C t1 t2 t3,
 C |- t1 ~aacc t2 -> C |- t2 ~aacc t3 -> C |- t1 ~aacc t3.
Proof.
 introv. gen_eq l : (term_size t1). gen t1 t2 t3.
 induction l using peano_induction; intros. 

 inverts H1; inverts H2; auto; simpl term_size in *|-; try omega; try contradiction.
 
 simpl in H0. apply equiv_Pr. 
 apply H with (t2 := t1') (m := term_size t0); try omega; trivial.
 apply H with (t2 := t2') (m := term_size t4); try omega; trivial. 

 simpl in H0. apply equiv_Fc; trivial.
 destruct H3. left~. destruct H1. right~. split~.
 destruct H2. left~. right~. apply aacc_neg_is_Pr in H10.
 apply H10; trivial.
 
 apply H with (t2 := t') (m := term_size t); try omega; trivial.

 false. destruct H3. apply H1. simpl. left~.
 destruct H1. omega.
 false. destruct H3. apply H1. simpl. right~.
 destruct H1. omega.
 inverts H4. destruct H3; try contradiction.
 destruct H1. simpl in H2. false. destruct H2; apply H2; trivial.
 inverts H4. destruct H3; try contradiction.
 destruct H1. simpl in H2. false. destruct H2; apply H2; trivial. 

 apply equiv_Ab_1. 
 apply H with (t2 := t') (m := term_size t); try omega; trivial.
 simpl in H0. apply equiv_Ab_2; trivial.
 apply H with (t2 := t') (m := term_size t); try omega; trivial. 
 simpl in H0. apply equiv_Ab_2; trivial.
 apply H with (t2 := (([ (a, a')]) @ t')) (m := term_size t); try omega; trivial.
 apply aacc_equivariance; trivial. 
 apply aacc_equiv_fresh with (a:=a) in H9; trivial.

 case (a ==at a'0); intro H1. rewrite H1. 
 simpl in H0. apply equiv_Ab_1.
 apply H with (t2 := (([ (a, a')]) @ t')) (m := term_size t); try omega; trivial.
 apply aacc_equiv_swap_inv_side. rewrite H1. trivial.

 assert (Q:  C |- a # t'0). 
  apply aacc_equiv_fresh with (a:=a) in H9; trivial.
  apply fresh_lemma_1 in H9. simpl rev in H9. 
  rewrite swap_neither in H9; auto.
 apply equiv_Ab_2; trivial.
 assert (Q' : C |- t ~aacc (([ (a, a')]) @ (([ (a', a'0)]) @ t'0))). 
  apply H with (t2 := (([ (a, a')]) @ t')) (m := term_size t); trivial. 
  simpl in H0. omega. apply aacc_equivariance; trivial.
 apply aacc_alpha_equiv_trans.
 exists ((([ (a, a')]) @ (([ (a', a'0)]) @ t'0))); split~. 
 apply alpha_equiv_trans with 
 (t2 := ([ (([(a,a')]) $ a', ([(a,a')]) $ a'0)]) @ (([ (a, a')]) @ t'0)). 
 apply alpha_equiv_pi_comm. rewrite swap_right. rewrite swap_neither; trivial.
 apply alpha_equiv_equivariance. apply alpha_equiv_swap_neither; trivial.

 apply equiv_Su; intros.
 case (In_ds_dec p p' a); intros. apply H3; trivial.
 apply H7. apply not_In_ds in H2. unfold In_ds in *|-*. 
 rewrite <- H2; trivial.

 false. destruct H10. apply H1. simpl. left~.
 destruct H1. omega.
 
 apply equiv_A; simpl set_In; try omega.
 autorewrite with tuples in *|-*.
 apply H with (m:=term_size (TPith 1 t 0 n))
              (t2:=  TPith 1 t' 0 n); trivial.
 assert (Q: term_size (TPith 1 t 0 n) <= term_size t). auto. omega.
 assert (Q0: C |- Fc 0 n t ~aacc Fc 0 n t'). 
  apply equiv_A; simpl set_In; try omega; trivial.
 assert (Q1: C |- Fc 0 n t' ~aacc Fc 0 n t'0). 
  apply equiv_A; simpl set_In; try omega; trivial.
 apply aacc_equiv_TPlength with (E:=0) (n:=n) in Q0. 
 apply aacc_equiv_TPlength with (E:=0) (n:=n) in Q1.
 autorewrite with tuples in *|-.
 case (eq_nat_dec (TPlength t 0 n) 1); intro H8.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega.
 apply H with (t2:=Fc 0 n (TPithdel 1 t' 0 n)) 
              (m:=term_size (Fc 0 n (TPithdel 1 t 0 n))); trivial.
 assert (Q2 : term_size (TPithdel 1 t 0 n) < term_size t). auto. 
 simpl. omega.

 false. destruct H10. apply H1. simpl. right~.
 destruct H1. omega.
 
 assert (Q0: C |- Fc 1 n t ~aacc Fc 1 n t'). 
  apply equiv_AC with (i:=i); repeat split~; simpl set_In; try omega; trivial.
 assert (Q1: C |- Fc 1 n t' ~aacc Fc 1 n t'0). 
  apply equiv_AC with (i:=i0); repeat split~; simpl set_In; try omega; trivial.
 generalize Q1; intro Q2.
 apply aacc_equiv_TPlength with (E:=1) (n:=n) in Q0. autorewrite with tuples in Q0.
 apply aacc_equiv_TPlength with (E:=1) (n:=n) in Q1. autorewrite with tuples in Q1.
 apply aacc_equiv_TPith_l' with (i:=i) (E:=1) (n:=n) in Q2;
 autorewrite with tuples; try omega.
 destruct Q2. destruct H1. 
 apply equiv_AC with (i:=x); try split~; simpl set_In; try omega;
 autorewrite with tuples in *|-*; trivial. 
 apply H with (t2:=TPith i t' 1 n) (m:=term_size (TPith 1 t 1 n)); trivial. 
 assert (Q2 : term_size (TPith 1 t 1 n) <= term_size t). auto. omega.
 case (eq_nat_dec (TPlength t 1 n) 1); intro H12.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples; try omega. 
 apply H with (t2:=Fc 1 n (TPithdel i t' 1 n)) (m:=term_size (Fc 1 n (TPithdel 1 t 1 n))); trivial. 
 assert (Q2 : term_size (TPithdel 1 t 1 n) < term_size t). auto. 
 simpl. omega.

 inverts H11. destruct H10; try contradiction.
 destruct H1. simpl in H2. false. destruct H2; apply H2; trivial.
 
 apply equiv_C1. simpl. right~.
  apply H with (t2 := t0) (m := term_size s0); try omega; trivial.
  apply H with (t2 := t4) (m := term_size s1); try omega; trivial.
  
 apply equiv_C2. simpl. right~.
  apply H with (t2 := t0) (m := term_size s0); try omega; trivial.
  apply H with (t2 := t4) (m := term_size s1); try omega; trivial.

 inverts H11. destruct H10; try contradiction.
 destruct H1. simpl in H2. false. destruct H2; apply H2; trivial.
 
 apply equiv_C2. simpl. right~.
  apply H with (t2 := t4) (m := term_size s0); try omega; trivial.
  apply H with (t2 := t0) (m := term_size s1); try omega; trivial.

 apply equiv_C1. simpl. right~.
  apply H with (t2 := t4) (m := term_size s0); try omega; trivial.
  apply H with (t2 := t0) (m := term_size s1); try omega; trivial.  
  
Qed. 


(** In AC choosing the ith element is arbitrary in both sides *)

Lemma aacc_equiv_AC : forall C t t' i j n,
      C |- TPith i (Fc 1 n t) 1 n ~aacc TPith j (Fc 1 n t') 1 n  ->
      C |- TPithdel i (Fc 1 n t) 1 n ~aacc TPithdel j (Fc 1 n t') 1 n ->
                           C |- Fc 1 n t ~aacc Fc 1 n t'.
Proof.
  intros. gen_eq l : (TPlength t 1 n); intro H1.
  gen t t' H1 i j. induction l using peano_induction; intros.
  case (eq_nat_dec i 1); intro Qi. rewrite Qi in *|-.
  apply equiv_AC with (i:=j); repeat split~; simpl set_In;
  try omega; trivial. 
  case (eq_nat_dec i 0); intro Qi'. rewrite Qi' in *|-.
  repeat rewrite TPith_0 in *|-; repeat rewrite TPithdel_0 in *|-.
  apply equiv_AC with (i:=j); simpl set_In; try omega; trivial.  
  
  case (eq_nat_dec (TPlength t 1 n) 1);
  case (eq_nat_dec (TPlength t' 1 n) 1); intros H3 H4.
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
  apply aacc_equiv_TPlength with (E:=1) (n:=n) in H2'.
  autorewrite with tuples in H2'.
  rewrite 2 TPlength_TPithdel in H2'; try omega; trivial.
  apply aacc_equiv_TPith_l1 with (E:=1) (n:=n) in H2.
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

  case (eq_nat_dec j 0); intro H10; try rewrite H10 in *|-*;
  repeat rewrite TPith_0 in *|-*;
  rewrite TPith_TPithdel_lt; try omega;
  replace (i -1 + 1) with i; try omega; trivial.
  rewrite TPith_overflow with (i:=i-1);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPith_overflow with (i:=i) in H0; try omega.
  rewrite TPith_TPithdel_geq; try omega.
  case (eq_nat_dec j 0); intro H10; try rewrite H10 in *|-*;
  repeat rewrite TPith_0 in *|-*;
  rewrite TPith_TPithdel_lt; try omega;
  replace (TPlength t 1 n -1 + 1) with (TPlength t 1 n); try omega; trivial.  
  
  case (eq_nat_dec (TPlength t 1 n) 2); intro H9.
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
  
  case (eq_nat_dec (TPlength t 1 n) 2); intro H10.
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

(** Symmetry of aacc_equiv *)

Lemma aacc_equiv_sym : forall C t1 t2, C |- t1 ~aacc t2 -> C |- t2 ~aacc t1 .
Proof.
 intros. induction H; auto; try omega; trivial. 
  
 apply equiv_Fc; trivial. destruct H.
 left~. right~. destruct H. split~.
 destruct H1. right~. left~. 
 
 assert (Q0 : C |- t' ~aacc (([(a', a)]) @ t)).
  apply aacc_equiv_trans with (t2 := ([(a, a')]) @ t).
  apply aacc_equiv_trans with (t2 := ([(a, a')]) @ (([(a, a')]) @ t')).
  apply aacc_alpha_equiv_trans. exists t'. split~.
  replace ([(a, a')]) with (!([(a, a')])).   
  apply perm_inv_side. apply alpha_equiv_refl. simpl; trivial.
  apply aacc_equivariance; trivial.  apply aacc_equiv_swap_comm. 
 assert (Q1 : C |- a # (([(a', a)]) @ t)).
  apply aacc_equiv_fresh with (t1 := t'); trivial.
 apply fresh_lemma_1 in Q1. simpl rev in Q1. rewrite swap_right in Q1.
 apply equiv_Ab_2; trivial; auto.
 
 apply equiv_Su. intros. apply H. apply ds_sym. trivial.

 apply aacc_equiv_AC with (i:=i) (j:=1); try omega; trivial.
Qed.

Lemma aacc_equiv_sub_context : forall C C' s t,
      sub_context C C' -> C |- s ~aacc t -> C' |- s ~aacc t.
Proof.
  intros. induction H0.
  apply equiv_Ut. apply equiv_At.
  apply equiv_Pr.
   apply IHequiv1; trivial.
   apply IHequiv2; trivial.
  apply aacc_equiv_Fc.
   apply IHequiv; trivial.
  apply equiv_Ab_1.  
   apply IHequiv; trivial.
  apply equiv_Ab_2; trivial.
   apply IHequiv; trivial.
  apply fresh_lemma_4 with (C:=C); trivial.
  apply equiv_Su; intros.
   unfold sub_context in H. 
   apply H. apply H0; trivial.
  apply equiv_A; trivial.
   apply IHequiv1; trivial.
   apply IHequiv2; trivial.  
  apply equiv_AC with (i:=i); trivial. 
   apply IHequiv1; trivial.
   apply IHequiv2; trivial.
  apply equiv_C1; trivial.
   apply IHequiv1; trivial.
   apply IHequiv2; trivial.
  apply equiv_C2; trivial.
   apply IHequiv1; trivial.
   apply IHequiv2; trivial.
Qed.
   
(** Soundness of aacc_equiv *)

Theorem aacc_equivalence : forall C, Equivalence (equiv (0::1::[2]) C).
Proof.
  split~.
  unfold Symmetric; intros. apply aacc_equiv_sym; trivial.
  unfold Transitive; intros. apply aacc_equiv_trans with (t2:=y); trivial.
Qed.

(** Soundness of a_equiv *)

Corollary a_equivalence : forall C, Equivalence (equiv ([0]) C).
Proof.
  intros. apply subset_equivalence with (S2:=0::1::[2]).
  unfold subset. simpl; intros. omega.
  unfold proper_equiv_Fc; intros. apply aacc_equiv_Fc; trivial.
  apply aacc_equivalence.
Qed.

(** Soundness of ac_equiv *)

Corollary ac_equivalence : forall C, Equivalence (equiv ([1]) C).
Proof.
  intros. apply subset_equivalence with (S2:=0::1::[2]).
  unfold subset. simpl; intros. omega.
  unfold proper_equiv_Fc; intros. apply aacc_equiv_Fc; trivial.
  apply aacc_equivalence.
Qed.

(** Soundness of c_equiv *)

Corollary c_equivalence : forall C, Equivalence (equiv ([2]) C).
Proof.
  intros. apply subset_equivalence with (S2:=0::1::[2]).
  unfold subset. simpl; intros. omega.
  unfold proper_equiv_Fc; intros. apply aacc_equiv_Fc; trivial.
  apply aacc_equivalence.
Qed.

(** Soundness of acc_equiv *)

Corollary acc_equivalence : forall C, Equivalence (equiv (1::[2]) C).
Proof.
  intros. apply subset_equivalence with (S2:=0::1::[2]).
  unfold subset. simpl; intros. omega.
  unfold proper_equiv_Fc; intros. apply aacc_equiv_Fc; trivial.
  apply aacc_equivalence.
Qed.


Corollary aacc_perm_inv_side : forall C pi s t, C |- (!pi) @ s ~aacc t -> C |- s ~aacc (pi @ t).
Proof.
  intros.
  apply aacc_equivariance with (pi:=pi) in H.
  apply aacc_equiv_trans with (t2:= pi @ ((!pi) @ s)); trivial.
  apply aacc_alpha_equiv_trans. exists s. split~.
  rewrite perm_comp. gen_eq g : (!pi); intro H0.
  replace pi with (!g). apply alpha_equiv_sym.
  apply alpha_equiv_perm_inv. rewrite H0.
  rewrite rev_involutive. trivial.
Qed.

Corollary aacc_perm_inv_side' : forall C pi s t, C |- s ~aacc (pi @ t) <-> C |- (!pi) @ s ~aacc t.
Proof.
  intros. split~; intro.
  apply aacc_equiv_sym.
  apply aacc_perm_inv_side.
  rewrite rev_involutive.
  apply aacc_equiv_sym. trivial.
  apply aacc_perm_inv_side; trivial.
Qed.  

                            