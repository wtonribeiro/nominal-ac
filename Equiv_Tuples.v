(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Equiv_Tuples.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 3, 2017.
 ============================================================================
 *)

Require Export Equiv.


Lemma aacc_equiv_TPlength : forall C t1 t2 E n, 
 C |- t1 ~aacc t2 -> TPlength t1 E n = TPlength t2 E n. 
Proof.
  intros. induction H; trivial. simpl; auto.

  case ((E0,n0) ==np (E,n)); intro H1. inverts H1.
  autorewrite with tuples; trivial.
  rewrite 2 TPlength_Fc_diff; trivial.

  case ((0,n0) ==np (E,n)); intro H2. inverts H2.
  autorewrite with tuples.  
  case (eq_nat_dec (TPlength t 0 n) 1); case (eq_nat_dec (TPlength t' 0 n) 1);
  intros H2 H3; try omega.   
  rewrite TPithdel_TPlength_1 in H1;
  autorewrite with tuples; try omega.
  rewrite TPithdel_Fc_eq in H1; try omega. inverts H1.
  rewrite TPithdel_Fc_eq in H1; try omega.
  rewrite TPithdel_TPlength_1 with (t:=Fc 0 n t') in H1;
  autorewrite with tuples; try omega. inverts H1.
  rewrite 2 TPithdel_Fc_eq in IHequiv2; try omega.
  autorewrite with tuples in IHequiv2;
  rewrite 2 TPlength_TPithdel in IHequiv2; try omega. 
  rewrite 2 TPlength_Fc_diff; trivial.

  case ((1,n0) ==np (E,n)); intro H2. inverts H2.
  autorewrite with tuples.  
  case (eq_nat_dec (TPlength t 1 n) 1); case (eq_nat_dec (TPlength t' 1 n) 1);
  intros H2 H3; try omega.   
  rewrite TPithdel_TPlength_1 in H1;
  autorewrite with tuples; try omega.
  rewrite TPithdel_Fc_eq in H1; try omega. inverts H1.
  rewrite TPithdel_Fc_eq in H1; try omega.
  rewrite TPithdel_TPlength_1 with (t:=Fc 1 n t') in H1;
  autorewrite with tuples; try omega. inverts H1.
  rewrite 2 TPithdel_Fc_eq in IHequiv2; try omega.
  autorewrite with tuples in IHequiv2;
  rewrite 2 TPlength_TPithdel in IHequiv2; try omega. 
  rewrite 2 TPlength_Fc_diff; trivial.

  case ((2,n0) ==np (E,n)); intro H2. inverts H2.
  autorewrite with tuples. simpl. omega.
  rewrite 2 TPlength_Fc_diff; trivial.

  case ((2,n0) ==np (E,n)); intro H2. inverts H2.
  autorewrite with tuples. simpl. omega.
  rewrite 2 TPlength_Fc_diff; trivial.
  
Qed.
  
Lemma aacc_equiv_TPith_l1 : forall C t t' E n, C |- t ~aacc t' ->
                         exists j, j > 0 /\ j <= TPlength t' E n /\ 
                         C |- TPith 1 t E n ~aacc TPith j t' E n /\ 
                         C |- TPithdel 1 t E n ~aacc TPithdel j t' E n.
Proof. 
 intros. induction H; intros.

 exists 1. simpl; split~. exists 1. simpl; split~.

 generalize H. intro H'. 
 apply aacc_equiv_TPlength with (E:=E) (n:=n) in H'.
 case IHequiv1; trivial. intros j Hj. clear IHequiv1 IHequiv2. 
 destruct Hj. destruct H2. destruct H3. exists j. 
 simpl TPlength. rewrite 2 TPith_Pr_le; try omega; auto.
 case (eq_nat_dec (TPlength t1' E n) 1); intro H5.  
 rewrite 2 TPithdel_t1_Pr; try omega. repeat split~; try omega; trivial.
 rewrite 2 TPithdel_Pr_le; try omega; trivial.
 repeat split~; try omega; auto.

 destruct IHequiv. destruct H1. destruct H2. destruct H3.
 generalize H0; intro H0'.
 apply aacc_equiv_TPlength with (E:=E) (n:=n) in H0.
 case ((E0,n0) ==np (E,n)); intro H5. inverts H5. exists x.
 autorewrite with tuples. repeat split~; trivial.
 case (eq_nat_dec (TPlength t E n) 1); intro H5.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq; try omega; auto.
 destruct H. apply equiv_Fc. left~. trivial.
 destruct H. apply equiv_Fc. destruct t; simpl in H5.
 false. false. false. false. 
 gen H5. case ((E, n) ==np (n0, n1)); intros H7 H8. inverts H7.
 rewrite <- H5 in *|-*. right~; split~; intros. 
 rewrite TPithdel_Fc_eq; trivial. intro H9. inverts H9.
 false. false. trivial.
 exists 1. rewrite TPlength_Fc_diff; trivial.
 rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff; trivial.
 repeat split~; auto.

 exists 1. simpl; split~. exists 1. simpl; split~.
 exists 1. simpl; split~.

 exists 1. clear IHequiv1 IHequiv2.
 case ((0,n0) ==np (E,n)); intro H2. inverts H2.
 autorewrite with tuples in *|-*. repeat split~; try omega; trivial.
 rewrite TPlength_Fc_diff; trivial. rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_Fc_diff; trivial. repeat split~; try omega; auto.

 case ((1,n0) ==np (E,n)); intro H2. inverts H2.
 case (eq_nat_dec i 0); intro H2.
 exists 1. rewrite H2 in *|-; rewrite TPith_0 in *|-; rewrite TPithdel_0 in *|-.
 autorewrite with tuples in *|-*. repeat split~; try omega; trivial.
 case (le_dec i (TPlength t' 1 n)); intro H3.
 exists i. autorewrite with tuples in *|-*. repeat split~; try omega; trivial.
 exists (TPlength t' 1 n).
 rewrite TPith_overflow with (i:=i) in H0; autorewrite with tuples in *|-*; try omega.
 rewrite TPithdel_overflow with (i:=i) in H1; autorewrite with tuples in * |-*; try omega.
 repeat split~; try omega; trivial.
 exists 1. rewrite TPlength_Fc_diff in *|-*; trivial. rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_Fc_diff; trivial. repeat split~; try omega; auto.
 apply equiv_AC with (i:=i); trivial.

 case ((2,n0) ==np (E,n)); intro H2. inverts H2.
 generalize H0. intro H'. 
 apply aacc_equiv_TPlength with (E:=2) (n:=n) in H'. 
 case IHequiv1; trivial. intros j Hj. clear IHequiv1 IHequiv2. 
 destruct Hj. destruct H3. destruct H4.
 exists j. autorewrite with tuples. simpl TPlength.
 rewrite 2 TPith_Pr_le; try omega; auto.
 rewrite 2 TPithdel_Fc_eq. repeat split~; try omega. 
 case (eq_nat_dec (TPlength s0 2 n) 1); intros H6. 
 assert (Q:j=1). omega. rewrite Q in *|-*; trivial.   
 rewrite 2 TPithdel_t1_Pr; try omega.
 apply equiv_Fc_c; trivial.
 rewrite 2 TPithdel_Pr_le; try omega. apply equiv_C1; trivial. 
 assert (Q0 : TPlength t1 2 n >= 1). auto. simpl; try omega.
 assert (Q1 : TPlength s1 2 n >= 1). auto. simpl; try omega.
 exists 1. rewrite TPlength_Fc_diff; trivial.
 rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_TPlength_1;
 try rewrite TPlength_Fc_diff; trivial.
 try omega. repeat split~.

 case ((2,n0) ==np (E,n)); intro H2. inverts H2.
 generalize H0. intro H'. 
 apply aacc_equiv_TPlength with (E:=2) (n:=n) in H'. 
 case IHequiv1; trivial. intros j Hj. clear IHequiv1 IHequiv2. 
 destruct Hj. destruct H3. destruct H4.
 exists (TPlength t0 2 n + j). autorewrite with tuples. simpl TPlength.
 rewrite TPith_Pr_le; try omega; auto.
 rewrite TPith_Pr_gt; try omega; auto.
 replace (TPlength t0 2 n + j - TPlength t0 2 n) with j; try omega.
 rewrite 2 TPithdel_Fc_eq. repeat split~; try omega. 
 case (eq_nat_dec (TPlength s0 2 n) 1); intros H6.
 assert (Q:j=1). omega. rewrite Q in *|-*; trivial.   
 rewrite TPithdel_t1_Pr; try omega.
 rewrite TPithdel_t2_Pr; try omega.
 apply equiv_Fc_c; trivial.
 rewrite TPithdel_Pr_le; try omega.
 rewrite TPithdel_Pr_gt; try omega.
 replace (TPlength t0 2 n + j - TPlength t0 2 n) with j; try omega.
 apply equiv_C2; trivial. 
 assert (Q0 : TPlength t0 2 n >= 1). auto. simpl; try omega.
 assert (Q1 : TPlength s1 2 n >= 1). auto. simpl; try omega. 
 exists 1. rewrite TPlength_Fc_diff; trivial.
 rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_TPlength_1;
 try rewrite TPlength_Fc_diff; trivial.
 try omega. repeat split~.

Qed.

 
Lemma aacc_equiv_TPith_E_diff_1_2 : forall C t t' i E n,
                 ~ set_In E (1::[2]) -> C |- t ~aacc t' -> 
                 (C |- TPith i t E n ~aacc TPith i t' E n /\
                  C |- TPithdel i t E n ~aacc TPithdel i t' E n).
Proof.
 intros. gen i. induction H0; intro.
 simpl; split~. simpl; split~. 

 generalize H0_ H0_0. intros H0' H0_0'.
 apply aacc_equiv_TPlength with (E:=E) (n:=n) in H0_.
 apply aacc_equiv_TPlength with (E:=E) (n:=n) in H0_0.

 case (le_dec i (TPlength t1 E n)); intro H1.
 rewrite 2 TPith_Pr_le; try omega. 
 case (eq_nat_dec (TPlength t1 E n) 1); intro H2.
 rewrite 2 TPithdel_t1_Pr; try omega. 
 split~; trivial. apply IHequiv1. 
 rewrite 2 TPithdel_Pr_le; try omega.
 split~. apply IHequiv1. apply equiv_Pr; trivial. apply IHequiv1.
 rewrite 2 TPith_Pr_gt; try omega. 
 case (eq_nat_dec (TPlength t2 E n) 1); intro H2.
 rewrite TPithdel_t2_Pr; try omega. rewrite H0_.
 rewrite TPithdel_t2_Pr; try omega. 
 split~; trivial. apply IHequiv2.
 rewrite 2 TPithdel_Pr_gt; try omega.
 rewrite H0_. split~. apply IHequiv2.
 apply equiv_Pr; trivial. apply IHequiv2.

 generalize H1; intro H1'.
 apply aacc_equiv_TPlength with (E:=E) (n:=n) in H1. 
 case ((E0,n0) ==np (E,n)); intro H2. inverts H2.
 autorewrite with tuples in *|-*.  split~. apply IHequiv.
 case (eq_nat_dec (TPlength t E n) 1); intro H2.
 rewrite 2 TPithdel_TPlength_1;
 autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq; try omega.
 apply equiv_Fc; trivial. destruct H0.
 left~. destruct H0.
 destruct t; simpl in H2.
 false. false. false. false. 
 gen H2. case ((E, n) ==np (n0, n1)); intros H4 H5. inverts H4.
 rewrite <- H2 in *|-*. right~; split~; intros. 
 rewrite TPithdel_Fc_eq; trivial. intro H6. inverts H6.
 false. false. apply IHequiv.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff; trivial.
 rewrite 2 TPith_Fc_diff; trivial. split~; auto.

 simpl; split~. simpl; split~. simpl; split~. 

 clear H0 IHequiv1.
 case ((0,n0) ==np (E,n)); intro H1. inverts H1. clear H.
 case (le_dec i 1); intro H2. case (eq_nat_dec i 0); intro H3; try rewrite H3;
 repeat rewrite TPith_0; repeat rewrite TPithdel_0. split~; trivial.
 assert (Qi:i=1). omega. rewrite Qi. split~; trivial.
 autorewrite with tuples in *|-*.
 assert (Q: C |- Fc 0 n t ~aacc Fc 0 n t').
  apply equiv_A; simpl set_In; try omega; autorewrite with tuples; trivial.
 apply aacc_equiv_TPlength with (E:=0) (n:=n) in Q.
 autorewrite with tuples in Q. case (eq_nat_dec (TPlength t 0 n) 1); intro H1.
 rewrite 2 TPithdel_TPlength_1;
 try rewrite 2 TPith_overflow with (i:=i);
 autorewrite with tuples; try omega. rewrite <- Q. rewrite H1; split~; trivial.

 rewrite 2 TPithdel_Fc_eq in *|-*; try omega.

 case (le_dec i (TPlength t 0 n)); intro H3. 
 
 assert (Q1: C |- TPith (i-1) (Fc 0 n (TPithdel 1 t 0 n)) 0 n ~aacc
                 TPith (i-1) (Fc 0 n (TPithdel 1 t' 0 n)) 0 n /\
            C |- TPithdel (i-1) (Fc 0 n (TPithdel 1 t 0 n)) 0 n ~aacc
                 TPithdel (i-1) (Fc 0 n (TPithdel 1 t' 0 n)) 0 n).
 apply IHequiv2. clear IHequiv2.
 destruct Q1. autorewrite with tuples in H.
 rewrite 2 TPith_TPithdel_geq in H; try omega.
 replace (i - 1 + 1) with i in H; try omega; trivial.
 split~; trivial. apply equiv_A; simpl set_In; try omega.
 autorewrite with tuples. rewrite 2 TPith_TPithdel_lt; try omega; trivial.
 case (eq_nat_dec (TPlength t 0 n) 2); intro H4.
 rewrite 2 TPithdel_TPlength_1; auto; autorewrite with tuples;
 try rewrite TPlength_TPithdel; try omega.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples;
 try rewrite TPlength_TPithdel; try omega.
 rewrite TPithdel_lt_comm; try omega.
 rewrite TPithdel_lt_comm with (i:=1); try omega; trivial.

 assert (Q1: C |- TPith (TPlength t 0 n -1) (Fc 0 n (TPithdel 1 t 0 n)) 0 n ~aacc
                 TPith (TPlength t 0 n -1) (Fc 0 n (TPithdel 1 t' 0 n)) 0 n /\
            C |- TPithdel (TPlength t 0 n -1) (Fc 0 n (TPithdel 1 t 0 n)) 0 n ~aacc
                 TPithdel (TPlength t 0 n -1) (Fc 0 n (TPithdel 1 t' 0 n)) 0 n).
 apply IHequiv2. clear IHequiv2. destruct Q1.
 rewrite 2 TPith_overflow with (i:=i); try omega.
 rewrite 2 TPithdel_overflow with (i:=i); autorewrite with tuples; try omega.
 autorewrite with tuples in H.
 assert (Q1: TPlength t 0 n >= 1 /\ TPlength t 0 n >= 1). auto. destruct Q1.
 rewrite 2 TPith_TPithdel_geq in H; try omega.
 replace (TPlength t 0 n - 1 + 1) with (TPlength t 0 n) in H; try omega; trivial.
 rewrite <- Q. split~; trivial. apply equiv_A; simpl set_In; try omega.
 autorewrite with tuples. rewrite 2 TPith_TPithdel_lt; try omega; trivial.
 case (eq_nat_dec (TPlength t 0 n) 2); intro H6.
 rewrite 2 TPithdel_TPlength_1; auto; autorewrite with tuples;
 try rewrite TPlength_TPithdel; try omega.
 rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples;
 try rewrite TPlength_TPithdel; try omega.
 rewrite 2 TPithdel_lt_comm with (i:=1); try omega; trivial.

 rewrite 2 TPith_Fc_diff; trivial. rewrite 2 TPithdel_Fc_diff; trivial.
 split~; auto. apply equiv_A; simpl set_In; try omega; trivial.

 assert (Q:(1,n0) <> (E,n)). intro H'. inverts H'.
 simpl in H. apply H. right~.
 rewrite 2 TPith_Fc_diff; trivial. rewrite 2 TPithdel_Fc_diff; trivial.
 split~. apply equiv_AC with (i:=i); simpl set_In; try omega; trivial. 

 case ((2,n0) ==np (E,n)); intro H1. inverts H1.
 simpl in H. false. apply H. right~.
 rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff; trivial.
 split~; auto.

 case ((2,n0) ==np (E,n)); intro H1. inverts H1.
 simpl in H. false. apply H. right~.
 rewrite 2 TPith_Fc_diff; trivial.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff; trivial.
 split~; auto.

Qed.


Lemma aacc_equiv_Fc : forall C t t' E n, C |- t ~aacc t' ->
                                        C |- Fc E n t ~aacc Fc E n t'.
Proof.
  intros. gen_eq l : (TPlength t E n); intro H0.
  gen t t' H0 H. induction l using peano_induction; intros.
  case (set_In_dec eq_nat_dec E (0 :: 1 :: ([2]))); intro H2.
  Focus 2. apply equiv_Fc. left~. trivial.

  generalize H1; intro H1'.
  apply aacc_equiv_TPlength with (E:=E) (n:=n) in H1'.

  assert (Q: TPlength t E n >= 1). auto. 
  simpl in H2. destruct H2.

  rewrite <- H2 in *|-*. clear H2.
  apply aacc_equiv_TPith_E_diff_1_2 with
  (E:=0) (n:=n) (i:=1) in H1; try omega.
  destruct H1. apply equiv_A; simpl set_In; try omega; trivial.
  autorewrite with tuples; trivial.
  case (eq_nat_dec (TPlength t 0 n) 1); intro H3.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; auto; try omega.
  rewrite 2 TPithdel_Fc_eq; try omega.
  apply H with (m:=TPlength (TPithdel 1 t 0 n) 0 n); trivial.
  rewrite TPlength_TPithdel; try omega.

  simpl. intro. omega. destruct H2.
  
  rewrite <- H2 in *|-*. clear H2.
  apply aacc_equiv_TPith_l1 with (E:=1) (n:=n) in H1.
  destruct H1. destruct H1. destruct H2. destruct H3. 
  apply equiv_AC with (i:=x); simpl set_In;
  repeat split~; try omega; trivial.
  autorewrite with tuples; trivial.
  case (eq_nat_dec (TPlength t 1 n) 1); intro H5.
  rewrite 2 TPithdel_TPlength_1;
  autorewrite with tuples; try omega; auto.
  rewrite 2 TPithdel_Fc_eq; try omega.
  apply H with (m:=TPlength (TPithdel 1 t 1 n) 1 n); trivial.
  rewrite TPlength_TPithdel; try omega. 

  destruct H2; try contradiction.
  rewrite <- H2. apply equiv_Fc_c; trivial.
  
Qed.



  
