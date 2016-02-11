(***************************************************************************
 *AC_Equiv_Tuples.v   
***************************************************************************)

Require Export Equiv.
  

Lemma ac_equiv_TPlength : forall C t1 t2 m n, 
 C |- t1 ~ac t2 -> TPlength t1 m n = TPlength t2 m n. 
Proof.
  intros. induction H; trivial. simpl; auto.
  simpl. repeat case_nat; try omega.
  simpl. repeat case_nat; try omega.
  simpl in H0. destruct H; try omega.
  simpl in H. destruct H; try omega.
  clear H0 H2 H3 IHequiv1.
  destruct H1. destruct H1. destruct H2.
  simpl in *|-*. repeat case_nat; try omega.
  rewrite <- e in *|-*.
  rewrite 2 TPlength_TPithdel in IHequiv2; try omega.
  assert (Q: TPlength t 1 n >= 1). auto. omega.
Qed.

Lemma ac_equiv_TPith_l1 : forall C t t' m n, C |- t ~ac t' -> 
               exists j, j > 0 /\ j <= TPlength t' m n /\
                         C |- TPith 1 t m n ~ac TPith j t' m n /\ 
                         C |- TPithdel 1 t m n ~ac TPithdel j t' m n.
Proof. 
 intros. induction H; intros.

 exists 1. simpl in *|-*. repeat split; repeat case_nat; try omega; auto.
 exists 1. simpl in *|-*. repeat split; repeat case_nat; try omega; auto. Focus 3.
 exists 1. simpl in *|-*. repeat split; repeat case_nat; try omega; auto. Focus 3.
 exists 1. simpl in *|-*. repeat split; repeat case_nat; try omega; auto. Focus 3.
 exists 1. simpl in *|-*. repeat split; repeat case_nat; try omega; auto.
 
 generalize H. intro H'. 
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H'.
 case IHequiv1; trivial. intros j Hj. clear IHequiv1 IHequiv2. 
 destruct Hj. destruct H2. destruct H3. exists j. 
 simpl TPlength. rewrite 2 TPith_Pr_le; try omega; auto.
 case (TPlength t1' m n === 1); intro H8.  
 assert (Qj:j=1). omega. rewrite Qj in *|-*. 
 rewrite 2 TPithdel_t1_Pr; try omega. repeat split; try omega; trivial.
 rewrite 2 TPithdel_Pr_le; try omega; trivial.
 repeat split; try omega; auto.

 destruct IHequiv. destruct H1. destruct H2. destruct H3.
 generalize H0; intro H0'.
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H0.
 case (m0 === m); intro H5. case (n0 === n); intro H6.
 rewrite H5 in *|-*. rewrite H6. exists x.
 autorewrite with tuples. repeat split; trivial.
 case (TPlength t m n === 1); intro H7.
 assert (Qx : x = 1). omega. rewrite Qx.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq; try omega; auto.
 exists 1. rewrite TPlength_Fc_diff_n; trivial.
 rewrite 2 TPith_Fc_diff_n; trivial; try omega.
 rewrite 2 TPithdel_TPlength_1;
 try rewrite TPlength_Fc_diff_n; try omega; trivial.
 repeat split; auto.
 exists 1. rewrite TPlength_Fc_diff_m; trivial.
 rewrite 2 TPith_Fc_diff_m; trivial; try omega.
 rewrite 2 TPithdel_TPlength_1;
 try rewrite TPlength_Fc_diff_m; try omega; trivial.
 repeat split; auto.

 exists 1. clear IHequiv.
 assert (Q: TPlength (Fc m0 n0 t) m n = 1).
  simpl. repeat case_nat; trivial.
 assert (Q': TPlength (Fc m0 n0 t') m n = 1).
  simpl. repeat case_nat; trivial.
 rewrite Q'. rewrite 2 TPithdel_TPlength_1; try omega.
 repeat split; try omega; auto. 
 case (m0 === m); intro H3. case (n0 === n); intro H4.
 rewrite H3 in *|-*. rewrite H4 in *|-*.
 rewrite 2 TPith_Fc_eq; try omega; trivial.
 rewrite 2 TPith_Fc_diff_n; try omega; auto. 
 rewrite 2 TPith_Fc_diff_m; try omega; auto. 

 simpl in H0. destruct H0; try omega.
 
 (* simpl in H0. destruct H0; try omega. *)
 rewrite H0 in *|-*. clear H H0 IHequiv1.
 destruct H1. destruct H0. destruct H1.
 destruct IHequiv2. destruct H5. destruct H6. destruct H7.
 generalize H3. intro H3'. apply ac_equiv_TPlength with (m:=m) (n:=n) in H3'.
 case (m === 1); intro H9.  case (n === n0); intro H10.
 rewrite H9 in *|-*. rewrite <- H10 in *|-*. exists i. 
 autorewrite with tuples in *|-*. 
 rewrite 2 TPlength_TPithdel in *|-*; try omega; trivial.
 rewrite 2 TPithdel_Fc_eq; try omega; trivial. repeat split; trivial.
 assert (Q:TPlength t 1 n >= 1). auto. omega.
 exists 1. rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_n; auto.
 rewrite 2 TPith_Fc_diff_n; auto. repeat split; auto.
 apply equiv_AC with (i:=i); repeat split; trivial. simpl; left; trivial. (* left; trivial. *)
 exists 1. rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; auto.
 rewrite 2 TPith_Fc_diff_m; auto. repeat split; auto.
 apply equiv_AC with (i:=i); repeat split; trivial. simpl; left; trivial. (* left; trivial. *)

Qed.


Lemma ac_equiv_TPith_m_diff_1 : forall C t t' i m n,
  m <> 1 -> C |- t ~ac t' -> 
                 (C |- TPith i t m n ~ac TPith i t' m n /\
                  C |- TPithdel i t m n ~ac TPithdel i t' m n).
Proof.
 intros. gen i. induction H0; intro.
 simpl; repeat case_nat; split; auto.
 simpl; repeat case_nat; split; auto. Focus 3.
 simpl; repeat case_nat; split; auto. Focus 3.
 simpl; repeat case_nat; split; auto. Focus 3.
 simpl; repeat case_nat; split; auto.
 
 generalize H0_ H0_0. intros H0' H0_0'.
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H0_.
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H0_0.
 case (i === 0); intro H1. rewrite H1.
 rewrite 2 TPith_0. rewrite 2 TPithdel_0. split; auto.
 case (le_dec i (TPlength t1 m n)); intro H2.
 rewrite 2 TPith_Pr_le; try omega. 
 case (TPlength t1 m n === 1); intro H3.
 assert (Qi:i=1). omega. rewrite Qi. 
 rewrite 2 TPithdel_t1_Pr; try omega. 
 split; trivial. apply IHequiv1. 
 rewrite 2 TPithdel_Pr_le; try omega.
 split. apply IHequiv1. apply equiv_Pr; trivial. apply IHequiv1.
 case (le_dec i (TPlength t1 m n + TPlength t2 m n)); intro H3.
 rewrite 2 TPith_Pr_gt; try omega. 
 case (TPlength t2 m n === 1); intro H4.
 assert (Qi:i=TPlength t1 m n + 1). omega. rewrite Qi.
 rewrite TPithdel_t2_Pr; trivial. rewrite H0_.
 rewrite TPithdel_t2_Pr; try omega. 
 split; trivial. apply IHequiv2.
 rewrite 2 TPithdel_Pr_gt; try omega.
 rewrite H0_. split. apply IHequiv2.
 apply equiv_Pr; trivial. apply IHequiv2.
 rewrite 2 TPith_overflow; simpl TPlength; try omega.
 rewrite 2 TPithdel_overflow; simpl TPlength; try omega.
 split; auto.

 generalize H1; intro H1'.
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H1. 
 case (i === 0); intro H2. rewrite H2.
 rewrite 2 TPith_0; rewrite 2 TPithdel_0. split; auto.
 case (le_dec i (TPlength (Fc m0 n0 t) m n)); intro H3.
 case (m0 === m); intro H4. case (n0 === n); intro H5.
 rewrite H4 in *|-*. rewrite H5 in *|-*. autorewrite with tuples in *|-*.  
 split. apply IHequiv.
 case (TPlength t m n === 1); intro H6. assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq; try omega. apply equiv_Fc; trivial. apply IHequiv.
 rewrite TPlength_Fc_diff_n in H3; trivial. assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPith_Fc_diff_n; try omega. 
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_n; try omega.
 split; auto.
 rewrite TPlength_Fc_diff_m in H3; trivial. assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPith_Fc_diff_m; try omega. 
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; try omega.
 split; auto. assert (Q: ~ i <= TPlength (Fc m0 n0 t') m n).
 simpl in *|-*. repeat case_nat; try omega.
 rewrite 2 TPith_overflow; try omega.
 rewrite 2 TPithdel_overflow; try omega.
 split; auto.

 simpl in H0. destruct H0; try omega.
 case (i === 0); intro H4. rewrite H4. 
 rewrite 2 TPith_0. rewrite 2 TPithdel_0. split; auto.
 apply equiv_Fc_TPlength_1; trivial. simpl. left; trivial.
 case (le_dec i 1); intro H5. 
 rewrite 2 TPith_Fc_diff_m; try rewrite TPlength_Fc_diff_m; try omega.
 assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; try omega.
 split; auto.  apply equiv_Fc_TPlength_1; trivial. simpl. left; trivial.
 rewrite 2 TPith_overflow; try rewrite TPlength_Fc_diff_m; try omega.
 rewrite 2 TPithdel_overflow; try rewrite TPlength_Fc_diff_m; try omega. 
 split; auto. apply equiv_Fc_TPlength_1; trivial. simpl. left; trivial.

 simpl in H1. destruct H1; try omega.
 
 simpl in H0. destruct H0; try omega. clear H1.
 destruct H2. destruct H2. destruct H3.
 case (i0 === 0); intro H5. rewrite H5. rewrite 2 TPith_0. rewrite 2 TPithdel_0.
 split; auto. apply equiv_AC with (i:=i); repeat split; trivial.
 simpl; left; try omega. (* left; *) omega.
 case (le_dec i0 1); intro H6. assert (Qi0:i0=1). omega. rewrite Qi0.
 rewrite 2 TPith_Fc_diff_m; try omega; trivial.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; try omega; trivial.
 split; auto. apply equiv_AC with (i:=i); repeat split; trivial.
 simpl; left; try omega. (* left; *) omega.
 rewrite 2 TPith_overflow; try rewrite TPlength_Fc_diff_m; try omega; trivial.
 rewrite 2 TPithdel_overflow; try rewrite TPlength_Fc_diff_m; try omega; trivial.
 split; auto. apply equiv_AC with (i:=i); repeat split; trivial.
 simpl; left; try omega. (* left; *) omega.
Qed.


Lemma ac_equiv_Fc : forall C t t' m n, C |- t ~ac t' ->
                                       C |- Fc m n t ~ac Fc m n t'.
Proof.
  intros. gen_eq l : (TPlength t m n); intro H0.
  gen t t' H0 H. induction l using peano_induction; intros.
  case (m === 1); intro Hm. Focus 2.
  apply equiv_Fc; trivial. intro. simpl in H2. destruct H2; try omega.
  rewrite Hm in *|-*. clear Hm.
  generalize H1; intro H1'. apply ac_equiv_TPlength with (m:=1) (n:=n) in H1'.
  apply ac_equiv_TPith_l1 with (m:=1) (n:=n) in H1.
  destruct H1. destruct H1. destruct H2. destruct H3.

  case (TPlength t 1 n === 1); intro H5.
  apply equiv_Fc_TPlength_1; try omega. simpl; left; trivial.
  assert (Qx:x=1). omega. rewrite Qx in H3. trivial.
  
  case (TPlength t 1 n === 2); intro H6. 
  assert (H7 : TPlength t' 1 n = 2). omega.
  apply TPlength_2 in H6. apply TPlength_2 in H7.
  destruct H6. destruct H7.
  case H6; clear H6; intros t1 H6.
  case H6; clear H6; intros t2 H6.  
  destruct H6. destruct H8.
  case H7; clear H7; intros t1' H7.
  case H7; clear H7; intros t2' H7.  
  destruct H7. destruct H10.
  rewrite H6 in H3|-*. rewrite H7 in H3|-*.
  rewrite H6 in H4. rewrite H7 in H4.
  assert(Q: x <= TPlength t1' 1 n + TPlength t2' 1 n).
   rewrite H7 in H2. rewrite TPlength_Fc_app in H2. simpl in H2; trivial.
  rewrite 2 TPith_Fc_app in H3.
  rewrite 2 TPithdel_Fc_app in H4; simpl TPlength; try omega.
  apply equiv_AC with (i:=x). simpl; left; trivial. (* left; *) trivial. 
  repeat split; try rewrite TPlength_Fc_app; simpl; try omega.
  rewrite 2 TPith_Fc_app; trivial. rewrite 2 TPithdel_Fc_app; simpl TPlength; try omega.
  rewrite 2 Fc_app_Sn. apply ac_equiv_TPith_l1 with (m:=1) (n:=n) in H4.
  destruct H4. destruct H4. destruct H12. destruct H13. clear H14.
  rewrite TPlength_Fc_app in H12. rewrite TPlength_TPithdel in H12; simpl TPlength; try omega.
  simpl TPlength in H12. assert (Qx2:x2=1). omega. rewrite Qx2 in *|-*. clear H12 Qx2 H3 H4 H6 H7.
  rewrite 2 TPith_Fc_app in H13.   
  case (x === 1); intro Qx. rewrite Qx in *|-*.
  rewrite 2 TPithdel_t1_Pr; try omega.
  rewrite 2 TPithdel_t1_Pr in H13; try omega.
  apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.
  assert (Q'x:x=TPlength t1' 1 n + 1). omega. rewrite Q'x in *|-*.
  rewrite TPithdel_t1_Pr; try omega.
  rewrite TPithdel_t1_Pr in H13; try omega.
  rewrite TPithdel_t2_Pr; try omega.
  rewrite TPithdel_t2_Pr in H13; try omega.
  apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.
  
  apply equiv_AC with (i:=x); repeat split; try omega; trivial.
  simpl; left; trivial. assert (TPlength t 1 n >= 1). auto.
  apply H with (m:=TPlength t 1 n - 1);
  try rewrite TPlength_TPithdel; try omega; trivial.
Qed.


Lemma ac_equiv_Fc_app_inv : forall C i0 m n i1 t0 t1,
                            TPlength  t0 m n = 1 ->
                            C |- Fc_app i0 m n t0 ~ac Fc_app i1 m n t1 ->
                            C |- TPith 1 t0 m n ~ac TPith 1 t1 m n.
Proof.
  intros. assert (Q: TPlength t1 m n = 1).
  apply ac_equiv_TPlength with (m:=m) (n:=n) in H0.
  rewrite 2 TPlength_Fc_app in H0. omega.
  apply ac_equiv_TPith_l1 with (m:=m) (n:=n) in H0.
  destruct H0. destruct H0. destruct H1. destruct H2.
  rewrite TPlength_Fc_app in H1. assert (Qx:x=1). omega.
  rewrite 2 TPith_Fc_app in H2. rewrite Qx in H2. trivial.
Qed.  

Lemma ac_equiv_TPith_l : forall C t t' i m n, C |- t ~ac t' -> 
                         i > 0 -> i <= TPlength t m n ->
               exists j, j > 0 /\ j <= TPlength t' m n /\
                         C |- TPith i t m n ~ac TPith j t' m n /\ 
                         C |- TPithdel i t m n ~ac TPithdel j t' m n.
Proof.
  intros. gen_eq l : (TPlength t m n).
  intro H2. gen i t t' H2 H0 H1. induction l using peano_induction; intros.
  destruct H0.
  
 exists 1. simpl. repeat case_nat; repeat split; try omega; auto.
 exists 1. simpl in *|-*. assert (i=1). omega.
 repeat case_nat; repeat split; try omega; auto. Focus 3.
 exists 1. simpl in *|-*. assert (i=1). omega.
 repeat case_nat; repeat split; try omega; auto. Focus 3.
 exists 1. simpl in *|-*. assert (i=1). omega.
 repeat case_nat; repeat split; try omega; auto. Focus 3.
 exists 1. simpl in *|-*. assert (i=1). omega.
 repeat case_nat; repeat split; try omega; auto.
 
 simpl in H2. generalize H0_ H0_0. intros H0' H0_0'.
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H0'.
 apply ac_equiv_TPlength with (m:=m) (n:=n) in H0_0'.
 assert (Q:TPlength t1 m n >= 1). auto. 
 assert (Q':TPlength t2 m n >= 1). auto. 
 case (le_dec i (TPlength t1 m n)); intro H4.
 case H with (m0:=TPlength t1 m n) (i:=i) (t:=t1) (t':=t1'); try omega; trivial.
 intros j H5. destruct H5. destruct H5. destruct H6. exists j.
 rewrite 2 TPith_Pr_le; try omega. 
 case (TPlength t1 m n === 1); intro H8.
 assert (Qi:i=1). omega. assert (Qj:j=1). omega.  
 rewrite Qi in *|-*. rewrite Qj in *|-*.
 rewrite 2 TPithdel_t1_Pr; try omega. simpl.
 repeat split; try omega; trivial.
 rewrite 2 TPithdel_Pr_le; try omega.
 simpl; repeat split; try omega; auto.
 case H with (m0:=TPlength t2 m n)
             (i:=i - TPlength t1 m n) (t:=t2) (t':=t2'); try omega; trivial.
 intros j H5. destruct H5. destruct H5. destruct H6. exists (TPlength t1 m n + j).
 rewrite 2 TPith_Pr_gt; try omega. rewrite <- H0'.
 replace (TPlength t1 m n + j - TPlength t1 m n) with j; try omega. 
 case (TPlength t2 m n === 1); intro H8.
 assert (Qi:i=TPlength t1 m n + 1). omega. assert (Qj:j=1). omega.  
 rewrite Qi in *|-*. rewrite Qj in *|-*.
 replace (TPlength t1 m n + 1 - TPlength t1 m n) with 1 in *|-*; try omega.  
 rewrite TPithdel_t2_Pr; try omega.
 rewrite H0'. rewrite TPithdel_t2_Pr; try omega. simpl.
 repeat split; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try omega.
 replace (TPlength t1 m n + j - TPlength t1' m n) with j; try omega.
 simpl; repeat split; try omega; auto.

 exists i. generalize H4; intro H4'.
 generalize H4'; intro H4''.
 apply ac_equiv_TPlength with (m:=m0) (n:=n0) in H4'.
 apply ac_equiv_TPith_m_diff_1 with (i:=i) (m:=m0) (n:=n0) in H4. destruct H4.
 case (m0 === m); intro H6. case (n0 === n); intro H7.
 rewrite H6 in *|-*. rewrite H7 in *|-*. autorewrite with tuples in *|-*.
 clear H6 H7. case (TPlength t m n === 1); intro H6.
 assert (Qi:i=1). omega. rewrite Qi in *|-*.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega.
 repeat split; try omega; trivial. rewrite 2 TPithdel_Fc_eq; try omega.
 repeat split; try omega; trivial. apply equiv_Fc; trivial.
 rewrite TPlength_Fc_diff_n in *|-*; trivial.
 rewrite 2 TPith_Fc_diff_n; try omega;  trivial. assert (Qi:i=1). omega. rewrite Qi in *|-*.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_n; try omega; trivial.
 repeat split; try omega; auto.
 rewrite TPlength_Fc_diff_m in *|-*; trivial.
 rewrite 2 TPith_Fc_diff_m; try omega;  trivial. assert (Qi:i=1). omega. rewrite Qi in *|-*.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; try omega; trivial.
 repeat split; try omega; auto. intro. apply H0. simpl; left; try omega.

 exists 1. simpl in H0. destruct H0; try omega. rewrite <- H0 in *|-*.
 assert (Q:TPlength (Fc 1 n0 t) m n = 1).
  rewrite H0. simpl. repeat case_nat; try omega.
  rewrite <- e; trivial.
 assert (Q':TPlength (Fc 1 n0 t') m n = 1).
  rewrite H0. simpl. repeat case_nat; try omega.
  rewrite <- e; trivial.
 assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPithdel_TPlength_1; trivial.
 repeat split; try omega; auto.
 case (1 === m); intro H7. case (n0 === n); intro H8.
 rewrite <- H7 in *|-*. rewrite H8 in *|-*.
 autorewrite with tuples; trivial.
 rewrite 2 TPith_Fc_diff_n; try omega.
 apply equiv_Fc_TPlength_1; trivial.
 simpl; left; trivial.
 rewrite 2 TPith_Fc_diff_m; try omega.
 apply equiv_Fc_TPlength_1; trivial.
 simpl; left; trivial.

 simpl in H4; try omega.

 simpl in H0. destruct H0; try omega. rewrite <- H0 in *|-*.
 clear H0 H4. destruct H5. destruct H4. destruct H5. 
 generalize H0_0; intro H0_0'. 
 apply ac_equiv_TPlength with (m:=1) (n:=n0) in H0_0'.
 autorewrite with tuples in H0_0'. 
 rewrite 2 TPlength_TPithdel in H0_0'; try omega; trivial.
 case (1 === m); intro H7. case (n0 === n); intro H8.
 rewrite <- H7 in *|-*. rewrite H8 in *|-*.

 case (TPlength t 1 n === 2); intro H9. assert (H10 : TPlength t' 1 n = 2). omega. 
 apply TPlength_2 in H9. apply TPlength_2 in H10.
 destruct H9. destruct H10.
 case H9; clear H9; intros t1 H9. case H9; clear H9; intros t2 H9.
 case H10; clear H10; intros t'1 H10. case H10; clear H10; intros t'2 H10.
 destruct H9. destruct H11. destruct H10. destruct H13.
 
 case (i === 1); intro Q0. rewrite Q0. exists i0.
 rewrite 2 TPithdel_Fc_eq; try omega. 
 repeat split; autorewrite with tuples; try omega; trivial.

 autorewrite with tuples in H2.
 assert (Q2:i=2). rewrite H9 in H2. rewrite TPlength_Fc_app in H2. simpl in H2. omega.
 rewrite Q2. case (i0 === 1); intro Q1. exists 2.
 rewrite Q1 in *|-. rewrite H9 in H0_|-*. rewrite H10 in H0_|-*.
 rewrite H9 in H0_0. rewrite H10 in H0_0. rewrite 2 Fc_app_Sn.
 rewrite TPlength_Fc_app. rewrite 2 TPith_Fc_app in *|-*.
 rewrite 2 TPithdel_Fc_app in *|-*; simpl TPlength; try omega. 
 replace (TPithdel 2 (<| t1, t2 |>) 1 n) with
 (TPithdel (TPlength t1 1 n + 1) (<| t1, t2 |>) 1 n); fequals; try omega.
 replace (TPithdel 2 (<| t'1, t'2 |>) 1 n) with
 (TPithdel (TPlength t'1 1 n + 1) (<| t'1, t'2 |>) 1 n); fequals; try omega.
 rewrite 2 TPithdel_t2_Pr; trivial. rewrite 2 TPithdel_t1_Pr in H0_0; trivial.
 rewrite 2 Fc_app_Sn in H0_0. rewrite 2 TPith_Pr_gt; try omega. 
 rewrite 2 TPith_Pr_le in H0_; try omega. 
 replace (2 - TPlength t1 1 n) with 1; try omega.
 replace (2 - TPlength t'1 1 n) with 1; try omega.
 repeat split; try omega. apply ac_equiv_Fc_app_inv with (i0:=S x) (i1:=S x0); trivial.
 apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.

 assert (Q3:i0=2). rewrite H10 in H6. rewrite TPlength_Fc_app in H6. simpl in H6. omega.
 rewrite Q3 in *|-. exists 1.
 rewrite H9 in H0_|-*. rewrite H10 in H0_|-*.
 rewrite H9 in H0_0. rewrite H10 in H0_0. rewrite 2 Fc_app_Sn.
 rewrite TPlength_Fc_app. simpl TPlength.
 rewrite 2 TPith_Fc_app in *|-*. 
 rewrite 2 TPithdel_Fc_app in *|-*; simpl TPlength; try omega.
 rewrite TPith_Pr_le in H0_; try omega. 
 rewrite TPith_Pr_gt in H0_; try omega. 
 rewrite TPith_Pr_gt; try omega.
 rewrite TPith_Pr_le; try omega. 
 rewrite TPithdel_t1_Pr in H0_0; try omega.
 replace 2 with (TPlength t'1 1 n + 1) in H0_0; try omega.
 replace (2 - TPlength t'1 1 n) with 1 in H0_0; try omega.
 rewrite TPithdel_t2_Pr in H0_0; try omega.
 rewrite TPithdel_t1_Pr; try omega.
 replace (2 - TPlength t1 1 n) with 1; try omega.
 replace 2 with (TPlength t1 1 n + 1); try omega.
 rewrite TPithdel_t2_Pr; try omega.
 repeat split; try omega. rewrite Fc_app_Sn in H0_0. 
 apply ac_equiv_Fc_app_inv with (i0:=S x) (i1:=S x0); trivial.
 replace (2 - TPlength t'1 1 n) with 1 in H0_; try omega.
 apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.

 case (i === 1); intro Qi. rewrite Qi. exists i0.
 rewrite 2 TPithdel_Fc_eq; try omega; repeat split; auto;
 autorewrite with tuples; trivial.
 
 autorewrite with tuples in H2.
 case H with (m  := TPlength (Fc 1 n (TPithdel 1 t 1 n)) 1 n) (i := i-1)
             (t  := Fc 1 n (TPithdel 1 t 1 n))
             (t' := Fc 1 n (TPithdel i0 t' 1 n));
             autorewrite with tuples;
             try rewrite TPlength_TPithdel; try omega; trivial. 
     
 intros j Hj. destruct Hj. destruct H11. destruct H12.  
 autorewrite with tuples in H12.
 rewrite 2 TPithdel_Fc_eq in H13;   
 try rewrite TPlength_TPithdel; try omega; trivial.               
 case (le_dec i0 j); intro H14.
 
 exists (j + 1). 
 rewrite 2 TPith_TPithdel_geq in H12; try omega.
 rewrite TPithdel_comm_geq in H13; try omega.
 rewrite TPithdel_comm_geq with (i:=j) in H13; try omega.
 replace (i - 1 + 1) with i in *|-; try omega.
 rewrite 2 TPithdel_Fc_eq; try omega.
 repeat split; try omega; trivial.
 autorewrite with tuples; trivial.
 apply equiv_AC with (i:=i0); trivial. simpl; left; trivial. (* left;*) trivial.
 repeat split; try rewrite TPlength_TPithdel; try omega.
 rewrite 2 TPith_TPithdel_lt; try omega; trivial.

 exists j.
 rewrite TPith_TPithdel_geq in H12; try omega.
 rewrite TPith_TPithdel_lt in H12; try omega.
 rewrite TPithdel_comm_geq in H13; try omega.
 rewrite TPithdel_comm_lt with (i:=j) in H13; try omega.
 replace (i - 1 + 1) with i in *|-; try omega.
 repeat split; try omega; trivial.
 autorewrite with tuples; trivial.
 rewrite 2 TPithdel_Fc_eq; try omega; trivial.
 apply equiv_AC with (i:=i0-1). simpl; left; trivial. (* left; *) trivial.
 repeat split; try rewrite TPlength_TPithdel; try omega.
 rewrite TPith_TPithdel_lt; try omega; trivial.
 rewrite TPith_TPithdel_geq; try omega; trivial.
 replace (i0 - 1 + 1) with i0; try omega; trivial.
 trivial.

 exists 1. 
 rewrite TPlength_Fc_diff_n in *|-*; trivial.
 rewrite 2 TPith_Fc_diff_n; try omega.
 assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_n; try omega.
 repeat split; try omega; auto. apply equiv_AC with (i:=i0); repeat split; trivial.
 simpl; left; trivial. (* left; *) trivial.

 exists 1. 
 rewrite TPlength_Fc_diff_m in *|-*; trivial.
 rewrite 2 TPith_Fc_diff_m; try omega.
 assert (Qi:i=1). omega. rewrite Qi.
 rewrite 2 TPithdel_TPlength_1; try rewrite TPlength_Fc_diff_m; try omega.
 repeat split; try omega; auto. apply equiv_AC with (i:=i0); repeat split; trivial.
 simpl; left; trivial. (* left; *) trivial.
 assert (Q: TPlength t 1 n0 >= 1). auto. omega.
Qed.

Lemma ac_equiv_AC : forall C t1 t2 i j n,
                      i > 0 -> j > 0 ->
                      i <= TPlength t1 1 n -> j <= TPlength t2 1 n ->
                      TPlength t1 1 n <> 1 -> TPlength t2 1 n <> 1 ->
                      C |- TPith i t1 1 n ~ac TPith j t2 1 n  ->
                      C |- Fc 1 n (TPithdel i t1 1 n) ~ac Fc 1 n (TPithdel j t2 1 n) ->
                           C |- Fc 1 n t1 ~ac Fc 1 n t2.
Proof.
  intros. gen_eq l : (TPlength t1 1 n); intro H7.
  generalize i j t1 t2 H7 H H0 H1 H2 H3 H4 H5 H6;
  clear  i j t1 t2 H7 H H0 H1 H2 H3 H4 H5 H6.
  induction l using peano_induction; intros.
  case (i === 1); intro Qi. rewrite Qi in *|-.
  apply equiv_AC with (i:=j); repeat split; try omega; trivial.  simpl. left; trivial.
  generalize H8; intro H8'. apply ac_equiv_TPlength with (m:=1) (n:=n) in H8'.
  autorewrite with tuples in H8'. rewrite 2 TPlength_TPithdel in H8'; try omega; trivial.
  case (TPlength t1 1 n === 2); intro H9.

  clear H.
  generalize H9; intro H9'. apply TPlength_2 in H9'.
  destruct H9'. case H; clear H; intros t0 H.
  case H; clear H; intros t3 H. destruct H. destruct H10.
  assert (H12 : TPlength t2 1 n = 2). omega. 
  generalize H12; intro H12'. apply TPlength_2 in H12'.
  destruct H12'. case H13; clear H13; intros t4 H13.
  case H13; clear H13; intros t5 H13. destruct H13. destruct H14.
  rewrite H. rewrite H13. assert (Q0:i=2). omega.
  rewrite H in H6. rewrite H13 in H6.
  rewrite H in H8. rewrite H13 in H8. rewrite Q0 in *|-*.
  rewrite 2 TPith_Fc_app in H6. 
  rewrite 2 TPithdel_Fc_app in H8; simpl TPlength; try omega.
  replace 2 with (TPlength t0 1 n + 1) in H8; try omega.
  rewrite TPith_Pr_gt in H6; try omega.
  replace (2 - TPlength t0 1 n) with 1 in H6; try omega.
  rewrite TPithdel_t2_Pr in H8; try omega.
  rewrite 2 Fc_app_Sn in H8.

  case (j === 1); intro Hj. rewrite Hj in *|-.
  rewrite TPith_Pr_le in H6; try omega.
  rewrite TPithdel_t1_Pr in H8; try omega.
  apply equiv_AC with (i:=2); repeat split; 
  try rewrite TPlength_Fc_app; simpl TPlength; try omega.
  simpl. left; trivial. rewrite 2 TPith_Fc_app.
  rewrite TPith_Pr_le; try omega.   
  rewrite TPith_Pr_gt; try omega.
  replace (2 - TPlength t4 1 n) with 1; try omega.
  apply ac_equiv_Fc_app_inv with (i0:=S x) (i1:= S x0); trivial.
  rewrite 2 TPithdel_Fc_app; simpl TPlength; try omega.
  rewrite 2 Fc_app_Sn. rewrite TPithdel_t1_Pr; try omega.
  replace 2 with (TPlength t4 1 n + 1); try omega.
  rewrite TPithdel_t2_Pr; try omega.
  apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.

  assert (Qj:j=2). omega. rewrite Qj in *|-.
  replace 2 with (TPlength t4 1 n + 1) in H8; try omega.
  rewrite TPith_Pr_gt in H6; try omega.
  rewrite TPithdel_t2_Pr in H8; try omega.
  replace (2 - TPlength t4 1 n) with 1 in H6; try omega.
  apply equiv_AC with (i:=1); repeat split; 
  try rewrite TPlength_Fc_app; simpl TPlength; try omega.
  simpl; left; trivial. rewrite 2 TPith_Fc_app.
  rewrite 2 TPith_Pr_le; try omega.   
  apply ac_equiv_Fc_app_inv with (i0:=S x) (i1:= S x0); trivial.
  rewrite 2 TPithdel_Fc_app; simpl TPlength; try omega.
  rewrite 2 Fc_app_Sn. rewrite 2 TPithdel_t1_Pr; try omega.
  apply Fc_app_TPlength_1; try omega; trivial. simpl; left; trivial.
 
  apply ac_equiv_TPith_l1 with (m:=1) (n:=n) in H8.
  destruct H8. destruct H8. destruct H10. destruct H11.
  autorewrite with tuples in *|-.
  rewrite 2 TPithdel_Fc_eq in H12;
  try rewrite TPlength_TPithdel in *|-*; try omega.
  rewrite TPith_TPithdel_lt in H11; try omega. 

  case (le_dec j x); intro H13.
  
  rewrite TPith_TPithdel_geq in H11; try omega.
  apply equiv_AC with (i:=x+1); 
  repeat split; try omega; trivial. simpl; left. trivial.
  apply H with (i:=i-1) (j:=j) (m:=TPlength (TPithdel 1 t1 1 n) 1 n);
  try rewrite TPlength_TPithdel; try omega.
  rewrite TPith_TPithdel_geq; try omega.
  rewrite TPith_TPithdel_lt; try omega.
  replace (i -1 + 1) with i; try omega; trivial.
  rewrite TPithdel_comm_geq; try omega.
  rewrite TPithdel_comm_lt with (i:=j); try omega.
  replace (i -1 + 1) with i; try omega.
  replace (x +1 - 1) with x; try omega; trivial.

  rewrite TPith_TPithdel_lt in H11; try omega.
  apply equiv_AC with (i:=x); 
  repeat split; try omega; trivial. simpl; left. trivial.
  apply H with (i:=i-1) (j:=j-1) (m:=TPlength (TPithdel 1 t1 1 n) 1 n);
  try rewrite TPlength_TPithdel; try omega.
  rewrite 2 TPith_TPithdel_geq; try omega.
  replace (i -1 + 1) with i; try omega.
  replace (j -1 + 1) with j; try omega; trivial.
  rewrite TPithdel_comm_geq; try omega.
  rewrite TPithdel_comm_geq with (i:=j-1); try omega.
  replace (i -1 + 1) with i; try omega.
  replace (j -1 + 1) with j; try omega; trivial.
Qed.
  
