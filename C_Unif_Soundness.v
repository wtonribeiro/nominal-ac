(**
%\begin{verbatim}
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Soundness.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
Description : A proof of the soundness of the C-unification algorithm is 
	      presented in this part of the theory. Roughly speaking, it 
	      was formalised that each solution of a generated successful 
	      leaf is also a solution of the original problem.
 
 Last Modified On: Jun 2, 2018.
 ============================================================================
\end{verbatim}%
*)

Require Export C_Unif_Termination.

(** %\section{ Soundness of the C-unification algorithm }% *)
	
	
(** %\subsection{ Completeness of fresh\_sys }% *) 
(**
	Be a reduction by fresh_sys form T to T'. Sl is a solution
	for T if and only if Sl a solution for T'. This is proved
	by case analysis over fresh_sys T T'.
*) 

Lemma fresh_sys_compl : forall T T' Sl, fresh_sys T T' -> (sol_c Sl T  <-> sol_c Sl T') .
Proof.
  intros. destruct T. destruct T'. destruct p. destruct p1.
  unfold sol_c. simpl. split~; intro H0; destruct H0; destruct H1; destruct H2.

  (* -> *)
  inverts H; repeat split~; intros.
    (* fresh_sys_Ut *)
    apply H1. apply set_remove_1 in H; trivial.
    apply H2. apply set_remove_1 in H; trivial.
    (* fresh_sys_At *)
    apply H1. apply set_remove_1 in H; trivial.
    apply H2. apply set_remove_1 in H; trivial.
    (* fresh_sys_Fc *)
    apply H1 in H5. simpl in H5. inverts H5.
    case (Constraint_eqdec (a0 #? t) (a #? s1)); intro H9.
    inverts H9; trivial.
    apply H1. apply set_remove_1 in H.
    apply set_add_elim in H. destruct H; try contradiction; trivial.
    apply H2. apply set_remove_1 in H. apply set_add_elim in H.
    destruct H; trivial. inverts H.
    (* fresh_sys_Ab_1 *)
    apply H1. apply set_remove_1 in H; trivial.
    apply H2. apply set_remove_1 in H; trivial.
    (* fresh_sys_Ab_2 *)
    apply H1 in H11. simpl in H11. inverts H11. false.
    case (Constraint_eqdec (a0 #? t) (a #? s1)); intro H11.
    inverts H11; trivial.
    apply H1. apply set_remove_1 in H.
    apply set_add_elim in H. destruct H; try contradiction; trivial.
    apply H2. apply set_remove_1 in H. apply set_add_elim in H.
    destruct H; trivial. inverts H.
    (* fresh_sys_Su *)
    unfold fresh_env in *|-*. intros.
    apply H1 in H5. simpl in H5.
    apply fresh_lemma_1 in H5.
    case ((!pi) $ a ==at a0); intro H6. case (Var_eqdec X X0); intro H7.
    rewrite <- H6. rewrite <- H7; simpl; autorewrite with perm; trivial.
    apply H0. apply set_add_elim in H. destruct H; trivial.
    inverts H. false.
    apply H0. apply set_add_elim in H. destruct H; trivial.
    inverts H. false.
    apply H1. apply set_remove_1 in H; trivial.
    apply H2. apply set_remove_1 in H; trivial.
    (* fresh_sys_Pr *)
    apply H1 in H5. simpl in H5. inverts H5.
    case (Constraint_eqdec (a0 #? t0) (a #? s1)); intro H11. inverts H11; trivial.
    case (Constraint_eqdec (a0 #? t0) (a #? t)); intro H12. inverts H12; trivial.
    apply H1. apply set_remove_1 in H.
    apply set_add_elim in H. destruct H; try contradiction; trivial.
    apply set_add_elim in H. destruct H; try contradiction; trivial.
    apply H2. apply set_remove_1 in H.
    apply set_add_elim in H. destruct H. inverts H.  
    apply set_add_elim in H. destruct H; trivial. inverts H.    

  (* <- *)
  inverts H; repeat split~; intros.
    (* fresh_sys_Ut *)
    case (term_eqdec t (<<>>)); intro H6.
    rewrite H6. simpl. apply fresh_Ut.
    apply H1. apply set_remove_3; trivial.
    intro H7. inverts H7. apply H6; trivial.
    apply H2; apply set_remove_3; trivial.
    discriminate.
    (* fresh_sys_At *)
    case (term_eqdec (%b) t); intro H7.
    case (a ==at a0); intro H8.
    rewrite <- H7. rewrite <- H8.
    simpl. apply fresh_At; trivial.
    apply H1. apply set_remove_3; trivial.
    intro H9. inverts H9. apply H8; trivial.
    apply H1. apply set_remove_3; trivial.
    intro H9. inverts H9. apply H7; trivial.
    apply H2; apply set_remove_3; trivial.
    discriminate.
    (* fresh_sys_Fc *)
    assert (Q : fst Sl |- a # (Fc E n (s1 |^ snd Sl))).
     apply fresh_Fc. apply H1. apply set_remove_3.
     apply set_add_intro2; trivial.     
     intro H'. inverts H'. symmetry in H6.
     apply Fc_neq_psub in H6; trivial.
    case (term_eqdec (Fc E n s1) t); intro H7.
    case (a ==at a0); intro H9.
    rewrite <- H7. rewrite <- H9. simpl; trivial.
    apply H1. apply set_remove_3.
    apply set_add_intro1; trivial.
    intro H10. inverts H10. apply H9; trivial.
    apply H1. apply set_remove_3.
    apply set_add_intro1; trivial.
    intro H10. inverts H10. apply H7; trivial.
    apply H2; apply set_remove_3.
    apply set_add_intro1; trivial.
    discriminate.    
    (* fresh_sys_Ab_1 *)
    case (term_eqdec ([a]^s1) t); intro H6.
    case (a ==at a0); intro H7.
    rewrite <- H6. rewrite <- H7.
    simpl. apply fresh_Ab_1; trivial.
    apply H1. apply set_remove_3; trivial.
    intro H9. inverts H9. apply H7; trivial.
    apply H1. apply set_remove_3; trivial.
    intro H9. inverts H9. apply H6; trivial.
    apply H2; apply set_remove_3; trivial.
    discriminate.
    (* fresh_sys_Ab_2 *)
    assert (Q : fst Sl |- a # ([b]^(s1 |^ snd Sl))).
     apply fresh_Ab_2; trivial.
     apply H1. apply set_remove_3.
     apply set_add_intro2; trivial.     
     intro H'. inverts H'. symmetry in H5.
     apply Ab_neq_psub in H5; trivial.
    case (term_eqdec ([b]^s1) t); intro H7.
    case (a ==at a0); intro H9.
    rewrite <- H7. rewrite <- H9. simpl; trivial.
    apply H1. apply set_remove_3.
    apply set_add_intro1; trivial.
    intro H10. inverts H10. apply H9; trivial.
    apply H1. apply set_remove_3.
    apply set_add_intro1; trivial.
    intro H10. inverts H10. apply H7; trivial.
    apply H2; apply set_remove_3.
    apply set_add_intro1; trivial.
    discriminate.
    (* fresh_sys_Su *)
    unfold fresh_env in *|-*. intros.
    apply H0. apply set_add_intro1; trivial.
    case (term_eqdec (pi|.X) t); intro H6.
    case (a ==at a0); intro H7.
    rewrite <- H6. rewrite <- H7.
    replace (pi|.X) with (pi @ ([]|.X)).
    rewrite subst_perm_comm.
    gen_eq pi' : (!pi); intro H8.
    replace pi with (!pi').
    apply fresh_lemma_2. unfold fresh_env in H0.
    apply H0. apply set_add_intro2; trivial.
    rewrite H8. apply rev_involutive.
    autorewrite with perm. simpl. trivial.
    apply H1. apply set_remove_3; trivial.
    intro H8. inverts H8. apply H7; trivial.
    apply H1. apply set_remove_3; trivial.
    intro H7. inverts H7. apply H6; trivial.
    apply H2. apply set_remove_3; trivial.
    discriminate.    
    (* fresh_sys_Pr *)
    assert (Q : fst Sl |- a # (<| s1|^(snd Sl), t|^(snd Sl)|>)).
     apply fresh_Pr.
     apply H1. apply set_remove_3.
     apply set_add_intro1. apply set_add_intro2; trivial.    
     intro H'. inverts H'. apply symmetry in H6.
     apply Pr_neq_psub_1 in H6; trivial.     
     apply H1. apply set_remove_3.
     apply set_add_intro2; trivial.    
     intro H'. inverts H'. apply symmetry in H6.
     apply Pr_neq_psub_2 in H6; trivial. 
    case (term_eqdec (<|s1,t|>) t0); intro H6.
    case (a ==at a0); intro H7.
    rewrite <- H6. rewrite <- H7. simpl; trivial.
    apply H1. apply set_remove_3.
    apply set_add_intro1. apply set_add_intro1; trivial.
    intro H8. inverts H8. apply H7; trivial.
    apply H1. apply set_remove_3.
    apply set_add_intro1. apply set_add_intro1; trivial.
    intro H8. inverts H8. apply H6; trivial.
    apply H2; apply set_remove_3.
    apply set_add_intro1. apply set_add_intro1; trivial.
    discriminate. 
Qed.  

(** %\subsection{ Preservation of solutions by equ\_sys }% *) 
(**
	Be a reduction by equ_sys form T to T'. If Sl is a solution
	for T', then Sl is also a solution for T. This is proved
	by case analysis over equ_sys T T'.
*)    

Lemma equ_sol_preserv : forall T T' Sl varSet, valid_triple T ->
                        equ_sys varSet T T' -> sol_c Sl T' -> sol_c Sl T .
Proof.
  intros. destruct T. destruct T'. destruct p. destruct p1.
  unfold sol_c in *|-*. destruct Sl. simpl in *|-*.
  destruct H1. destruct H2. destruct H3. 
  inverts H0; repeat split~; intros.  

  (* equ_sys_refl *)

  apply H2. apply set_remove_3; trivial. discriminate.
  case (term_eqdec s t); intro H5. rewrite H5. apply c_equiv_refl.
  apply H3. apply set_remove_3; trivial. intro H7. inverts H7.
  apply H5; trivial.

  (* equ_sys_Pr *)

  apply H2. apply set_remove_3.
  apply set_add_intro1. apply set_add_intro1; trivial.
  discriminate.
  assert (Q: c1 |- <|s2,s3|>|^s1 ~c (<|t0,t1|>|^s1)).
   simpl. apply equiv_Pr.
   apply H3. apply set_remove_3. 
   apply set_add_intro1. apply set_add_intro2; trivial.
   intro H7. inverts H7. symmetry in H8.
   apply Pr_neq_psub_1 in H8. trivial.
   apply H3. apply set_remove_3. 
   apply set_add_intro2; trivial.
   intro H7. inverts H7. symmetry in H8.
   apply Pr_neq_psub_2 in H8. trivial.   
  case (Constraint_eqdec (s~?t) ((<|s2,s3|>)~?(<|t0,t1|>))); intro H7.
  inverts H7; trivial.
  apply H3. apply set_remove_3; trivial.
  apply set_add_intro1. apply set_add_intro1; trivial. 

  (* equ_sys_Fc *)

  apply H2. apply set_remove_3. apply set_add_intro1; trivial.
  discriminate.
  assert (Q : c1 |- (t|^s1) ~c (t'|^s1)).
   apply H3. apply set_remove_3. apply set_add_intro2; trivial.
   intro H8. inverts H8. symmetry in H6.
   apply Fc_neq_psub in H6. trivial.
  case (Constraint_eqdec (s~?t0) ((Fc E n t)~?(Fc E n t'))); intro H8.
  inverts H8. apply c_equiv_Fc; trivial.
  apply H3. apply set_remove_3.
  apply set_add_intro1; trivial.
  intro H9. inverts H9. apply H8; trivial.
  
  (* equ_sys_C1 *)

  apply H2. apply set_remove_3. 
  apply set_add_intro1. apply set_add_intro1; trivial.
  discriminate.
  assert (Q: c1 |- <|s2,s3|>|^s1 ~c (<|t0,t1|>|^s1)).
   simpl. apply equiv_Pr.
   apply H3. apply set_remove_3. 
   apply set_add_intro1. apply set_add_intro2; trivial.
   intro H7. inverts H7. symmetry in H8.
   apply Fc_Pr_neq_psub_1 in H8. trivial.
   apply H3. apply set_remove_3. 
   apply set_add_intro2; trivial.
   intro H7. inverts H7. symmetry in H8.
   apply Fc_Pr_neq_psub_2 in H8. trivial.   
  case (Constraint_eqdec (s~?t) (Fc 2 n (<|s2,s3|>)~?(Fc 2 n (<|t0,t1|>)))); intro H7.
  inverts H7. simpl in Q|-*. apply c_equiv_Fc; trivial. 
  apply H3. apply set_remove_3; trivial.
  apply set_add_intro1. apply set_add_intro1; trivial. 
  
  (* equ_sys_C2 *)

  apply H2. apply set_remove_3. 
  apply set_add_intro1. apply set_add_intro1; trivial.
  discriminate.
  assert (Q: c1 |- <|s2,s3|>|^s1 ~c (<|t1,t0|>|^s1)).
   simpl. apply equiv_Pr.
   apply H3. apply set_remove_3. 
   apply set_add_intro1. apply set_add_intro2; trivial.
   intro H7. inverts H7. symmetry in H8.
   apply Fc_Pr_neq_psub_1 in H8. trivial.
   apply H3. apply set_remove_3. 
   apply set_add_intro2; trivial.
   intro H7. inverts H7. symmetry in H8.
   apply Fc_Pr_neq_psub_2 in H8. trivial.   
  case (Constraint_eqdec (s~?t) (Fc 2 n (<|s2,s3|>)~?(Fc 2 n (<|t0,t1|>)))); intro H7.
  inverts H7. simpl in Q|-*. inverts Q. apply equiv_C2; trivial. left~.
  apply H3. apply set_remove_3; trivial.
  apply set_add_intro1. apply set_add_intro1; trivial. 


  (* equ_sys_Ab1 *)

  apply H2. apply set_remove_3. apply set_add_intro1; trivial.
  discriminate.
  assert (Q: c1 |- t|^s1 ~c (t'|^s1)).
   apply H3. apply set_remove_3. 
   apply set_add_intro2; trivial.
   intro H5. inverts H5. symmetry in H8.
   apply Ab_neq_psub in H8. trivial.
  case (Constraint_eqdec (s~?t0) (([a]^t) ~? ([a]^t'))); intro H7.
  inverts H7. simpl. apply equiv_Ab_1; trivial.
  apply H3. apply set_remove_3; trivial.
  apply set_add_intro1; trivial.


  (* equ_sys_Ab2 *) 
  apply H2. apply set_remove_3.
  apply set_add_intro1. apply set_add_intro1; trivial.
  discriminate.
  assert (Q : c1 |- t|^s1 ~c ((([(a, b)]) @ t')|^s1)).
   apply H3. apply set_remove_3.
   apply set_add_intro1. apply set_add_intro2; trivial. 
   intro H5. inverts H5. symmetry in H8.
   apply Ab_neq_psub in H8. trivial.
  assert (Q' : c1 |- a # (t'|^s1)).
   apply H2. apply set_remove_3.
   apply set_add_intro2; trivial.
   discriminate.
  case (Constraint_eqdec (s~?t0) (([a]^t) ~? ([b]^t'))); intro H8.
  inverts H8. simpl. apply equiv_Ab_2; trivial.
  rewrite <- subst_perm_comm; trivial.
  apply H3. apply set_remove_3; trivial.
  apply set_add_intro1. apply set_add_intro1; trivial.


  (* equ_sys_inst *)

  assert (Q : c1 |- a # (t0|^(([(X,(!pi)@t)]©s1)))).
   rewrite subst_comp_expand. apply H2.
   apply set_union_intro1.
   replace (a #? (t0 |^ ([(X, (! pi) @ t)]))) with (subs_Constraint (a#?t0) ([(X, (! pi) @ t)])).
   apply set_In_subs_problem. apply set_remove_3. apply set_remove_3; trivial.
   intro H10. inverts H10. intro H10. inverts H10.
   simpl; trivial.

  assert (Q': set_In X (Problem_vars p0)).
   destruct H12. apply Problem_vars_set_In with (u:= (pi|.X)~?t); trivial.
   simpl. apply set_union_intro1. left~.
   apply Problem_vars_set_In with (u:= t~?(pi|.X)); trivial.
   simpl. apply set_add_intro2; trivial.

  assert (Q'': forall Y, set_In Y (term_vars t) ->  set_In Y (Problem_vars p0)).
   intros. destruct H12. apply Problem_vars_set_In with (u:= (pi|.X)~?t); trivial.
   simpl. apply set_union_intro2; trivial.
   apply Problem_vars_set_In with (u:= t~?(pi|.X)); trivial.
   simpl. apply set_add_intro1; trivial.
  
   
  clear H0 H1 H2 H3 H12.

  induction t0; simpl in *|-*; trivial.
  case (a ==at a0); intro H2. rewrite H2. apply fresh_Ab_1.
  apply fresh_Ab_2; trivial. apply IHt0.
  inverts Q. false. trivial.
  inverts Q. apply fresh_Pr.
  apply IHt0_1; trivial. apply IHt0_2; trivial.
  inverts Q. apply fresh_Fc. apply IHt0; trivial.
  
  gen Q. case (X ==v v); trivial. intros H2 Q.
  rewrite <- H2. clear H2.
  apply c_equiv_fresh with (t1:= p @ (((! pi) @ t) |^ s1)); trivial.
  apply c_equiv_equivariance. replace (look_up X s1) with (([]|.X)|^s1).
  case H4; clear H4; intros s2 H4.
  apply c_equiv_unif_2 with (S1:=(s©([(X,(!pi) @ t)]))©s2); trivial.
  unfold valid_triple in H. simpl in H. destruct H.
  rewrite 4 subst_comp_expand.
  rewrite 2 inter_dom_term_vars with (t:= (!pi)@t).
  rewrite not_In_dom. rewrite subst_var_eq.
  autorewrite with perm. apply c_equiv_refl.
  intro H5. apply set_inter_nil with (a:=X) in H.
  apply H. apply set_inter_intro; trivial.
  apply In_dom_eq_dom_rec; trivial. 
  apply set_inter_nil; intros. intro H1.
  apply set_inter_elim in H1. destruct H1.
  apply var_in_dom_rec_singleton in H2.
  rewrite H2 in H1. rewrite perm_term_vars in H1.
  apply H9. apply set_union_intro1; trivial.
  apply set_inter_nil; intros. intro H5.
  apply set_inter_elim in H5. destruct H5.
  apply set_inter_nil with (a:=a0) in H. apply H.
  apply set_inter_intro; trivial.
  rewrite perm_term_vars in H1. apply Q''; trivial.
  simpl. autorewrite with perm; trivial.

  assert (Q1: forall Y, set_In Y (term_vars t) ->  set_In Y (Problem_vars p0)).
   intros. destruct H12. apply Problem_vars_set_In with (u:= (pi|.X)~?t); trivial.
   simpl. apply set_union_intro2; trivial.
   apply Problem_vars_set_In with (u:= t~?(pi|.X)); trivial.
   simpl. apply set_add_intro1; trivial.
   
  assert (Q2: forall Y, set_In Y (term_vars t0) ->  set_In Y (Problem_vars p0)).
   intros. apply Problem_vars_set_In with (u:= s0~?t0); trivial.
   simpl. apply set_union_intro2; trivial.

  assert (Q3: forall Y, set_In Y (term_vars s0) ->  set_In Y (Problem_vars p0)).
   intros. apply Problem_vars_set_In with (u:= s0~?t0); trivial.
   simpl. apply set_union_intro1; trivial.

  case H4; clear H4; intros s2 H4.
  unfold valid_triple in H; simpl in H. destruct H.
  
  case (Constraint_eqdec (s0~?t0) ((pi|.X)~?t)); intro H6. inverts H6.

  apply c_equiv_unif_2 with (S1:=(s©([(X,(!pi) @ t)]))©s2); trivial.
  rewrite 4 subst_comp_expand.
  rewrite not_In_dom. rewrite subst_var_eq.
  rewrite inter_dom_term_vars with (t:= t).
  rewrite not_occurs; trivial.
  rewrite 2 subst_perm_comm.
  apply c_equiv_pi_inv_side. apply c_equiv_refl.
  intro H10. apply H9. apply set_union_intro1; trivial.
  apply set_inter_nil; intros. intro H8.
  apply set_inter_elim in H8. destruct H8.
  apply set_inter_nil with (a:=a) in H. apply H.
  apply set_inter_intro; trivial.
  apply Q2; trivial. intro H8.
  apply set_inter_nil with (a:=X) in H. apply H.
  apply set_inter_intro. apply In_dom_eq_dom_rec; trivial.
  apply Q3. simpl. left~.

  case (Constraint_eqdec (s0~?t0) (t~?(pi|.X))); intro H7. inverts H7. 

  apply c_equiv_unif_2 with (S1:=(s©([(X,(!pi) @ t)]))©s2); trivial.
  rewrite 4 subst_comp_expand.
  rewrite not_In_dom. rewrite subst_var_eq.
  rewrite inter_dom_term_vars with (t:= t).
  rewrite not_occurs; trivial.
  rewrite 2 subst_perm_comm. apply c_equiv_sym.
  apply c_equiv_pi_inv_side. apply c_equiv_refl.
  intro H10. apply H9. apply set_union_intro1; trivial.
  apply set_inter_nil; intros. intro H8.
  apply set_inter_elim in H8. destruct H8.
  apply set_inter_nil with (a:=a) in H. apply H.
  apply set_inter_intro; trivial.
  apply Q1; trivial. intro H8.
  apply set_inter_nil with (a:=X) in H. apply H.
  apply set_inter_intro. apply In_dom_eq_dom_rec; trivial.
  apply Q2. simpl. left~.
  
  assert (Q : c1 |- (s0|^(([(X,(!pi)@t)]©s1))) ~c (t0|^(([(X,(!pi)@t)]©s1)))).
   rewrite 2 subst_comp_expand. apply H3.
   apply set_union_intro1.
   replace ((s0 |^ ([(X, (! pi) @ t)])) ~? (t0 |^ ([(X, (! pi) @ t)])))
     with (subs_Constraint (s0~?t0) ([(X, (! pi) @ t)])).
   apply set_In_subs_problem. apply set_remove_3; trivial. apply set_remove_3; trivial.
   simpl; trivial.

  clear H0 H1 H2 H3 H5 H6 H7 H12.
  rewrite 2 subst_comp_expand in Q.
  apply c_equiv_unif_2 with (S1 := (s © ([(X, (! pi) @ t)])) © s2); trivial.
  apply c_equiv_unif_2 with (S2 := (s © ([(X, (! pi) @ t)])) © s2) in Q. clear H4.
  rewrite 4 subst_comp_expand in Q.  rewrite 4 subst_comp_expand.
  rewrite inter_dom_term_vars with (t:= s0).
  rewrite inter_dom_term_vars with (t:= t0).
  rewrite 2 inter_dom_term_vars with (S:= s) in Q.
  rewrite inter_dom_term_vars with (t:= s0 |^ ([(X, (! pi) @ t)])) in Q.
  rewrite inter_dom_term_vars with (t:= t0 |^ ([(X, (! pi) @ t)])) in Q. trivial.

  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.
  apply var_in_dom_rec_singleton in H1.
  rewrite H1 in H0. apply In_im_subst_term in H0.
  rewrite perm_term_vars in H0.
  apply H9. apply set_union_intro1; trivial.

  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.
  apply var_in_dom_rec_singleton in H1.
  rewrite H1 in H0. apply In_im_subst_term in H0.
  rewrite perm_term_vars in H0.
  apply H9. apply set_union_intro1; trivial.

  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.  
  apply set_inter_nil with (a:=a) in H.
  apply H. apply set_inter_intro; trivial.
  apply In_im_subst_term' in H0.
  apply set_union_elim in H0. destruct H0.
  apply Q2; trivial.
  rewrite perm_term_vars in H0.
  apply Q1; trivial.

  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.  
  apply set_inter_nil with (a:=a) in H.
  apply H. apply set_inter_intro; trivial.
  apply In_im_subst_term' in H0.
  apply set_union_elim in H0. destruct H0.
  apply Q3; trivial.
  rewrite perm_term_vars in H0.
  apply Q1; trivial.
 
  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.  
  apply set_inter_nil with (a:=a) in H.
  apply H. apply set_inter_intro; trivial.
  apply Q2; trivial.

  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.  
  apply set_inter_nil with (a:=a) in H.
  apply H. apply set_inter_intro; trivial.
  apply Q3; trivial.

  apply subst_sym; trivial.

  case H4; clear H4; intros s2 H4.
  exists ([(X,(!pi)@t)] © s2).
  apply subst_assoc; trivial.

  (* equ_sys_inv *)

  apply H2. apply set_remove_3.
  apply set_add_intro1; trivial.
  discriminate.
  assert (Q : c1 |- (pi++(! pi')|.X)|^s1 ~c ((([])|.X)|^s1)).
   apply H3. apply set_remove_3.
   apply set_add_intro2; trivial.
   intro H5. inverts H5. apply H12; trivial.
  case (Constraint_eqdec (s~?t) ((pi|.X)~?(pi'|.X))); intro H7. 
  inverts H7. 
  replace (pi|.X) with (pi @ ([]|.X)).
  replace (pi'|.X) with (pi' @ ([]|.X)).  
  rewrite 2 subst_perm_comm.
  apply c_equiv_sym.
  apply c_equiv_pi_inv_side.
  apply c_equiv_sym.
  rewrite perm_comp.
  rewrite <- subst_perm_comm.
  autorewrite with perm. simpl app; trivial.
  autorewrite with perm; simpl; trivial.
  autorewrite with perm; simpl; trivial. 
  apply H3. apply set_remove_3; trivial.
  apply set_add_intro1; trivial.

Qed.


Lemma tr_clos_equ_sol_preserv : forall T T' Sl varSet, valid_triple T ->
      tr_clos _ (equ_sys varSet) T T' -> sol_c Sl T' -> sol_c Sl T .
Proof.
  intros. induction H0; trivial.
  apply equ_sol_preserv with (Sl:=Sl) in H0; trivial.
  apply equ_sol_preserv with (Sl:=Sl) in H0; trivial.
  apply IHtr_clos; trivial.
  apply equ_valid_preservation with (T:= s) (varSet:=varSet); trivial.
Qed.
  
(** %\subsection{ Preservation of solutions by unif\_step }% *) 
(**
	Be a unifcation step form T to T'. If Sl is a solution
	for T', then Sl is also a solution for T. This is proved
	by case analysis over unif_step T T' and uses lemmas
	fresh_sys_compl and equ_sol_preserv.
*)

Lemma unif_step_preserv : forall T T' Sl varSet,
                          valid_triple T ->
                          unif_step varSet T T' -> sol_c Sl T' -> sol_c Sl T.
Proof.
 intros. destruct H0.
 apply equ_sol_preserv with (T':= T') (varSet:=varSet); trivial.
 apply fresh_sys_compl with (Sl:=Sl) in H2. apply H2; trivial.
Qed.

 
(** %\subsection{ Soundness of the C-unification algorithm }% *)  
(** 
	Be a unifcation path form T to T'. If Sl is a solution
	for T', then Sl is also a solution for T. This is proved
	by case analysis over unif_path T T' and uses lemma
	unif_step_preserv.
*)
 
Theorem c_unif_path_soundness : forall T T' Sl varSet,
                                valid_triple T ->
                                unif_path varSet T T' -> sol_c Sl T' -> sol_c Sl T.
Proof.
  intros. destruct H0.
  induction H0; trivial.
  apply unif_step_preserv with (Sl := Sl) in H0; trivial.
  apply unif_step_preserv with (Sl := Sl) in H0; trivial.
  apply IHtr_clos; trivial.
  apply unif_step_valid_preserv with (T:= s) (varSet:=varSet); trivial.
Qed.




(** %\section{ Characterisation of successful leaves }% *)   
(**
	The characterisation of successful leaves is 
	the subject of this part of the theory.

*)

(** % \subsection{ Freshness constraints in a leaf } % *)
(**
	Be a leaf T = (C, S, P). If [a#?s] is in P and the 
	equational part of P is a fixpoint problem, then 
	the term s must be equal to [a]. This statement 
	is proved by case analysis over [s].
*)

Lemma leaf_fresh_sys : forall a s C S P varSet,
                         set_In (a#?s) P ->
                         leaf varSet (C,S,P) ->
                         fixpoint_Problem (equ_proj P) ->
                         s = %a.
Proof.
  intros. unfold leaf in H0. unfold NF in H0.
  destruct s; trivial.
  false. apply (H0 (C, S, P\(a #? (<<>>)))).
  apply fresh_unif_step; trivial. apply fresh_sys_Ut; trivial.
  case (a ==at a0); intro H2. rewrite H2; trivial.
  false. apply (H0 (C, S, P\(a #? (%a0)))).
  apply fresh_unif_step; trivial. apply fresh_sys_At; trivial. 
  case (a ==at a0); intro H2. rewrite H2 in *|-.
  false. apply (H0 (C, S, P\(a0 #? ([a0]^s)))).
  apply fresh_unif_step; trivial. apply fresh_sys_Ab_1; trivial. 
  false. apply (H0 (C, S, (P|+(a#?s))\(a #? ([a0]^s)))).
  apply fresh_unif_step; trivial. apply fresh_sys_Ab_2; trivial. 
  false. apply (H0 (C,S,(((P|+(a#?s1))|+(a#?s2))\(a#?(<|s1,s2|>))))).
  apply fresh_unif_step; trivial. apply fresh_sys_Pr; trivial.
  false. apply (H0 (C, S, (P|+(a#?s))\(a #? (Fc n n0 s)))).
  apply fresh_unif_step; trivial. apply fresh_sys_Fc; trivial.
  false. apply (H0 (C|++((!p) $ a,v),S,(P\(a#?(p|.v))))).  
  apply fresh_unif_step; trivial. apply fresh_sys_Su; trivial.
Qed.


(** % \subsection{ Characterisation of equations that are in normal forms of equ\_sys } % *)
(**
	Be T = (C, S, P) a normal form regarding equ_sys. If s ~? t is in P then 
	it must match with one of the following showed cases. This is proved by case analysis
	over s and t. 
	
	Notice that the predicate Proper_Problem P synthesises
	the following property: for each equation s ~? t in P, if s or t 
	has as a subterm (Fc C n s0), with C commutative, then s0
	must be a pair. This restriction was added to insure that
	commutative function symbols are only applied to pairs.
*)  

Lemma NF_equ_sys : forall C S P varSet,
                     
           Proper_Problem P ->

           NF _ (equ_sys varSet) (C, S, P) ->

            (forall s t, set_In (s ~? t) P ->
                        
            ((forall pi X, t <> pi|.X) /\
              ((s = (<<>>) /\ t <> (<<>>)) \/
              (exists a, s = (%a) /\ t <> (%a))  \/
              (exists E n u, s = (Fc E n u) /\ forall v, t <> (Fc E n v)) \/
              (exists a u, s = [a]^u /\ forall b v, t <> [b]^v) \/
              (exists u v, s = (<|u,v|>) /\ forall u' v', t <> (<|u',v'|>))  \/
              (exists pi X, s = pi|.X /\ set_In X (set_union Var_eqdec (term_vars t) varSet)))) \/     
            
            ((forall pi X, s <> pi|.X) /\ (exists pi, exists X, t = pi|.X /\
                                                 set_In X (set_union Var_eqdec (term_vars s) varSet)))
               \/

            (exists pi pi' X Y, X <> Y /\ s = pi|.X /\ t = pi'|.Y /\ set_In X varSet /\ set_In Y varSet) \/   
               
            (fixpoint_equ (s ~? t)) ).
Proof.
  intros.

  case (term_eqdec s t); intro H2.
  (* s = t *)
   rewrite H2 in *|-*; clear H2. 
   false. apply (H0 (C, S, P\(t~?t))). apply equ_sys_refl; trivial.                             
  (* s <> t *)
   case (Su_eqdec s); case (Su_eqdec t); intros H3 H4.
   (* s and t are both suspensions *)  
    case H3; clear H3; intros pi' H3. case H3; clear H3; intros Y H3.
    case H4; clear H4; intros pi H4. case H4; clear H4; intros X H4.
    rewrite H3 in *|-*. rewrite H4 in *|-*. clear H3 H4.
    case (Y ==v X); intro H3. 
     (* the variables of the two suspesions are equal *)
      rewrite H3 in *|-*. clear H3.
      case (Perm_eqdec pi' ([])); intro H3.
      (* pi' = [] *) 
       rewrite H3 in *|-*. clear H3. 
       right~. right~. right~. unfold fixpoint_equ. exists pi X.
       split~. intro H3. rewrite H3 in H2. false. 
      (* pi' <> [] *)
       false. apply (H0 (C,S,(P|+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X)))).
       apply equ_sys_inv; trivial. intro H4. rewrite H4 in H2. false.    
     (* the variables of the two suspesions are different *) 
       case (set_In_dec Var_eqdec X varSet); intro H4.
       (* X is in varSet *)
        case (set_In_dec Var_eqdec Y varSet); intro H5.
        (* Y is in varSet *)
         right~. right~. left~. exists pi pi' X Y. repeat split~.
        (* Y is not in varSet *) 
         false.
          apply (H0 (C,S©([(Y,(!pi')@(pi|.X))]),
                        ((P\(pi'|.Y~?(pi|.X))\((pi|.X)~?(pi'|.Y)))|^^([(Y,(!pi')@(pi|.X))]))
                          \cup(C/?(S©([(Y,(!pi')@(pi|.X))]))))).
          apply equ_sys_inst; trivial. simpl. intro H6.
          apply set_union_elim in H6. destruct H6; try contradiction.
          simpl in H6. destruct H6; trivial. symmetry in H6. contradiction.
          right~.
       false.
         apply (H0 (C,S©([(X,(!pi)@(pi'|.Y))]),
                        ((P\(pi|.X~?(pi'|.Y))\((pi'|.Y)~?(pi|.X)))|^^([(X,(!pi)@(pi'|.Y))]))
                          \cup(C/?(S©([(X,(!pi)@(pi'|.Y))]))))).
       apply equ_sys_inst; trivial. simpl. intro H5.
       apply set_union_elim in H5. destruct H5; try contradiction.
       simpl in H5. destruct H5; trivial. contradiction.
       left~.
   (* only s is a suspension *)
    case H4; clear H4; intros pi H4.    
    case H4; clear H4; intros X H4. rewrite H4 in *|-*. clear H4.
    case (set_In_dec Var_eqdec X (set_union Var_eqdec (term_vars t) varSet)); intro H4.
    (* X is in set_union _ (term_vars t) varSet *)
     left~. split~. right~. right~. right~. right~. right~.
     exists pi X. split~.
    (* X is not in set_union _ (term_vars t) varSet *) 
     false. apply (H0 (C,S©([(X,(!pi)@t)]),
                        ((P\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))
                          \cup(C/?(S©([(X,(!pi)@t)]))))).
     apply equ_sys_inst; trivial. left~.
   (* only t is a suspension *)  
    case H3; clear H3; intros pi H3.    
    case H3; clear H3; intros X H3. rewrite H3 in *|-*. clear H3.
    case (set_In_dec Var_eqdec X (set_union Var_eqdec (term_vars s) varSet)); intro H5.
    (* X is in set_union _ (term_vars s) varSet *)
     right~. left~. split~. exists pi X. split~.     
    (* X is not in set_union _ (term_vars s) varSet *)
     false. apply (H0 (C,S©([(X,(!pi)@s)]),
                        ((P\(pi|.X~?s)\(s~?(pi|.X)))|^^([(X,(!pi)@s)]))
                          \cup(C/?(S©([(X,(!pi)@s)]))))).
     apply equ_sys_inst; trivial. right~.

  (* both s and t are not suspensions *)
   left~. split~. destruct s.
   (* s = <<>> *)
    left~.
   (* s = %a *)
    right~. left~. exists a. split~.
   (* s = [a]^s0 *)
    right~. right~. right~. left~. 
    exists a. exists s. split~; intros.
    intro H5. rewrite H5 in *|-*; clear H5.
    case (a ==at b); intro H5. rewrite H5 in H1.
    apply (H0 (C,S,P|+(s~?v)\(([b]^s)~?([b]^v)))).
    apply equ_sys_Ab1; trivial. 
    apply (H0 (C,S,((P|+(s~?([(a,b)]@v))|+(a#?v)))\(([a]^s)~?([b]^v)))).
    apply equ_sys_Ab2; trivial. 
   (* s = <|s1, s2|> *)
    right~. right~. right~. right~. left~.
    exists s1 s2. split~; intros. intro H5.
    rewrite H5 in *|-*.
    apply (H0 (C,S,((P|+(s1~?u'))|+(s2~?v'))\(<|s1, s2|>~?<|u', v'|>))).
    apply equ_sys_Pr; trivial.
   (* s = Fc n n0 s0 *) 
    right~. right~. left~. exists n n0 s. split~; intros.
    intro H5. rewrite H5 in *|-*. clear H5.
    case (eq_nat_dec n 2); intro H5. rewrite H5 in *|-*; clear H5.
    assert (Q : is_Pr s /\ is_Pr v).
     apply H in H1. destruct H1.
     unfold Proper_term in H1.
     unfold Proper_term in H5. split~.
     apply H1 with (n:=n0). apply In_subterms.
     apply H5 with (n:=n0). apply In_subterms.
    destruct Q. apply is_Pr_exists in H5. apply is_Pr_exists in H6.
    case H5; clear H5; intros s0 H5. case H5; clear H5; intros s1 H5.
    case H6; clear H6; intros t0 H6. case H6; clear H6; intros t1 H6.
    rewrite H5 in *|-. rewrite H6 in *|-*. clear H5 H6.
    apply (H0 (C,S,((P|+(s0~?t0))|+(s1~?t1))\(Fc 2 n0 (<|s0,s1|>)~?(Fc 2 n0 (<|t0,t1|>))))).
    apply equ_sys_C1; trivial.
    apply (H0 (C,S,(P|+(s~?v))\(Fc n n0 s ~?(Fc n n0 v)))).
    apply equ_sys_Fc; trivial.

   false. 
 
Qed.


(** % \subsection{ Equations in a sucessful leaf by equ\_sys } % *)
(**
	Be T = (C, S, P) a normal form of equ_sys. If s ~? t is in P and 
	T has solutions, then s ~? t must be a fixpoint equation. 
	A proof of this lemma is obtained by case analysis over the feasible
	normal forms of equ_sys, and it uses Lemma NF_equ_sys.
*)

Lemma NF_successful_equ: forall C S P s t varSet,
                         Proper_Problem P ->
                         set_In (s ~? t) P -> 
                         NF _ (equ_sys varSet) (C, S, P) ->
                         (exists Sl, sol_c Sl (C, S, P) /\
                          set_inter Var_eqdec (dom_rec (snd Sl)) varSet = []) -> 
                         fixpoint_equ (s ~? t).  
Proof.
  intros. case H2; clear H2; intros Sl H2. destruct H2.
  unfold sol_c in H2.
  destruct H2. destruct H4. destruct H5. simpl fst in *|-. simpl snd in *|-.
  apply NF_equ_sys with (s:=s) (t:=t) (varSet := varSet) in H1; trivial.
  destruct H1. destruct H1. destruct H7. destruct H7.
  assert (Q : fst Sl |- (<<>>) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial.
  inverts Q. false. apply H8.
  destruct t; simpl in H10; inverts H10; trivial. false.   
  destruct H7. case H7; clear H7; intros a H7. destruct H7.   
  assert (Q : fst Sl |- (%a) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial. 
  inverts Q. false. apply H8.
  destruct t; simpl in H12; inverts H12; trivial. false. 
  destruct H7. case H7; clear H7; intros E H7.
  case H7; clear H7; intros n H7.
  case H7; clear H7; intros u H7. destruct H7.  
  assert (Q : fst Sl |- (Fc E n u) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial. 
  inverts Q. destruct t; simpl in H14; inverts H14; trivial.
  false. false. simpl in H14. omega. simpl in H14. omega.
  destruct t; simpl in H13; inverts H13. false. false.
  destruct t; simpl in H13; inverts H13. false. false.  
  destruct H7. 
  case H7; clear H7; intros a H7.
  case H7; clear H7; intros u H7. destruct H7.  
  assert (Q : fst Sl |- ([a]^u) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial. 
  inverts Q. destruct t; simpl in H13; inverts H13;
   trivial. false. false. destruct t; inverts H11. false. false.
  destruct H7.
  case H7; clear H7; intros u H7.
  case H7; clear H7; intros v H7. destruct H7.
  assert (Q : fst Sl |- (<|u,v|>) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial. 
  inverts Q. destruct t; simpl in H12; inverts H12;
   trivial. false. false.
  case H7; clear H7; intros pi H7.
  case H7; clear H7; intros X H7. destruct H7.
  assert (Q : fst Sl |- (pi|.X) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial.
  apply set_union_elim in H8. destruct H8.
  assert (Q' : set_In X (term_vars ((!pi) @ t))).
   rewrite perm_term_vars; trivial.
  apply psubterms_subs with (S:=snd Sl) in Q'; trivial.
  case Q'; clear Q'; intros pi' Q'.
  replace (pi|.X) with (pi @ ([]|.X)) in Q;
  autorewrite with perm; trivial. 
  rewrite subst_perm_comm in Q.
  apply c_equiv_pi_inv_side in Q.
  apply c_equiv_perm_psubterm with (pi := pi') in Q.
  rewrite <- 2 subst_perm_comm in Q.
  autorewrite with perm in Q. simpl app in Q.
  contradiction.
  intros. intro H9. destruct t;
    autorewrite with perm in H9; inverts H9. false.
  rewrite inter_dom_term_vars in Q. inverts Q.
  destruct t; simpl in H13; inverts H13. false.
  apply set_inter_nil. intros Y H9.
  apply set_inter_nil with (a:=Y) in H3.
  apply H3. clear H3. apply set_inter_elim in H9.
  destruct H9. simpl in H3. destruct H3; try contradiction.
  apply set_inter_intro; trivial.
  rewrite <- H3; trivial.
  destruct H1. destruct H1.
  case H7; clear H7; intros pi H7.
  case H7; clear H7; intros X H7. destruct H7.
  assert (Q : fst Sl |- s |^ snd Sl ~c ((pi|.X) |^ snd Sl)). 
   rewrite <- H7. apply H5; trivial.
  apply set_union_elim in H8. destruct H8.
  assert (Q' : set_In X (term_vars ((!pi) @ s))).
   rewrite perm_term_vars; trivial. apply c_equiv_sym in Q.
  apply psubterms_subs with (S:=snd Sl) in Q'; trivial.
  case Q'; clear Q'; intros pi' Q'.
  replace (pi|.X) with (pi @ ([]|.X)) in Q;
  autorewrite with perm; trivial. 
  rewrite subst_perm_comm in Q.
  apply c_equiv_pi_inv_side in Q.
  apply c_equiv_perm_psubterm with (pi := pi') in Q.
  rewrite <- 2 subst_perm_comm in Q.
  autorewrite with perm in Q. simpl app in Q.
  contradiction.
  intros. intro H9. destruct s;
    autorewrite with perm in H9; inverts H9. false.
  rewrite inter_dom_term_vars with (t:=pi|.X) in Q. inverts Q.
  destruct s; simpl in H9; inverts H9. false.
  apply set_inter_nil. intros Y H9.
  apply set_inter_nil with (a:=Y) in H3.
  apply H3. clear H3. apply set_inter_elim in H9.
  destruct H9. simpl in H3. destruct H3; try contradiction.
  apply set_inter_intro; trivial.
  rewrite <- H3; trivial.
  destruct H1; trivial.
  case H1; clear H1; intros pi H1.
  case H1; clear H1; intros pi' H1.
  case H1; clear H1; intros X H1.  
  case H1; clear H1; intros Y H1.
  destruct H1. destruct H7. destruct H8. destruct H9.
  apply H5 in H0. rewrite H7 in H0. rewrite H8 in H0.
  rewrite 2 inter_dom_term_vars in H0.
  inverts H0. false.
  apply set_inter_nil; intros Z H11.
  apply set_inter_nil with (a:=Z) in H3.
  apply H3; clear H3.
  apply set_inter_elim in H11. destruct H11.
  simpl in H3. destruct H3; try contradiction.
  apply set_inter_intro; trivial. rewrite <- H3; trivial.
  apply set_inter_nil; intros Z H11.
  apply set_inter_nil with (a:=Z) in H3.
  apply H3; clear H3.
  apply set_inter_elim in H11. destruct H11.
  simpl in H3. destruct H3; try contradiction.
  apply set_inter_intro; trivial. rewrite <- H3; trivial.
  
Qed.


(** % \subsection{ Characterisation of successful leaves } % *)
(**
		A successful leaf T = (C, S, P) must be a fixpoint problem. This
		is proved by case analysis over P, and 
		uses lemmas NF_successful_equ and leaf_fresh_sys.
*)
  
Lemma successful_leaves_ch : forall T varSet,
                               Proper_Problem (snd T) ->
                               (leaf varSet T /\
                                (exists Sl, (sol_c Sl T) /\
                                 set_inter Var_eqdec (dom_rec (snd Sl)) varSet = [] )) ->
                               (fixpoint_Problem (snd T)).
Proof.
  intros. destruct H0. 
  destruct T. destruct p. simpl.
  
  assert (Q : fixpoint_Problem (equ_proj p0)).
   apply set_In_fixpoint_eq_proj; intros.   
   apply NF_successful_equ with (C:=c) (S:=s) (P:=p0) (varSet:=varSet); trivial.
   unfold leaf in H0. unfold NF in *|-*.
   intros T H3. apply (H0 T). apply equ_unif_step; trivial.

  unfold fixpoint_Problem; intros. destruct u.

  case H1; clear H1; intros Sl H1. unfold sol_c in H1.  
  destruct H1. destruct H1. destruct H4.
  apply leaf_fresh_sys with (a:=a) (s:=t) in H0; trivial.    
  assert (Q': fst Sl |- a # ((%a) |^ snd Sl)).  
   apply H4. simpl. rewrite <- H0. trivial.
  simpl in Q'. inverts Q'. false.
   
  apply NF_successful_equ with (C:=c) (S:=s) (P:=p0) (varSet:=varSet); trivial.
  unfold leaf in H0. unfold NF in *|-*.
  intros T H3. apply (H0 T).   
  apply equ_unif_step; trivial.
Qed.    


(** % \subsection{ Generated successful leaves } % *)
(** 
	Be a unification path from T to T'. If T' = (C', S', P') is
	a successful leaf, then P' is a fixpoint problem. This is 
	a corollary of the Lemma successful_leaves_ch.
*)	

Corollary gen_successfull_leaves : forall T T' varSet,                              
                                   Proper_Problem (snd T)  ->
                                   unif_path varSet T T' ->  
                                    (exists Sl, (sol_c Sl T') /\
                                     set_inter Var_eqdec (dom_rec (snd Sl)) varSet = []) ->   
                                   fixpoint_Problem (snd T').
Proof.
  intros. apply successful_leaves_ch with (varSet:=varSet).
  apply unif_path_Proper_Problem with (T:=T) (varSet:=varSet); trivial.
  destruct H0. split~.
Qed.
