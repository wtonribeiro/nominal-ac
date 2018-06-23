(**
%\begin{verbatim}
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Completeness.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : The formalisation of the theorem of C-unification 
               completeness (unif_path_completeness) is the main result 
	       of this file. It also contains two preliminary lemmas 
	       (equ_sys_compl and unif_step_compl).
 
 Last Modified On: June 7th, 2018.
 ============================================================================
 \end{verbatim} %
*)

Require Export C_Unif_Soundness.

(** %\section{ Completeness of equ\_sys }% *)
(**
	The following lemma express the completeness of the reductions 
	by the equational system equ_sys. Its proof is done by case 
	analysis over equ_sys and uses Lemma equ_sol_preserv.
 *)

Lemma equ_sys_compl  : forall T Sl varSet,
                       valid_triple T ->
                       ~ NF _ (equ_sys varSet) T ->
                       (sol_c Sl T  <-> (exists T', equ_sys varSet T T' /\ sol_c Sl T')).

Proof.
  intros.
  apply equ_sys_neg_NF in H0.
  case H0; clear H0; intros T' H0.
  
  split~; intro. 
  destruct T. destruct T'.
  destruct p. destruct p1. destruct Sl.
  unfold sol_c in H1|-*. simpl in H1|-*.
  destruct H1. destruct H2. destruct H3.

  inverts H0.
  
  (* equ_sys_refl *)
  exists (c0,s0,p0\(s2~?s2)); simpl.
  repeat split~; intros.
  apply equ_sys_refl; trivial.
  apply H2. apply set_remove_1 in H0. trivial. 
  apply H3. apply set_remove_1 in H0. trivial. 
  
  (* equ_sys_Pr *)
  exists (c0,s0,(p0|+(s2~?t0)|+(s3~?t1))\((<|s2,s3|>)~?(<|t0,t1|>))); simpl.
  repeat split~; intros. 
  apply equ_sys_Pr; trivial.
  apply H2. apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply set_add_elim in H0. destruct H0. inverts H0. trivial.
  assert (Q:c1|-(<|s2,s3|>)|^s1~c((<|t0,t1|>)|^s1)).
   apply H3; trivial.
  inverts Q.
  apply set_remove_1 in H0. apply set_add_elim in H0.
  destruct H0. inverts H0; trivial.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply H3; trivial.
   
  (* equ_sys_Fc *)
  exists (c0,s0,(p0|+(t~?t'))\(Fc E n t~?Fc E n t')); simpl.
  repeat split~; intros.  
  apply equ_sys_Fc; trivial.
  apply H2. apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0; trivial. inverts H0.
  apply set_remove_1 in H0. apply set_add_elim in H0.
  destruct H0. inverts H0. 
  assert (Q : c1 |- (Fc E n t)|^s1 ~c ((Fc E n t')|^s1)).
   apply H3; trivial.
  inverts Q; trivial. simpl in H10; omega. simpl in H10; omega. 
  false. false.
  apply H3; trivial.
  
  (* equ_sys_C1 *)
  generalize H6; intro H6'.
  apply H3 in H6'. simpl in H6'. inverts H6'.
  destruct H8. simpl in H0. omega. destruct H0. false.
  simpl in H5. destruct H5; apply H5; trivial. 
  exists (c0,s0,(p0|+(s2~?t0)|+(s3~?t1))\
          (Fc 2 n (<|s2,s3|>)~?Fc 2 n (<|t0,t1|>))); simpl.
  repeat split~; intros. apply equ_sys_C1; trivial. 
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply H2; trivial.
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply H3; trivial.
  clear H10.
  exists (c0,s0,(p0|+(s2~?t1)|+(s3~?t0))\
          (Fc 2 n (<|s2,s3|>)~?Fc 2 n (<|t0,t1|>))); simpl.
  repeat split~; intros. apply equ_sys_C2; trivial. 
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply H2; trivial.
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply H3; trivial.
  
  (* equ_sys_C2 *)
  generalize H6; intro H6'.
  apply H3 in H6'. simpl in H6'. inverts H6'.
  destruct H8. simpl in H0. omega. destruct H0. false.
  simpl in H5. destruct H5; apply H5; trivial.   
  exists (c0,s0,(p0|+(s2~?t0)|+(s3~?t1))\
          (Fc 2 n (<|s2,s3|>)~?Fc 2 n (<|t0,t1|>))); simpl.
  repeat split~; intros. apply equ_sys_C1; trivial. 
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply H2; trivial.
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply H3; trivial.
  clear H10.
  exists (c0,s0,(p0|+(s2~?t1)|+(s3~?t0))\
          (Fc 2 n (<|s2,s3|>)~?Fc 2 n (<|t0,t1|>))); simpl.
  repeat split~; intros. apply equ_sys_C2; trivial. 
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply H2; trivial.
  apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply set_add_elim in H0. destruct H0. inverts H0; trivial.
  apply H3; trivial.

  (* equ_sys_Ab1 *)
  exists (c0,s0,(p0|+(t~?t'))\(([a]^t)~?([a]^t'))); simpl.
  repeat split~; intros.  
  apply equ_sys_Ab1; trivial.
  apply H2. apply set_remove_1 in H0.     
  apply set_add_elim in H0. destruct H0; trivial. inverts H0.
  assert (Q : c1 |- ([a]^ t)|^s1 ~c (([a]^ t')|^s1)).
   apply H3; trivial.
  apply set_remove_1 in H0. apply set_add_elim in H0.
  destruct H0. inverts H0. inverts Q; trivial. false.
  apply H3; trivial.
  
  (* equ_sys_Ab2 *) 
  exists (c0,s0,((p0|+(t~?([(a,b)]@t'))|+(a#?t')))\(([a]^t)~?([b]^t'))); simpl.
  repeat split~; intros.  
  apply equ_sys_Ab2; trivial.
  apply set_remove_1 in H0.
  assert (Q : c1 |- ([a]^ t)|^s1 ~c (([b]^ t')|^s1)).
   apply H3; trivial.  
  apply set_add_elim in H0. destruct H0. inverts H0.
  inverts Q. false. trivial. 
  apply set_add_elim in H0. destruct H0. inverts H0.
  apply H2; trivial.
  assert (Q : c1 |- ([a]^ t)|^s1 ~c (([b]^ t')|^s1)).
   apply H3; trivial.
  apply set_remove_1 in H0. apply set_add_elim in H0.
  destruct H0. inverts H0. apply set_add_elim in H0.
  destruct H0. inverts H0. inverts Q. false.
  rewrite subst_perm_comm. trivial.
  apply H3; trivial.


  (* equ_sys_inst *)
  gen_eq s' : (s©([(X,(!pi)@t)])); intro H11.
  exists (c0,s',((p0\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))\cup(c0/?s')); simpl.
  repeat split~; intros.  
  apply equ_sys_inst; trivial.
 
  case H4; clear H4; intros s2 H4. 
  
  assert (Q0 : c1 |- (pi|.X)|^s1 ~c (t|^s1)).
   destruct H12. apply H3; trivial.
   apply c_equiv_sym. apply H3; trivial.
   
  apply c_equiv_unif in Q0.
   
  apply set_union_elim in H0. destruct H0.
  apply set_In_subs_remove_problem in H0.
  apply set_In_subs_remove_problem in H0.
  apply set_In_subs in H0. case H0; clear H0; intros u H0.
  destruct H0. destruct u; simpl in H; inverts H0.

  rewrite <- subst_comp_expand.
  apply c_equiv_unif_fresh with (S1:=s1).
  apply subst_sym; trivial. apply H2; trivial.

  unfold fresh_env in H2.
  apply set_In_subs_fresh_constraints in H0.
  case H0; clear H0; intros Y H0. destruct H0.
  apply H1 in H0. rewrite H5. rewrite H11. clear H1 H2 H3 H5 H12.
  rewrite subst_comp_expand.
  rewrite <- subst_comp_expand with (t:= (([])|.Y)|^ s).
  apply c_equiv_unif_fresh with (S1:=s1). apply subst_sym; trivial.
  rewrite <- subst_comp_expand.
  apply c_equiv_unif_fresh with (S1:=s1); trivial.
  
  apply subst_trans with (S2:= s © s2). 
  apply subst_sym; trivial.
  apply subst_trans with (S2:= s © s © s2).
  apply subst_sym. apply subst_idem. apply H.
  apply subst_assoc. apply subst_cancel_left; trivial.

  case H4; clear H4; intros s2 H4.
  
  assert (Q0 : c1 |- (pi|.X)|^s1 ~c (t|^s1)).
   destruct H12. apply H3; trivial.
   apply c_equiv_sym. apply H3; trivial.

  apply c_equiv_unif in Q0.
   
  apply set_union_elim in H0. destruct H0.
  apply set_In_subs_remove_problem in H0.
  apply set_In_subs_remove_problem in H0.
  apply set_In_subs in H0. case H0; clear H0; intros u H0.
  destruct H0. destruct u; simpl in H0; inverts H0.  
  
  rewrite <- 2 subst_comp_expand.
  apply c_equiv_unif_2 with (S1:=s1).
  apply subst_sym; trivial. apply H3; trivial.

  apply equ_subs_fresh in H0. contradiction.
 
  case H4; clear H4; intros s2 H4.

  assert (Q0 : c1 |- (pi|.X)|^s1 ~c (t|^s1)).
   destruct H12. apply H3; trivial.
   apply c_equiv_sym. apply H3; trivial.

  apply c_equiv_unif in Q0.

  exists s1. rewrite H11.
  apply subst_trans with (S2 := s © s1).
  apply subst_assoc.
  apply subst_cancel_left; trivial.
  apply subst_trans with (S2 := s © (s © s2)). 
  apply subst_cancel_left.
  apply subst_sym; trivial.
  apply subst_trans with (S2 := s © s2); trivial.
  apply subst_assoc. apply subst_idem. apply H.


  (* equ_sys_inv *)
  exists (c0,s0,(p0|+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X))); simpl.
  repeat split~; intros.  
  apply equ_sys_inv; trivial.
  apply H2. apply set_remove_1 in H0.
  apply set_add_elim in H0. destruct H0; trivial. inverts H0.
  apply set_remove_1 in H0. apply set_add_elim in H0.
  destruct H0. inverts H0.
  replace (pi ++ (! pi')|.X) with (pi ++ (! pi') @ ([]|.X)).
  rewrite <- perm_comp. apply c_equiv_sym.
  rewrite subst_perm_comm. apply -> c_equiv_pi_inv_side.
  apply c_equiv_sym. rewrite <- subst_perm_comm.     
  autorewrite with perm. simpl app. apply H3; trivial.
  autorewrite with perm. simpl. trivial.
  apply H3; trivial.
  
  case H1; clear H1; intros T'' H1. destruct H1.
  apply equ_sol_preserv with (T':=T'') (varSet:=varSet); trivial.
  
Qed.




(**  %\section{ Completeness of unif\_step }% *) 
(**
	If T is a valid triple and it is not a leaf,
	then Sl is a solution for T if, and only if, there exists a triple T' such
	that T reduces to T', by a unif_step, and Sl is also a solution for T'. 
	The proof is done by case analysis on the possible reductions from T,
	and uses lemmas fresh_sys_compl, equ_sys_compl and unif_step_preserv. 
*)


Lemma unif_step_compl : forall T Sl varSet,
      valid_triple T ->
      ~ leaf varSet T ->
      (sol_c Sl T  <-> (exists T', unif_step varSet T T' /\ sol_c Sl T')).
Proof.
  intros. split~; intro.
  
  apply unif_step_neg_NF in H0.
  case H0; clear H0; intros T0 H0. inverts H0.
  assert (Q : ~ NF _ (equ_sys varSet) T).
   apply equ_sys_neg_NF. exists T0; trivial.
  apply equ_sys_compl with (Sl := Sl) in Q; trivial.  
  apply Q in H1. case H1; clear H1; intros T1 H1. destruct H1.
  exists T1. split~. apply equ_unif_step; trivial.
  generalize H3; intro H3'.
  apply fresh_sys_compl with (Sl:=Sl) in H3'.
  exists T0. split~. apply fresh_unif_step; trivial.
  apply H3'; trivial.
 
  case H1; clear H1; intros T' H1.
  destruct H1. apply unif_step_preserv with (Sl:=Sl) in H1; trivial.
  
Qed.



(** %\section{ Completeness of unif\_path }% *) 
(**
    This is the main result of this file. It establishes 
    that the set of solutions for a triple T is equal to the set of 
    solutions of the successful leaves. These leaves are gererated
    by the application of the C-unification algorithm to T.

    Formally: Sl is a solution for T, a valid triple, if and only if 
    there exists a unification path form T to T', with Sl 
    being also a solution for T'. The proof is done by well-founded 
    induction in the unif_step_order, and it uses Theorem c_unif_soundness 
    and Lemma unif_step_compl.		
*)

Theorem unif_path_compl : forall T Sl varSet,
        valid_triple T ->  
        (sol_c Sl T <-> exists T', unif_path varSet T T' /\ sol_c Sl T').
Proof.
  intros. split~; intro. gen T. intro T.  
  apply well_founded_ind with (R := unif_step_order varSet) (a := T).  
  apply unif_step_order_wf.

  intros T0 H0 H1 H2. unfold unif_step_order in H0. 
  case (unif_step_NF_dec T0) with (varSet:=varSet); intro H3. 

  exists T0. split~. unfold unif_path. split~. apply tr_rf.

  apply unif_step_neg_NF in H3. 
  apply unif_step_compl with (Sl := Sl) in H3; trivial.
  generalize H2; intro H2'. apply H3 in H2'.
  clear H3. case H2'; clear H2'; intros T1 H2'.
  destruct H2'. generalize H. intro H'.
  apply H0 in H'; trivial.
  case H'; clear H'; intros T2 H'. destruct H'. destruct H4.
  exists T2. split~. split~.
  apply tr_ms with (t := T1); trivial.
  apply unif_step_valid_preserv with (T:=T0) (varSet:=varSet); trivial.

  case H0; clear H0; intros T' H0. destruct H0.
  apply c_unif_path_soundness with (Sl:=Sl) in H0; trivial.
Qed.
