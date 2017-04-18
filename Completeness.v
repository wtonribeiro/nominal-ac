(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Completeness.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: April 1st, 2017.
 ============================================================================
*)

Require Export Soundness.

Lemma equ_sol_compl  : forall T T' Sl,
                        valid_triplet T -> equ_sys T T' ->
                        (sol_c Sl T  <->
                        (exists T'', equ_sys T T'' /\ sol_c Sl T'')).

Proof.
  intros. split~; intro. 
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
  destruct H8. simpl in H0. omega. destruct H0. false. clear H10.  
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
  destruct H8. simpl in H0. omega. destruct H0. false. clear H10.  
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

  gen_eq s' : (s©([(X,(!pi)@t)])); intro H10.
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
  destruct H0. destruct u; simpl in H0; inverts H0.

  rewrite <- subst_comp_expand.
  apply c_equiv_unif_fresh with (S1:=s1).
  apply subst_sym; trivial. apply H2; trivial.

  unfold fresh_env in H1.
  apply set_In_subs_fresh_constraints in H0.
  case H0; clear H0; intros Y H0. destruct H0.
  apply H1 in H0. rewrite H5. rewrite H10. clear H1 H2 H3 H5 H12.
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

  exists s1. rewrite H10.
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
  apply equ_sol_preserv with (T':=T''); trivial.
  
Qed.


Lemma unif_step_compl  : forall T T' Sl,
                         valid_triplet T -> unif_step T T' ->
                        (sol_c Sl T  <->
                        (exists T'', unif_step T T'' /\ sol_c Sl T'')).
Proof.
  intros. split~; intros. destruct H0. 
  apply equ_sol_compl with (Sl:=Sl) in H0; trivial.
  apply H0 in H1. case H1; clear H1; intros T'' H1.
  exists T''. destruct H1. split~. apply equ_unif_step; trivial.
  exists T'. split~. apply fresh_unif_step; trivial.
  apply fresh_sys_compl with (Sl:=Sl) in H2; trivial. apply H2; trivial.
  case H1; clear H1; intros T'' H1. destruct H1. destruct H1.
  apply equ_sol_preserv with (T':=T'0); trivial.  
  apply fresh_sys_compl with (Sl:=Sl) in H3; trivial. apply H3; trivial.
Qed.  