(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Soundness.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: April 1st, 2017.
 ============================================================================
*)

Require Export Termination.

(** Characterisation of successful leaves *)   
  

Lemma NF_equ_sys : forall C S s t P,
                     
            Proper_Problem P ->
            set_In (s ~? t) P ->
            NF _ equ_sys (C, S, P) ->
            
            ((forall pi X, t <> pi|.X) /\
              ((s = (<<>>) /\ t <> (<<>>)) \/
              (exists a, s = (%a) /\ t <> (%a))  \/
              (exists E, exists n, exists u, s = (Fc E n u) /\ forall v, t <> (Fc E n v)) \/
              (exists a, exists u, s = [a]^u /\ forall b v, t <> [b]^v) \/
              (exists u, exists v, s = (<|u,v|>) /\ forall u' v', t <> (<|u',v'|>))  \/
              (exists pi, exists X, s = pi|.X /\ set_In X (term_vars t)))) \/
            
            ((forall pi X, s <> pi|.X) /\ (exists pi, exists X, t = pi|.X /\
                                                                set_In X (term_vars s))) \/
                                    
            (fixpoint_equ (s ~? t)) .
Proof.
  intros. destruct s. destruct t.
  false. apply (H1 (C,S,P\((<<>>) ~? (<<>>)))).
  apply equ_sys_refl; trivial.
  left~. split~; intros. discriminate. left~. split~. discriminate.
  left~. split~; intros. discriminate. left~. split~. discriminate.  
  left~. split~; intros. discriminate. left~. split~. discriminate.
  left~. split~; intros. discriminate. left~. split~. discriminate.
  false. gen_eq S' : (S © ([(v,(!p) @ (<<>>))])); intro H'.
  apply (H1 (C,S',(P\((p|.v) ~? (<<>>)))\((<<>>) ~? (p|.v))|^^([(v,(!p) @ (<<>>))])\cup(C/?S'))).
  apply equ_sys_inst; trivial.
  simpl. intro; trivial. right~. 
  destruct t.
  left~. split~; intros. discriminate. right~. left~. exists a. split~. discriminate.
  case (a ==at a0); intro H'. rewrite H' in H0. clear H'.
  false. apply (H1 (C,S,P\((%a0) ~? (%a0)))).
  apply equ_sys_refl; trivial. 
  left~. split~; intros. discriminate.
  right~. left~. exists a. split~.
  intro H2. inverts H2. apply H'; trivial.
  left~. split~; intros. discriminate. right~. left~. exists a. split~. discriminate.
  left~. split~; intros. discriminate. right~. left~. exists a. split~. discriminate.
  left~. split~; intros. discriminate. right~. left~. exists a. split~. discriminate.
  false. gen_eq S' : (S © ([(v,(!p) @ (%a))])); intro H'.
  apply (H1 (C,S',(P\((p|.v) ~? (%a)))\((%a) ~? (p|.v))|^^([(v,(!p) @ (%a))])\cup(C/?S'))).
  apply equ_sys_inst; trivial.
  simpl. intro; trivial. right~.
  destruct t.
  left~. split~; intros. discriminate.
  right~. right~. right~. left~. exists a. exists s. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. right~. left~. exists a. exists s. split~; intros. discriminate. 
  false. case (a ==at a0); intro H'. rewrite H' in H0. clear H'.
  apply (H1 (C,S,P|+(s ~? t)\(([a0]^s) ~? ([a0]^t)))).
  apply equ_sys_Ab1; trivial. 
  apply (H1 (C,S,((P|+(s~?([(a,a0)]@t))|+(a#?t)))\(([a]^s)~?([a0]^t)))).
  apply equ_sys_Ab2; trivial. 
  left~. split~; intros. discriminate.
  right~. right~. right~. left~. exists a. exists s. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. right~. left~. exists a. exists s. split~; intros. discriminate.  
  case (set_In_dec Var_eqdec v (term_vars s)); intro H'.
  right~. left~. split~; intros. discriminate. exists p. exists v. simpl. split~.
  false. gen_eq S' : (S © ([(v,(!p) @ ([a]^s))])); intro H''.
  apply (H1 (C,S',(P\((p|.v) ~? ([a]^s)))\(([a]^s) ~? (p|.v))|^^([(v,(!p) @ ([a]^s))])\cup(C/?S'))).
  apply equ_sys_inst; trivial. right~.    
  destruct t.
  left~. split~; intros. discriminate.
  right~. right~. right~. right~.  left~. exists s1. exists s2. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. right~. right~. left~. exists s1. exists s2. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. right~. right~. left~. exists s1. exists s2. split~; intros. discriminate.
  false. apply (H1 (C,S,((P|+(s1~?t1)|+(s2~?t2)))\((<|s1,s2|>) ~? (<|t1,t2|>)))). 
  apply equ_sys_Pr; trivial. 
  left~. split~; intros. discriminate.
  right~. right~. right~. right~. left~. exists s1. exists s2. split~; intros. discriminate.
  right~. case (set_In_dec Var_eqdec v (term_vars (<|s1,s2|>))); intro H'.
  left~. split~; intros. discriminate.
  exists p. exists v. split~.
  false. gen_eq S' : (S © ([(v,(!p) @ (<|s1,s2|>))])); intro H''.
  apply (H1 (C,S',(P\((p|.v) ~? (<|s1,s2|>)))\((<|s1,s2|>) ~?
                  (p|.v))|^^([(v,(!p) @ (<|s1,s2|>))])\cup(C/?S'))).
  apply equ_sys_inst; trivial.
  right~.
  destruct t.  
  left~. split~; intros. discriminate.
  right~. right~. left~. exists n. exists n0. exists s. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. left~. exists n. exists n0. exists s. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. left~. exists n. exists n0. exists s. split~; intros. discriminate.
  left~. split~; intros. discriminate.
  right~. right~. left~. exists n. exists n0. exists s. split~; intros. discriminate.
  case (eq_nat_dec n n1); intro H2. case (eq_nat_dec n0 n2); intro H3.
  rewrite H2 in *|-*. rewrite H3 in *|-*.
  clear H2 H3. case (eq_nat_dec n1 2); intro H2.
  rewrite H2 in *|-*; clear H2.
  assert (Q : is_Pr s /\ is_Pr t).
   apply H in H0. destruct H0.
   unfold Proper_term in H0.
   unfold Proper_term in H2.
   split~.
   apply H0 with (n:=n2).
   apply In_subterms.
   apply H2 with (n:=n2).
   apply In_subterms.
   destruct Q.  
  apply is_Pr_exists in H2.
  apply is_Pr_exists in H3.
  case H2; clear H2; intros s0 H2.
  case H2; clear H2; intros s1 H2.
  case H3; clear H3; intros t0 H3.
  case H3; clear H3; intros t1 H3.
  rewrite H2 in *|-*. rewrite H3 in *|-*. clear H2 H3.
  false. apply (H1 (C,S,((P|+(s0 ~? t0))|+(s1 ~? t1))\
                        ((Fc 2 n2 (<|s0,s1|>))~?(Fc 2 n2 (<|t0,t1|>))))).
  apply equ_sys_C1; trivial.
  false. apply (H1 (C,S,(P|+(s ~? t))\((Fc n1 n2 s)~?(Fc n1 n2 t)))).
  apply equ_sys_Fc; trivial.
  left~. split~; intros. discriminate.
  right~. right~. left~. exists n. exists n0. exists s. split~.
  intros v H4. inverts H4. apply H3; trivial.
  left~. split~; intros. discriminate.
  right~. right~. left~. exists n. exists n0. exists s. split~.
  intros v H4. inverts H4. apply H2; trivial.
  case (set_In_dec Var_eqdec v (term_vars s)); intro H'.
  right~. left~. split~; intros. discriminate. exists p. exists v. simpl. split~.
  false. gen_eq S' : (S © ([(v,(!p) @ (Fc n n0 s))])); intro H''.
  apply (H1 (C,S',(P\((p|.v) ~? (Fc n n0 s)))\((Fc n n0 s) ~?
            (p|.v))|^^([(v,(!p) @ (Fc n n0 s))])\cup(C/?S'))).
  apply equ_sys_inst; trivial.
  right~. 
  case (set_In_dec Var_eqdec v (term_vars t)); intro H'.
  destruct t; simpl in H'; try contradiction. 
  left~. split~; intros. discriminate.
  right~. right~. right~. right~. right~. 
  exists p. exists v. simpl. split~.
  left~. split~; intros. discriminate.
  right~. right~. right~. right~. right~. 
  exists p. exists v. simpl. split~.
  left~. split~; intros. discriminate.
  right~. right~. right~. right~. right~. 
  exists p. exists v. simpl. split~.
  destruct H'; try contradiction. rewrite H2 in *|-*. clear H2.
  case (Perm_eqdec p p0); intro H2. rewrite H2 in *|-*.
  false. apply (H1 (C,S,P\((p0|.v) ~? (p0|.v)))).
  apply equ_sys_refl; trivial.   
  case (Perm_eqdec p0 ([])); intro H3.
  right~. right~. rewrite H3. unfold fixpoint_equ.
  exists p. exists v. split~. rewrite <- H3; trivial.
  false. apply (H1 (C,S,(P|+((p++(!p0))|.v~?([]|.v)))\((p|.v)~?(p0|.v)))).
  apply equ_sys_inv; trivial.    
  false. gen_eq S' : (S © ([(v,(!p) @ t)])); intro H''.
  apply (H1 (C,S',(P\((p|.v) ~? t))\(t ~? (p|.v))|^^([(v,(!p) @ t)])\cup(C/?S'))).
  apply equ_sys_inst; trivial.
  left~. 
Qed.


Lemma NF_successful_equ: forall C S P s t,
                           Proper_Problem P ->
                           set_In (s ~? t) P -> 
                           NF _ equ_sys (C, S, P) -> (exists Sl, sol_c Sl (C, S, P)) -> fixpoint_equ (s ~? t).  
Proof.
  intros. case H2; clear H2; intros Sl H2. unfold sol_c in H2.
  destruct H2. destruct H3. destruct H4. simpl fst in *|-. simpl snd in *|-.
  apply NF_equ_sys with (s:=s) (t:=t) in H1; trivial. destruct H1. destruct H1.
  destruct H6. destruct H6.
  assert (Q : fst Sl |- (<<>>) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial.
  inverts Q. false. apply H7.
  destruct t; simpl in H9; inverts H9; trivial. false.   
  destruct H6. case H6; clear H6; intros a H6. destruct H6.   
  assert (Q : fst Sl |- (%a) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial. 
  inverts Q. false. apply H7.
  destruct t; simpl in H11; inverts H11; trivial. false. 
  destruct H6. case H6; clear H6; intros E H6.
  case H6; clear H6; intros n H6.
  case H6; clear H6; intros u H6. destruct H6.  
  assert (Q : fst Sl |- (Fc E n u) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial. 
  inverts Q. destruct t; simpl in H13; inverts H13; trivial.
  false. false. simpl in H13. omega. simpl in H13. omega.
  destruct t; simpl in H12; inverts H12. false. false.
  destruct t; simpl in H12; inverts H12. false. false.  
  destruct H6. 
  case H6; clear H6; intros a H6.
  case H6; clear H6; intros u H6. destruct H6.  
  assert (Q : fst Sl |- ([a]^u) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial. 
  inverts Q. destruct t; simpl in H12; inverts H12;
   trivial. false. false. destruct t; inverts H10. false. false.
  destruct H6.
  case H6; clear H6; intros u H6.
  case H6; clear H6; intros v H6. destruct H6.
  assert (Q : fst Sl |- (<|u,v|>) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial. 
  inverts Q. destruct t; simpl in H11; inverts H11;
   trivial. false. false.
  case H6; clear H6; intros pi H6.
  case H6; clear H6; intros X H6. destruct H6.
  assert (Q : fst Sl |- (pi|.X) |^ snd Sl ~c (t |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial.
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
  intros. intro H8. destruct t;
    autorewrite with perm in H8; inverts H8. false.
  destruct H1; trivial. destruct H1.
  case H6; clear H6; intros pi H6.
  case H6; clear H6; intros X H6. destruct H6.
  assert (Q : fst Sl |- s |^ snd Sl ~c ((pi|.X) |^ snd Sl)). 
   rewrite <- H6. apply H4; trivial.
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
  intros. intro H8. destruct s;
    autorewrite with perm in H8; inverts H8. false.
Qed.



Lemma leaf_fresh_sys : forall a s C S P,
                       set_In (a#?s) P -> leaf (C,S,P) -> fixpoint_Problem (equ_proj P) -> s = %a.
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

  
Lemma successful_leaves_ch : forall T,
                               Proper_Problem (snd T) ->
                               (leaf T /\ exists Sl, (sol_c Sl T)) ->
                               (fixpoint_Problem (snd T)).
Proof.
  intros. destruct H0. destruct T. destruct p. simpl.
  
  assert (Q : fixpoint_Problem (equ_proj p0)).
   apply set_In_fixpoint_eq_proj; intros.   
   apply NF_successful_equ with (C:=c) (S:=s) (P:=p0); trivial.
   unfold leaf in H0. unfold NF in *|-*.
   intros T H3. apply (H0 T). apply equ_unif_step; trivial.

  unfold fixpoint_Problem; intros. destruct u.

  case H1; clear H1; intros Sl H1. unfold sol_c in H1.  
  destruct H1. destruct H3.
  apply leaf_fresh_sys with (a:=a) (s:=t) in H0; trivial.    
  assert (Q': fst Sl |- a # ((%a) |^ snd Sl)).  
   apply H3. simpl. rewrite <- H0. trivial.
  simpl in Q'. inverts Q'. false.
   
  apply NF_successful_equ with (C:=c) (S:=s) (P:=p0); trivial.
  unfold leaf in H0. unfold NF in *|-*.
  intros T H3. apply (H0 T).   
  apply equ_unif_step; trivial.
Qed.    


(** Towards soundness and completeness proofs *)

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
    

Lemma equ_sol_preserv : forall T T' Sl, valid_triplet T ->
                                        equ_sys T T' -> sol_c Sl T' -> sol_c Sl T .
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
  unfold valid_triplet in H. simpl in H. destruct H.
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
  rewrite H2 in H1. rewrite perm_term_vars in H1. contradiction.
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
  unfold valid_triplet in H; simpl in H. destruct H.
  
  case (Constraint_eqdec (s0~?t0) ((pi|.X)~?t)); intro H6. inverts H6.

  apply c_equiv_unif_2 with (S1:=(s©([(X,(!pi) @ t)]))©s2); trivial.
  rewrite 4 subst_comp_expand.
  rewrite not_In_dom. rewrite subst_var_eq.
  rewrite inter_dom_term_vars with (t:= t).
  rewrite not_occurs; trivial.
  rewrite 2 subst_perm_comm.
  apply c_equiv_pi_inv_side. apply c_equiv_refl.
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
  rewrite perm_term_vars in H0. contradiction.

  clear Q.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_elim in H0. destruct H0.
  apply var_in_dom_rec_singleton in H1.
  rewrite H1 in H0. apply In_im_subst_term in H0.
  rewrite perm_term_vars in H0. contradiction.

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


Lemma c_unif_path_preserv : forall T T' Sl, valid_triplet T ->
                                            unif_path T T' -> sol_c Sl T' -> sol_c Sl T.
Proof.
  intros. destruct H0.
  induction H0; trivial. destruct H0.
  apply equ_sol_preserv with (T':= T'); trivial.
  apply fresh_sys_compl with (Sl:=Sl) in H3.
  apply H3; trivial. destruct H0.
  apply equ_sol_preserv with (T':= T'); trivial. 
  apply IHtr_clos; trivial.
  apply equ_valid_preservation with (T:= T); trivial.
  generalize H4; intro H4'.
  apply fresh_sys_compl with (Sl:=Sl) in H4.
  apply H4. apply IHtr_clos; trivial. 
  apply fresh_valid_preservation with (T:= T); trivial.
Qed.


Theorem c_unif_soundness : forall T T' Sl,
                             Proper_Problem (snd T) ->
                             valid_triplet T ->
                             unif_path T T' -> sol_c Sl T' ->
                             (sol_c Sl T /\ fixpoint_Problem (snd T')).
Proof.
  intros. split~.
  apply c_unif_path_preserv with (T':= T'); trivial.
  apply successful_leaves_ch.
  apply unif_path_Proper_Problem with (T:=T); trivial.
  split~.
  destruct H1; trivial.
  exists Sl; trivial.
Qed.



