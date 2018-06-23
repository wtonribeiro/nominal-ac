(**
%\begin{verbatim}
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : C-Matching.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : The specification of nominal C-matching and
               the formalisation of its properties of 
               termination, soundness and completess are
               the contributions of this file.
 
 Last Modified On: Jun 23, 2018.
 ============================================================================
 \end{verbatim} %
*)

Require Import C_Unif_Completeness.


(** Definition of a solution for a matching problem *)

Definition match_sol (Sl : Context * Subst) (T : Triple) :=
  let C' := (fst Sl) in
  let S' := (snd Sl) in
  let C := (fst (fst T)) in
  let S := (snd (fst T)) in
  let P := (snd T) in
  
  (* 1 *) ( fresh_env C C' S' ) /\         
  (* 2 *) ( forall a s, set_In (a#?s) P -> C' |- a # (s|^S') ) /\
  (* 3 *) ( forall s t, set_In (s~?t) P -> C' |- (s|^S') ~c t ) /\         
  (* 4 *) ( exists S'', C' |- (S©S'') ~:c S' ) /\
  (* 5 *)  set_inter Var_eqdec (rhvars_Probl P) (dom_rec S') = [] 
. 


(* C-matching system, step and path definitions *)

Inductive match_step : Triple -> Triple -> Prop :=
  
| match_to_unif_step : forall T T', unif_step (rhvars_Probl (snd T)) T T' -> match_step T T'

| match_fixpoint : forall C C' S P pi X,

                   fixpoint_Problem P ->

                   pi <> [] ->

                   set_In (pi|.X~?([]|.X)) P ->
    
                   C' =  set_union Context_eqdec C (fresh_context (dom_perm pi) X) ->
                     
                   match_step (C, S, P) (C', S, P\(pi|.X~?([]|.X)))
.
                                                                                 
 
Definition match_leaf (T : Triple) := NF _ match_step T .  

Definition match_path  (T T' : Triple) := tr_clos _ match_step T T' /\ match_leaf T'.


(** Termination of match_step *)

Lemma match_step_termination : forall T T', match_step T T' -> T' <<* T .
Proof.
  intros. inverts H.
  apply unif_step_termination in H0; trivial.
  
  unfold unif_step_size_order. 
  unfold Quadruple_order.
  unfold Problem_measure. simpl.

  right~. left~. split~. 
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H. 
  apply Problem_vars_remove in H; trivial.
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P >= equ_Problem_size ([(pi|.X)~?(([])|.X)])).
   apply equ_Problem_size_neq_nil; trivial.
  assert (Q' : equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=pi|.X) (t:=([])|.X); trivial. 
  simpl in *|-*. omega.
Qed.


(* If the intersection between the right-hand variables and the domain of a substituion
   of a solution is the empty set, then Sl is a solution for T as a unification problem if, 
   and only if, it is a solution for T as matching problem *)

Lemma unif_match_sol_equiv : forall T Sl,
      
      set_inter Var_eqdec (rhvars_Probl (snd T)) (dom_rec (snd Sl)) = [] ->

      sol_c Sl T <-> match_sol Sl T.

Proof.
  intros. unfold sol_c. unfold match_sol.

  split~; intro.

  destruct H0. destruct H1. destruct H2.
  repeat split~; intros; trivial.
  rewrite <- inter_dom_term_vars with (t:=t) (S:= snd Sl).
  apply H2; trivial. apply set_inter_nil. intros X H5.
  apply set_inter_nil with (a:=X) in H.
  apply H; clear H. apply set_inter_elim in H5.
  destruct H5. apply set_inter_intro; trivial.
  apply rh_term_Probl_vars with (X:=X) in H4; trivial.

  destruct H0. destruct H1. destruct H2. destruct H3. 
  repeat split~; intros; trivial.
  rewrite inter_dom_term_vars with (t:=t).
  apply H2; trivial. apply set_inter_nil. intros X H6.
  apply set_inter_nil with (a:=X) in H.
  apply H; clear H. apply set_inter_elim in H6.
  destruct H6. apply set_inter_intro; trivial.
  apply rh_term_Probl_vars with (X:=X) in H5; trivial.
Qed.


(** Reductions by match_step do not change 
    the set of right-hand side variables *)

Lemma match_step_rh_vars : forall T T',                     
      match_step T T' ->
      ( forall X,  set_In X (rhvars_Probl (snd T')) -> set_In X (rhvars_Probl (snd T) )).
Proof.
  intros. inverts H. inverts H1.

  inverts H; simpl in *|-*;
    try apply rhvars_Prob_rem in H0; trivial;
    try  apply rhvars_Prob_rem in H0;
    try apply rhvars_Prob_add in H0;
    try destruct H0;
    try apply rhvars_Prob_add in H; simpl in *|-;
    try destruct H; trivial;
    try rewrite perm_term_vars in *|-; 
    try apply rh_term_Probl_vars with (X:=X) in H1;
    try apply rh_term_Probl_vars with (X:=X) in H2;
    trivial; simpl; 
    try apply set_union_intro; auto.

    destruct H2.
    apply rhvars_Prob_union in H0.
    destruct H0. apply rhvars_Prob_subs in H0.
    apply rhvars_Prob_rem in H0. apply rhvars_Prob_rem in H0. trivial.
    intro H2. apply rhvars_Prob_rem in H2. apply rhvars_Prob_rem in H2.
    apply H1. apply set_union_intro2; trivial.
    apply rhvars_Prob_fresh in H0. contradiction. 
    apply rh_term_Probl_vars with (X:=X0) in H.
    false. apply H1. apply set_union_intro2; trivial.   
    simpl. left~.
    
    rewrite H in *|-*.
    apply rh_term_Probl_vars with (X:=X) in H3; trivial.
    simpl. left~.

    contradiction.
  
  inverts H2; simpl in *|-*;
  try apply rhvars_Prob_rem in H0; trivial; 
  try apply rhvars_Prob_add in H0; try destruct H0; trivial;
  simpl in H0; try contradiction.
  apply rhvars_Prob_add in H0. destruct H0; trivial.
  simpl in H0. contradiction. 
   
  simpl. apply rhvars_Prob_rem in H0; trivial. 

Qed.

(** A corollary of previous lemma is that if the 
    intersection between the right-hand variables of T
    and a given set St is empty and T reduces to T'
    by match_step, then intersection between 
    the right-hand variables of T' and St is also
    empty.
*)

Corollary match_step_rh_inter_empty : forall T T' St ,

      set_inter Var_eqdec (rhvars_Probl (snd T)) St = [] ->
      
      match_step T T' ->

      set_inter Var_eqdec (rhvars_Probl (snd T')) St = [] .
Proof.
  intros. apply set_inter_nil; intros X H1.
  apply set_inter_elim in H1. destruct H1.
  apply set_inter_nil with (a:=X) in H.
  apply H. apply set_inter_intro; trivial.
  apply match_step_rh_vars with (X:=X) in H0; trivial.
Qed.



(** Soundness and completeness of the match_step relation *)


(**
  Let T T' triples e Sl = < C, S > a matching solution for T'
  such that the intersection between the right-hand variables
  of T and the domain of S is empty, and T reduces to T' by match_step. 
  In this case Sl is also a matching solution for T. 
*)

Lemma match_step_preserv : forall Sl T T',

      valid_triple T ->

      set_inter Var_eqdec (rhvars_Probl (snd T)) (dom_rec (snd Sl)) = [] ->

      match_step T T' ->

      match_sol Sl T' -> match_sol Sl T .

Proof.
  intros. inverts H1.

  assert (Q : set_inter Var_eqdec (rhvars_Probl (snd T')) (dom_rec (snd Sl)) = []).
  unfold match_sol in H2. apply H2.
  
  apply unif_match_sol_equiv; trivial.
  apply unif_match_sol_equiv in H2; trivial.
  apply unif_step_preserv with (Sl:=Sl) in H3; trivial.


  unfold match_sol in *|-*. simpl in *|-*.
  destruct H2. destruct H2. destruct H6. destruct H7.
  repeat split~; intros.

  unfold fresh_env in *|-*; intros.
  apply H1. apply set_union_intro1; trivial.

  apply H2. apply set_remove_3; trivial.
  discriminate.

  case (Constraint_eqdec (s~?t) ((pi|.X)~?(([])|.X))); intro H10.
  inverts H10.

  assert (Q : set_inter Var_eqdec ([X]) (dom_rec (snd Sl)) = []).

   apply set_inter_nil. intros Y H11.  
   apply set_inter_nil with (a:=Y) in H0.
   apply H0. apply set_inter_elim in H11. destruct H11.
   apply set_inter_intro; trivial.
   apply rh_term_Probl_vars with (X:=X) in H9. 
   simpl in H10. destruct H10; try contradiction.
   rewrite <- H10; trivial.
   simpl. left~.
   
  rewrite inter_dom_term_vars.
  apply equiv_Su; intros.  
  unfold fresh_env in H1.
  assert (Q': fst Sl |- a # []|.X).
   rewrite <- inter_dom_term_vars with (t:=[]|.X) (S:=snd Sl).
   apply H1. apply set_union_intro2.
   apply fresh_context_mem. split~.
   replace (dom_perm pi) with (disgr pi ([])).
   apply ds_eq_disgr; trivial.
   unfold disgr. simpl.
   rewrite app_nil_r; trivial.
   simpl; trivial.
  inverts Q'. simpl in H14; trivial.
  simpl; trivial.
   
  apply H6. apply set_remove_3; trivial.
 
Qed.
  
(** For every triple T, is possible to decide either if 
    T is a matching leaf or there exists a T' such that  
    T reduces to T' by match_step *)

Lemma match_step_NF_dec : forall T,
      match_leaf T \/ exists T', match_step T T'.
Proof.
  intros. case (unif_step_NF_dec T) with
          (varSet := rhvars_Probl (snd T)); intro H.
  case (fixpoint_Problem_eqdec (snd T)); intro H0.
  
  generalize H0. intro H0'. destruct T. destruct p.
  simpl in *|-.
  unfold fixpoint_Problem in H0. destruct p0.
  left~.
  intros T' H2. inverts H2.
  simpl in H1.
  inverts H1. inverts H2; simpl in *|-; trivial.
  destruct H7; trivial.
  inverts H3; simpl in *|-; trivial.
  simpl in H8; trivial. 
  right~.
  assert (Q : fixpoint_equ c0).
   apply H0. left~.
  unfold fixpoint_equ in Q.
  case Q; clear Q; intros pi Q.
  case Q; clear Q; intros X Q.
  destruct Q.
  exists (set_union Context_eqdec c (fresh_context (dom_perm pi) X),  s, (c0::p0)\c0).
  rewrite H2. apply match_fixpoint; trivial.
  rewrite <- H2. trivial.
  left~.

  left~. intros T' H'. inverts H'.
  apply H in H1; trivial.
  simpl in H0. contradiction.

  right~.
  case H; clear H; intros T' H.
  exists T'.

  apply match_to_unif_step; trivial.

Qed.

(** 
A corollary of the previous lemma is that a triple T is not matching leaf
only if there exists a T' such that T reduces to T' by match_step.
*)

Corollary match_step_neg_NF : forall T, ~ match_leaf T <-> exists T', match_step T T'.
Proof.
  intros. split~; intro.
  case (match_step_NF_dec T); intro H0; try contradiction; trivial.
  intro H'. case H; clear H; intros T' H.
  apply H' in H. trivial.
Qed.


(**
The relation match_step preserves the validity of the triples
*)

Lemma match_step_valid_preserv : forall T T', match_step T T' -> valid_triple T -> valid_triple T'.
Proof.
  intros. inverts H.
  apply unif_step_valid_preserv in H1; trivial.
  unfold valid_triple in *|-*.
  simpl in *|-*. destruct H0.
  repeat split~.
  apply set_inter_nil. intros Y H4.
  apply set_inter_elim in H4. destruct H4.
  apply set_inter_nil with (a:=Y) in H.
  apply H; clear H. apply set_inter_intro; trivial.
  apply Problem_vars_remove in H5; trivial.
Qed. 


(**
   Let a triple T is valid that is not a matching leaf, and a pair Context x Substitution
   Sl = < C, S >. If the intersection between the right-hand variables of T and the domain
   of S is empty, then Sl is matching solution for T only if there exists a T' such that
   T reduces to T' by match_step and Sl is a solution for T'.
*)

Lemma match_step_compl : forall T Sl,
      valid_triple T ->
      set_inter Var_eqdec (rhvars_Probl (snd T)) (dom_rec (snd Sl)) = [] ->                     
      ~ match_leaf T ->
      (match_sol Sl T  <-> (exists T', match_step T T' /\ match_sol Sl T')).
Proof.
  
  intros. split~; intro.
  
  apply match_step_neg_NF in H1.
  case H1; clear H1; intros T' H1. inverts H1.

  assert (Q: exists T', unif_step (rhvars_Probl (snd T)) T T' /\ sol_c Sl T').
   apply unif_step_compl; trivial.
   apply unif_step_neg_NF. exists T'; trivial.
   apply unif_match_sol_equiv; trivial.

  case Q; clear Q; intros T0 Q. destruct Q.
  exists T0. split~. apply match_to_unif_step; trivial. 
  apply unif_match_sol_equiv; trivial.
  apply match_step_rh_inter_empty with (T:=T); trivial.
  apply match_to_unif_step; trivial.
  
  simpl in H0.
  exists (set_union Context_eqdec C (fresh_context (dom_perm pi) X),  S, P\((pi|.X)~?(([])|.X))).
  split~. apply match_fixpoint; trivial.
  unfold match_sol in *|-*.
  destruct H2. destruct H2. destruct H6. destruct H7.
  repeat split~; intros; simpl in *|-*.
  unfold fresh_env in *|-*; intros.
  apply set_union_elim in H9. destruct H9.
  apply H1; trivial.
  apply fresh_context_mem in H9. destruct H9. rewrite <- H9.
  
  assert (Q : set_inter Var_eqdec ([X]) (dom_rec (snd Sl)) = []).
   apply set_inter_nil. intros Y H11.  
   apply set_inter_nil with (a:=Y) in H0.
   apply H0. apply set_inter_elim in H11. destruct H11.
   apply set_inter_intro; trivial.
   apply rh_term_Probl_vars with (X:=X) in H5. 
   simpl in H11. destruct H11; try contradiction.
   rewrite <- H11; trivial.
   simpl. left~.
   
  rewrite inter_dom_term_vars with (t:=[]|.X) (S:=snd Sl); simpl; trivial.
  apply H6 in H5.
  rewrite inter_dom_term_vars with (t:=pi|.X) (S:=snd Sl) in H5; simpl; trivial.
  inverts H5. apply fresh_Su. simpl. apply H13.
  replace (dom_perm pi) with (disgr pi ([])) in H10.
  apply ds_eq_disgr; trivial.
  unfold disgr. simpl.
  rewrite app_nil_r; trivial.

  apply H2. apply set_remove_1 in H9; trivial.
  apply H6. apply set_remove_1 in H9; trivial.

  replace (P\((pi|.X)~?(([])|.X))) with
      (snd (set_union Context_eqdec C (fresh_context (dom_perm pi) X),  S, P\((pi|.X)~?(([])|.X)))).
  apply match_step_rh_inter_empty with (T := (C, S, P)); simpl; trivial.
  apply match_fixpoint; trivial. simpl; trivial.
  
  case H2; clear H2. intros T' H2. destruct H2.
  apply match_step_preserv with (Sl:=Sl) in H2; trivial.
  
Qed.

(**
   A well-founded order over match_step that allows
   using well-founded induction pricipies     
*)

Definition match_step_order (T T' : Triple) := match_step T' T.

Lemma match_step_order_wf : well_founded match_step_order.
Proof.
  unfold well_founded. intro T.
  apply well_founded_ind with (R := unif_step_size_order).
  apply unif_step_size_order_wf. intros T' H.
  apply Acc_intro. intros T'' H0.
  unfold match_step_order in H0.
  apply match_step_termination in H0.
  apply H; trivial.
Qed.

(**
  Let T a valid triple and Sl a pair Context x Substitution < C, S >.
  If the intersection between the right-hand variables of T
  and the domain of S is empty, T reduces to T' by match_step  
  and Sl is solution for T', then Sl is a solution for T.
*)

Theorem match_path_soundness : forall T T' Sl,
                                valid_triple T ->
                                set_inter Var_eqdec (rhvars_Probl (snd T)) (dom_rec (snd Sl)) = [] -> 
                                match_path T T' -> match_sol Sl T' -> match_sol Sl T.
Proof.
  intros. unfold match_path in H1.
  destruct H1. clear H3.
  induction H1; trivial.
  apply match_step_preserv with (Sl:=Sl) in H1; trivial.
  apply match_step_preserv with (Sl:=Sl) in H1; trivial.
  apply IHtr_clos; trivial.
  apply match_step_valid_preserv in H1; trivial.
  apply match_step_rh_inter_empty with (T := s); trivial.
Qed.


(**
   Let a triple T is valid that is not a matching leaf, and a pair Context x Substitution
   Sl = < C, S >. If the intersection between the right-hand variables of T and the domain
   of S is empty, then Sl is matching solution for T only if there exists a T' such that
   T reduces to T' by match_path and Sl is a solution for T'.
*)

  
Theorem match_path_compl : forall T Sl,
        valid_triple T ->
        set_inter Var_eqdec (rhvars_Probl (snd T)) (dom_rec (snd Sl)) = [] ->                         
        (match_sol Sl T <-> exists T', match_path T T' /\ match_sol Sl T').
Proof.
  
  intros. split~; intro. gen T. intro T.  
  apply well_founded_ind with (R := match_step_order) (a := T).  
  apply match_step_order_wf.

  intros T0 H0 H1 H2 H3. unfold match_step_order in H0. 
  case (match_step_NF_dec T0); intro H4.

  exists T0. split~. unfold match_path. split~. apply tr_rf.

  apply match_step_neg_NF in H4. 
  apply match_step_compl with (Sl := Sl) in H4; trivial.
  generalize H3; intro H3'. apply H4 in H3'.
  clear H4. case H3'; clear H3'; intros T1 H3'.
  destruct H3'. generalize H. intro H'.
  apply H0 in H'; trivial.
  case H'; clear H'; intros T2 H'. destruct H'. destruct H5.
  exists T2. split~. split~.
  apply tr_ms with (t := T1); trivial.

  apply match_step_valid_preserv with (T:=T0); trivial.
  apply match_step_rh_inter_empty with (T := T0); trivial.
  
  case H1; clear H1; intros T' H1. destruct H1.
  apply match_path_soundness with (Sl:=Sl) in H1; trivial.
  
Qed.


(** Characterisation of the set of matching successful leaves *) 


(** 
Let T = < C, S, P> a matching leaf and P a proper problem.
If there exists a solution Sl for T then P = [].
*)

Theorem match_successfull_leaves_ch : forall T,
    
                             Proper_Problem (snd T)  ->

                             match_leaf T ->  

                             (exists Sl, match_sol Sl T) ->

                             snd T = [].

Proof.

  intros. case H1; clear H1; intros Sl H1.
  
  assert (Q: fixpoint_Problem (snd T)).
   apply successful_leaves_ch with (varSet:=rhvars_Probl (snd T)); trivial.
   split~. intros T' H2.  
   apply (H0 T'). apply match_to_unif_step; trivial.
   exists Sl. split~.
   apply unif_match_sol_equiv; trivial.
   unfold match_sol in H1. apply H1.
   assert (set_inter Var_eqdec (rhvars_Probl (snd T)) (dom_rec (snd Sl)) = []). apply H1.
   apply set_inter_nil; intros Y H3.
   apply set_inter_nil with (a:=Y) in H2. apply H2.
   apply set_inter_elim in H3. destruct H3.
   apply set_inter_intro; trivial.

  destruct T. destruct p. simpl in *|-*.
  destruct p0; trivial.   
  false. generalize Q; intro Q'.
  unfold fixpoint_Problem in Q. simpl in Q.
  assert (fixpoint_equ c0). apply Q. left~. 
  unfold fixpoint_equ in H2.
  case H2; clear H2; intros pi H2.
  case H2; clear H2; intros X H2.
  destruct H2. rewrite H3 in *|-. clear H3.
  apply (H0 (set_union Context_eqdec c
            (fresh_context (dom_perm pi) X),  s, (((pi|.X)~?(([])|.X))::p0)\((pi|.X)~?(([])|.X)))).
  apply match_fixpoint; trivial.
  left~.

Qed.
