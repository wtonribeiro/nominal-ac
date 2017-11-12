(**
%\begin{verbatim}
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Termination.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
Description : This file is dedicated to the proof of termination of the 
              nominal C-unification algorithm. This proof is based 
	      in a lexicographic measure that is defined over triples (C, S, P).
	      Thus one proves that both equ_sys and fresh_sys induce a 
	      well-founded order.
 
 Last Modified On: November 10, 2017.
 ============================================================================
 \end{verbatim} %
 *)


Require Export C_Unif.                            
Require Import Wf.

(** %\section{Termination of the nominal C-unificaiton algorithm}% *)


(** %\subsection{Quadruple lexicographic order}% *)
(** 
	The Quadruple_order is an lexicographic order 
	that will be used in the proofs of well-foundness of 
	systems equ_sys and fresh_sys.
*)	

Definition Quadruple_order (Q Q': nat * nat * nat * nat) :=
  let N1  := fst (fst (fst Q)) in
  let N1' := fst (fst (fst Q')) in
  let N2  := snd (fst (fst Q)) in
  let N2' := snd (fst (fst Q')) in
  let N3  := snd (fst Q) in
  let N3' := snd (fst Q') in
  let N4  := snd Q in
  let N4' := snd Q' in
   (N1 > N1') \/
  ((N1 >= N1') /\ (N2 > N2')) \/
  (((N1 >= N1') /\ (N2 >= N2')) /\ (N3 > N3')) \/
  ((((N1 >= N1') /\ (N2 >= N2')) /\ (N3 >= N3')) /\ N4 > N4').


(** %\subsection{Problem measure}% *)
(**
	The lexicographic measure of a problem P is defined by 
	the quadruple: size of the set of variables of equations of P;
	size of the equations of P (ie., the sum of the size of the terms of the equations of P);
	number of fixpoint equations occurring in P; and size of the freshness constrains of P 
	(size of the terms in the freshness constraints of P).
*) 

Definition Problem_measure (P : Problem) :=
  (length (Problem_vars (equ_proj P)), equ_Problem_size P, non_fixpoint_equ P, fresh_Problem_size P).

  
(**
	The order between two triples is defined having as basis
	the measure of their respectives problems. 
*)
  
Definition unif_step_size_order (T T' : Triple) := 
  Quadruple_order (Problem_measure (snd T')) (Problem_measure (snd T)) .

(**
	A simpler notation for unif_step_size_order.
*)  
  
Notation "T <<* T'" := (unif_step_size_order T T') (at level 67).


(**
	The order that is induced by the relation unif_step.
*)

Definition unif_step_order (T T' : Triple) := unif_step T' T.


(** %\subsection{Termination of fresh\_sys}% *)

(** 
	If T reduces to T' by system fresh_sys, then  T' <<* T. 
	This lemma is proved by case analysis over fresh_sys T T'. 
	Notice that in all reductions 
	of fresh_sys, Problem_vars (equ_proj P)), equ_Problem_size P, 
	non_fixpoint_equ P keep same values, and fresh_Problem_size P is decreased. 
*)

Lemma fresh_sys_termination : forall T T', fresh_sys T T' -> T' <<* T .
Proof.
  intros.
  unfold unif_step_size_order. 
  unfold Quadruple_order.
  unfold Problem_measure.
  
  destruct H; simpl fst; simpl snd;
  repeat right~; repeat split~;
  repeat rewrite equ_proj_add_fresh;
  repeat rewrite equ_proj_rem_fresh;
  repeat rewrite equ_proj_add_fresh; 
  repeat rewrite equ_Problem_size_add_fresh;
  repeat rewrite equ_Problem_size_rem_fresh;
  repeat rewrite equ_Problem_size_add_fresh;
  repeat rewrite non_fixpoint_equ_add_fresh;
  repeat rewrite non_fixpoint_equ_rem_fresh;
  repeat rewrite non_fixpoint_equ_add_fresh; try omega.       


  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=<<>>); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=%b); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > fresh_Problem_size P + (term_size s)  - Datatypes.S (term_size s)).
   assert (Q': fresh_Problem_size P > 0).
    apply fresh_Problem_size_gt_0 with (a:=a) (s:=Fc E n s); trivial. omega.
  assert (Q': fresh_Problem_size (P |+ (a #? s)) <= fresh_Problem_size P + term_size s). 
  apply fresh_Problem_size_add. simpl in Q'. omega. apply set_add_intro1; trivial.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=[a]^s); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > 0).
  apply fresh_Problem_size_gt_0 with (a:=a)(s:=[b]^s); trivial.
  assert (Q': fresh_Problem_size P > fresh_Problem_size P + (term_size s) -
              Datatypes.S (term_size s)). omega.
  assert (Q'': fresh_Problem_size (P |+ (a #? s)) <= fresh_Problem_size P + term_size s). 
  apply fresh_Problem_size_add. simpl in Q''. omega. apply set_add_intro1; trivial.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=pi|.X); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size P > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=<|s,t|>); trivial.
  assert (Q': fresh_Problem_size P >
              fresh_Problem_size P + (term_size s) + (term_size t) -
              Datatypes.S (term_size s + term_size t)).
  omega.
  assert (Q'': fresh_Problem_size (P |+ (a #? s) |+ (a #? t)) <=
               fresh_Problem_size P + (term_size s) + (term_size t)). 
  assert (Q'': fresh_Problem_size ((P |+ (a #? s)) |+ (a #? t)) <=
               fresh_Problem_size (P |+ (a #? s)) + (term_size t)).
  apply fresh_Problem_size_add.
  assert (Q''': fresh_Problem_size (P |+ (a #? s)) <=
               fresh_Problem_size P + (term_size s)).
  apply fresh_Problem_size_add. omega.
  simpl in Q''. omega. apply set_add_intro1. apply set_add_intro1; trivial.

Qed.


(** %\subsection{Termination of the relation equ\_sys}% *)
(** 
	Termiantion of fresh_sys. 
	If T reduces to T' by system equ_sys, then  T' <<* T. 
	This lemma is proved by case analysis over equ_sys T T'. 
*)

Lemma equ_sys_termination : forall T T', equ_sys T T' ->  T' <<* T.
Proof.
  intros.
  unfold unif_step_size_order. 
  unfold Problem_measure.
  unfold Quadruple_order.

  destruct H; simpl fst; simpl snd.
  
  right~. left~. split~. 
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0. 
  apply Problem_vars_remove in H0; trivial.
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P >= equ_Problem_size ([s~?s])).
   apply equ_Problem_size_neq_nil; trivial.
  assert (Q' : equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=s) (t:=s); trivial. 
  assert (Q'' : term_size s > 0).
   apply term_size_gt_0.
  simpl in Q. omega.
   
  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0. 
  rewrite 2 equ_proj_add_eq in H0. 
  apply equ_proj_set_In_eq in H.
  apply Problem_vars_remove in H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.

  rewrite equ_Problem_size_remove.
  assert (Q : equ_Problem_size (P |+ (s0 ~? t0)) + equ_Problem_size ([s1 ~? t1]) >=
              equ_Problem_size ((P |+ (s0 ~? t0)) |+ (s1 ~? t1))).
   apply equ_Problem_size_add.
  assert (Q' : equ_Problem_size P + equ_Problem_size ([s0 ~? t0]) >=
               equ_Problem_size (P |+ (s0 ~? t0))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=<|s0,s1|>) (t:=<|t0,t1|>); trivial. 
  assert (Q''' : term_size s0 > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1. apply set_add_intro1; trivial.

  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H1. 
  rewrite equ_proj_add_eq in H1. 
  apply equ_proj_set_In_eq in H.
  apply Problem_vars_remove in H1; trivial.
  apply Problem_vars_add in H1. simpl in H1.
  apply set_union_elim in H1. destruct H1; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.  
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P + equ_Problem_size ([t ~? t']) >=
              equ_Problem_size (P |+ (t ~? t'))).
   apply equ_Problem_size_add.
  assert (Q': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=Fc E n t) (t:=Fc E n t'); trivial. 
  assert (Q'' : term_size t > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1; trivial.
   
  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0.
  rewrite equ_proj_add_eq in H0.
  rewrite equ_proj_add_eq in H0. 
  apply Problem_vars_remove in H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply set_union_elim in H0.
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply set_union_elim in H0.  
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.
  
  rewrite equ_Problem_size_remove. 
  assert (Q : equ_Problem_size (P |+ (s0 ~? t0)) + equ_Problem_size ([s1 ~? t1]) >=
              equ_Problem_size ((P |+ (s0 ~? t0)) |+ (s1 ~? t1))).
   apply equ_Problem_size_add.
  assert (Q' : equ_Problem_size P + equ_Problem_size ([s0 ~? t0]) >=
               equ_Problem_size (P |+ (s0 ~? t0))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=Fc 2 n (<| s0, s1 |>)) (t:=Fc 2 n (<| t0, t1 |>)); trivial. 
  assert (Q''' : term_size s0 > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1. apply set_add_intro1; trivial.

  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0.
  rewrite equ_proj_add_eq in H0.
  rewrite equ_proj_add_eq in H0. 
  apply Problem_vars_remove in H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply set_union_elim in H0.
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.
  apply set_union_elim in H0.  
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  
  rewrite equ_Problem_size_remove. 
  assert (Q : equ_Problem_size (P |+ (s0 ~? t1)) + equ_Problem_size ([s1 ~? t0]) >=
              equ_Problem_size ((P |+ (s0 ~? t1)) |+ (s1 ~? t0))).
   apply equ_Problem_size_add.
  assert (Q' : equ_Problem_size P + equ_Problem_size ([s0 ~? t1]) >=
               equ_Problem_size (P |+ (s0 ~? t1))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=Fc 2 n (<| s0, s1 |>)) (t:=Fc 2 n (<| t0, t1 |>)); trivial. 
  assert (Q''' : term_size s0 > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1. apply set_add_intro1; trivial.

  
  right~. left~. split~.

  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0. 
  rewrite equ_proj_add_eq in H0. 
  apply equ_proj_set_In_eq in H.
  apply Problem_vars_remove in H0; trivial.
  apply Problem_vars_add in H0. simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P + equ_Problem_size ([t ~? t']) >=
              equ_Problem_size (P |+ (t ~? t'))).
   apply equ_Problem_size_add.
  assert (Q': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=[a]^t) (t:=[a]^t'); trivial. 
  assert (Q'' : term_size t > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1; trivial.

  
  right~. left~. split~.

  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H1. 
  rewrite equ_proj_add_fresh in H1.
  rewrite equ_proj_add_eq in H1.
  apply equ_proj_set_In_eq in H0.
  apply Problem_vars_remove in H1; trivial.
  apply Problem_vars_add in H1. simpl in H1.
  apply set_union_elim in H1. destruct H1; trivial.
  apply Problem_vars_set_In with (X:=b0) in H0; trivial.  
  simpl. apply set_union_elim in H1. destruct H1.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  rewrite perm_term_vars in H1; trivial.

  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size (P |+ (t ~? (([(a, b)]) @ t'))) + equ_Problem_size ([a #? t']) >=
              equ_Problem_size ((P |+ (t ~? (([(a, b)]) @ t'))) |+ (a #? t'))).
   apply equ_Problem_size_add.  
  assert (Q' : equ_Problem_size P + equ_Problem_size ([t ~? (([(a, b)]) @ t')]) >=
              equ_Problem_size (P |+ (t ~? (([(a, b)]) @ t')))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=[a]^t) (t:=[b]^t'); trivial. 
  assert (Q''' : term_size t > 0).
   apply term_size_gt_0.
  simpl in *|-*. rewrite perm_term_size in Q'. omega.
  apply set_add_intro1; apply set_add_intro1; trivial.

  left~.

  apply nat_lt_inv.
  apply subset_list'.
  apply Var_eqdec. apply NoDup_Problem_vars.
  intros.
  rewrite equ_proj_union in H2. 
  apply Problem_vars_union in H2.
  apply set_union_elim in H2. destruct H2.

  Focus 2. rewrite equ_proj_subs_fresh in H2.
  simpl in H2. contradiction.

  rewrite equ_proj_subs in H2.
  case (b ==v X); intro H3. rewrite H3 in H2.
  apply In_im_subst_term_Problem in H2.
  rewrite perm_term_vars in H2. contradiction.
  apply In_im_subst_term_Problem' in H2; trivial.
  apply set_union_elim in H2. destruct H2.
  rewrite 2 equ_proj_rem_eq in H2.
  apply Problem_vars_remove in H2.
  apply Problem_vars_remove in H2. trivial.
  rewrite perm_term_vars in H2.
  destruct H0; apply equ_proj_set_In_eq in H0;
  apply Problem_vars_set_In with (X:=b) in H0; simpl; trivial.
  apply set_union_intro2; trivial.
  apply set_add_intro1; trivial.
  
  exists X; split~.
  destruct H0; apply equ_proj_set_In_eq in H0;
  apply Problem_vars_set_In with (X:=X) in H0; simpl; trivial.
  apply set_union_intro1; simpl; left~.
  apply set_add_intro2; trivial.
  intro H2. rewrite equ_proj_union in H2. 
  apply Problem_vars_union in H2.
  apply set_union_elim in H2. destruct H2.

  Focus 2. rewrite equ_proj_subs_fresh in H2.
  simpl in H2; trivial.
  rewrite equ_proj_subs in H2.
  apply In_im_subst_term_Problem in H2.
  rewrite perm_term_vars in H2. contradiction.
  
  right~. right~. left~. split~. split~.
 
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H2. 
  rewrite equ_proj_add_eq in H2.
  apply equ_proj_set_In_eq in H1.
  apply Problem_vars_remove in H2; trivial.
  apply Problem_vars_add in H2. simpl in H2.
  apply set_union_elim in H2. destruct H2; trivial.
  apply Problem_vars_set_In with (X:=b) in H1; trivial.

  rewrite equ_Problem_size_remove. simpl. 

  assert (Q : equ_Problem_size P + equ_Problem_size ([((pi ++ (! pi')|.X) ~? (([])|.X))])  >=
               equ_Problem_size (P |+ ((pi ++ (! pi')|.X) ~? (([])|.X)))).
  apply equ_Problem_size_add.
  simpl in Q. omega. apply set_add_intro1; trivial.

  rewrite non_fixpoint_equ_remove.
  rewrite non_fixpoint_equ_add.
  assert (Q : non_fixpoint_equ P > 0).
   apply non_fixpoint_equ_gt_0 with (s := pi|.X) (t := pi'|.X); trivial.
   intro H2. destruct H2. destruct H2. destruct H2. inverts H3. apply H0; trivial.
  omega. intro H2. apply H0.
  assert (Q' : !pi' = []).
   gen_eq g : (!pi'); intro H'. clear H'.
   destruct g; trivial. symmetry in H2.
   apply app_cons_not_nil in H2. contradiction.
  replace pi' with (!(!pi')). rewrite Q'. simpl; trivial.
  rewrite rev_involutive; trivial.
  apply set_add_intro1; trivial.
  intro. destruct H2. destruct H2. destruct H2. inverts H3. apply H0; trivial.

Qed.  


(** %\subsection{Termiantion of unif\_step\_sys}% *)

(** For each unifaction step unif_step T T', 
one has T' <<* T. This Corollary is also proved by case analysis over 
unif_step T T', and its proof uses Lemmas equ_sys_termination and
fresh_sys_termination.
*)

Corollary unif_step_termination : forall T T', unif_step T T' -> T' <<* T .
Proof.
 intros. destruct H.
 apply equ_sys_termination; trivial.
 apply fresh_sys_termination; trivial. 
Qed.

(** %\subsection{Well-foundness of the induced order by unif\_step}% *)
(** 
	unif_step_size_order and unif_step_order are both well_founded orders. 
	The proof of the latter uses Corollary unif_step_termination.
*)


Lemma unif_step_size_order_wf : well_founded unif_step_size_order.
Proof.
  unfold well_founded. intro T. destruct T. destruct p. 
  gen_eq l : (Problem_measure p0). 
  destruct l. destruct p. destruct p.
  gen c s n2 n0 n p0. induction n1 using peano_induction; intros.
  gen c s n0 n p0. induction n2 using peano_induction; intros.
  gen c s n p0. induction n0 using peano_induction; intros.
  gen c s p0. induction n using peano_induction; intros.  
  apply Acc_intro; intros T' H'. destruct T'. destruct p.
  unfold unif_step_size_order in H'. unfold Quadruple_order in H'.
  unfold Problem_measure in *|-. simpl in *|-. inverts H3.
  destruct H'.    
  apply H with (m := length (Problem_vars (equ_proj p1)))
                 (n2 := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                  (n := fresh_Problem_size p1); try omega; trivial.
  destruct H3. destruct H3.
  inverts H3.
  apply H0 with (m := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                 (n := fresh_Problem_size p1); try omega.
  rewrite H6; trivial.   
  
  apply H with (m := length (Problem_vars (equ_proj p1)))
                 (n2 := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                  (n := fresh_Problem_size p1); try omega; trivial.
  destruct H3. destruct H3. destruct H3.
  inverts H3. inverts H5.
  apply H1 with (m := non_fixpoint_equ p1) (n := fresh_Problem_size p1); try omega.
  rewrite H6. rewrite H7; trivial.
  apply H0 with (m := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                 (n := fresh_Problem_size p1); try omega.
  rewrite H7; trivial.
  apply H with (m := length (Problem_vars (equ_proj p1)))
                 (n2 := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                  (n := fresh_Problem_size p1); try omega; trivial.
  destruct H3. destruct H3. destruct H3. 
  inverts H3. inverts H6. inverts H5.
  apply H2 with (m := fresh_Problem_size p1); try omega.
  rewrite H6. rewrite H7. rewrite H8. trivial.
  apply H1 with (m := non_fixpoint_equ p1) (n := fresh_Problem_size p1); try omega.
  rewrite H7. rewrite H8; trivial. 
  apply H0 with (m := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                 (n := fresh_Problem_size p1); try omega.
  rewrite H8; trivial.
  apply H with (m := length (Problem_vars (equ_proj p1)))
                 (n2 := equ_Problem_size p1) (n0 := non_fixpoint_equ p1)
                  (n := fresh_Problem_size p1); try omega; trivial.
Qed.



Lemma unif_step_order_wf : well_founded unif_step_order .
Proof.
  unfold well_founded. intro T.
  apply well_founded_ind with (R := unif_step_size_order).
  apply unif_step_size_order_wf. intros T' H.
  apply Acc_intro. intros T'' H0.
  unfold unif_step_order in H0.
  apply unif_step_termination in H0.
  apply H; trivial.
Qed.


(** %\section{Decidability of the predicates NF fresh\_sys, NF equ\_sys and leaf}% *)

(**
	The following 10 lemmas and 3 corollaries are very technical results.
	They serve the sole purpose of prooving that the predicates 
	NF fresh_sys, NF equ_sys and leaf are decidable, which are applied 
	to the proof of completeness of the C-unication algorithm.
*)

Lemma fresh_sys_NF_dec_singleton :
  forall C S c, NF _ fresh_sys (C, S, [c]) \/ exists T', fresh_sys (C, S, [c]) T'.
Proof.
  intros. destruct c. destruct t.
  right~. exists (C, S, [a#?(<<>>)]\(a#?(<<>>))). apply fresh_sys_Ut. left~.
  case (a ==at a0); intro H.
   left~. intros T' H'. inverts H'; simpl in H4; try destruct H4; trivial; try inverts H0; 
   try destruct H5; try contradiction; try inverts H0; trivial.
  right~. exists (C, S, [a#?(% a0)]\(a#?(%a0))). apply fresh_sys_At; trivial. left~.
  right~. case (a ==at a0); intro H.
  rewrite H. exists (C, S, [a0#?([a0]^t)]\(a0#?([a0]^t))). apply fresh_sys_Ab_1. left~.
  exists (C, S, [a#?([a0]^t)]|+(a#?t)\(a#?([a0]^t))). apply fresh_sys_Ab_2; trivial. left~.
  right~. exists (C, S, [a #?(<|t1,t2|>)]|+(a#?t1)|+(a#?t2)\(a#?(<|t1,t2|>))).
   apply fresh_sys_Pr. left~.
  right~. exists (C, S, [a #? Fc n n0 t]|+(a#?t)\(a#?(Fc n n0 t))). apply fresh_sys_Fc. left~.
  right~. exists (C|++((!p) $ a,v), S, [a #? (p|.v)]\(a#?(p|.v))). apply fresh_sys_Su. left~.
  
  left~. intros T H. inverts H; simpl in *|-;
   try destruct H4; try inverts H; try destruct H5; try inverts H; try inverts H0.
Qed.


Lemma fresh_sys_red_singleton : forall C S P ,
                               (exists c T0, set_In c P /\ fresh_sys (C, S, [c]) T0) <->
                               (exists T1, fresh_sys (C, S, P) T1).
Proof.
  intros.
  split~; intro.
  
  case H; clear H; intros c H.
  case H; clear H; intros T0 H.
  destruct H. destruct T0. destruct p.
  inverts H0; simpl in *|-;
   try destruct H2; try contradiction; try rewrite H0 in *|-.
  exists (c0, s, P\(a#?(<<>>))). apply fresh_sys_Ut; trivial.
  destruct H8; try contradiction; rewrite H0 in H.
  exists (c0, s, P\(a#?(%b))). apply fresh_sys_At; trivial.
  exists (c0, s, P|+(a#?s0)\(a#?(Fc E n s0))). apply fresh_sys_Fc; trivial.
  exists (c0, s, P\(a#?([a]^s0))). apply fresh_sys_Ab_1; trivial.
  destruct H8; try contradiction; rewrite H0 in H.
  exists (c0, s, P|+(a#?s0)\(a#?([b]^s0))). apply fresh_sys_Ab_2; trivial.
  exists (C|++((!pi) $ a,X), s, P\(a#?(pi|.X))). apply fresh_sys_Su; trivial.
  exists (c0, s, P|+(a#?s0)|+(a#?t)\(a#?(<|s0, t|>))). apply fresh_sys_Pr; trivial.
  
  case H; clear H; intros T1  H.
  inverts H.
  exists (a #? (<<>>)) (C, S, [a #? (<<>>)]\(a#?(<<>>))).
   split~. apply fresh_sys_Ut. left~.
  exists (a #? (% b)) (C, S, [a #? (% b)]\(a#?(%b))).
   split~. apply fresh_sys_At; trivial. left~.
  exists (a#?Fc E n s) (C, S, [a #? Fc E n s]|+(a#?s)\(a#?(Fc E n s))).
   split~. apply fresh_sys_Fc. left~.
  exists (a #? ([a]^s)) (C, S, [a #? ([a]^s)]\(a#?([a]^s))).
   split~. apply fresh_sys_Ab_1. left~.
  exists (a #? ([b]^s)) (C, S, [a #? ([b]^s)]|+(a#?s)\(a#?([b]^s))).
   split~. apply fresh_sys_Ab_2; trivial. left~.
  exists (a #? (pi|.X)) (C|++((!pi) $ a,X), S, [a #? (pi|.X)]\(a#?(pi|.X))).
   split~. apply fresh_sys_Su. left~.
  exists (a #? (<|s, t|>)) (C, S, [a #? (<|s, t|>)]|+(a#?s)|+(a#?t)\(a#?(<|s, t|>))).
   split~. apply fresh_sys_Pr. left~. 
Qed.

Lemma fresh_sys_NF_singleton : forall C S P, NF _ fresh_sys (C, S, P) <->
                                           (forall c, set_In c P -> NF _ fresh_sys (C, S, [c])).
Proof.
  intros. split~; intros.
  
  intros T H'.
  assert (Q : exists T1, fresh_sys (C, S, P) T1).
   apply fresh_sys_red_singleton.
   exists c T. split~.
  case Q; clear Q; intros T' Q.
  apply H in Q. trivial.

  intros T' H0.
  assert (Q : exists c T0, set_In c P /\ fresh_sys (C, S, [c]) T0).
   apply fresh_sys_red_singleton. exists T'; trivial.
  case Q; clear Q; intros c Q.    
  case Q; clear Q; intros T'' Q.
  destruct Q. gen H2. apply H; trivial.
Qed.

  
Lemma fresh_sys_NF_dec_singleton'  : forall C S P,
                             (NF _ fresh_sys (C, S, P)) \/        
                             (exists c T', set_In c P /\ fresh_sys (C, S, [c]) T') .
Proof.
  intros. induction P.
  left~. intros T' H. 
  inverts H; simpl in *|-; trivial. 
  destruct IHP.
  case fresh_sys_NF_dec_singleton with (C:=C) (S:=S) (c:=a); intro H'.
  left~. apply fresh_sys_NF_singleton.
  intros c H0. simpl in H0. destruct H0.
  rewrite <- H0. trivial.
  apply fresh_sys_NF_singleton with (c:=c) in H; trivial.
  right~. case H'; clear H'; intros T' H'.
  exists a T'. split~. left~.
  right~. case H; clear H; intros c H.
  case H; clear H; intros T' H. destruct H.
  exists c T'. split~. right~.
Qed.
  
Lemma fresh_sys_NF_dec : forall T, NF _ fresh_sys T \/ exists T', fresh_sys T T'.
Proof.  
  intros. destruct T. destruct p.
  case fresh_sys_NF_dec_singleton' with (C:=c) (S:=s) (P:=p0); intro H.
  left~. right~. case H; clear H; intros a H.
  case H; clear H; intros T' H. destruct H.
  apply fresh_sys_red_singleton. 
  exists a T'. split~.
Qed.

Corollary fresh_sys_neg_NF : forall T, ~ NF _ fresh_sys T <-> exists T', fresh_sys T T'.
Proof.
  intros. split~; intro.
  
  case (fresh_sys_NF_dec T); intro H0; try contradiction; trivial.

  intro H'. case H; clear H; intros T' H.
  apply H' in H. trivial.
Qed.  


Lemma equ_sys_NF_dec_singleton :
  forall C S c, NF _ equ_sys (C, S, [c]) \/ exists T', equ_sys (C, S, [c]) T'.
Proof.
  intros. destruct c.

  left~. intros T H. inverts H; simpl in *|-;
   try destruct H4; try inverts H; try destruct H5; try inverts H; try inverts H0.
   destruct H6; try contradiction. inverts H.
  
  case (term_eqdec t t0); intro H.
  (* t = t0 *)
   rewrite H; clear H. right~.
   exists (C, S, [t0 ~? t0]\(t0~?t0)). apply equ_sys_refl. left~.                            
  (* t <> t0 *)
   case (Su_eqdec t); case (Su_eqdec t0); intros H0 H1.
   (* t and t0 are both suspensions *)  
    case H0; clear H0; intros pi' H0. case H0; clear H0; intros Y H0.
    case H1; clear H1; intros pi H1. case H1; clear H1; intros X H1.
    rewrite H0 in *|-*. rewrite H1 in *|-*. clear H0 H1.
    case (Y ==v X); intro H0. 
     (* the variables of the two suspesions are equal *)
      rewrite H0 in *|-*. clear H0.
      case (Perm_eqdec pi' ([])); intro H0.
      (* pi' = [] *) 
       rewrite H0 in *|-*. clear H0. 
       left~. intros T' H0. inverts H0; simpl in *|-;
       try destruct H5; try inverts H0; try destruct H6; try inverts H0; try inverts H1.
       symmetry in H3. contradiction.
       apply H4. simpl. left~. apply H4. simpl. left~.
       destruct H7; try contradiction. inverts H0; trivial.
      (* pi' <> [] *)
       right~. exists (C,S,([(pi|.X)~?(pi'|.X)]|+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X))).
       apply equ_sys_inv; trivial. intro H1. rewrite H1 in H. false. left~.    
     (* the variables of the two suspesions are different *) 
       right~. exists (C,S©([(X,(!pi)@(pi'|.Y))]),
                       (([(pi|.X)~?(pi'|.Y)]\(pi|.X~?(pi'|.Y))
                         \((pi'|.Y)~?(pi|.X)))|^^([(X,(!pi)@(pi'|.Y))]))
                          \cup(C/?(S©([(X,(!pi)@(pi'|.Y))])))).
       apply equ_sys_inst; trivial. simpl. intro H1. destruct H1; contradiction. left~. left~.
   (* only t is a suspension *)
    case H1; clear H1; intros pi H1.    
    case H1; clear H1; intros X H1. rewrite H1 in *|-*. clear H1.
    case (set_In_dec Var_eqdec X (term_vars t0)); intro H1.
    (* X is in (term_vars t0) *)
     left~. intros T' H2. inverts H2; simpl in *|-;
       try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
       false. contradiction. false. destruct H9; try contradiction. inverts H2. false.
    (* X is not in (term_vars t0) *) 
     right~. exists (C,S©([(X,(!pi)@t0)]),
                        (([(pi|.X)~?t0]\(pi|.X~?t0)\(t0~?(pi|.X)))|^^([(X,(!pi)@t0)]))
                          \cup(C/?(S©([(X,(!pi)@t0)])))).
     apply equ_sys_inst; trivial. left~. left~.
   (* only t0 is a suspension *)  
    case H0; clear H0; intros pi H0.    
    case H0; clear H0; intros X H0. rewrite H0 in *|-*. clear H0.
    case (set_In_dec Var_eqdec X (term_vars t)); intro H2.
    (* X is in (term_vars t) *)
     left~. intros T' H3. inverts H3; simpl in *|-;
       try destruct H7; try inverts H0; try destruct H8; try inverts H0; try inverts H3.
       false. false. contradiction. destruct H9; try contradiction. inverts H0. false.
    (* X is not in (term_vars t) *) 
     right~. exists (C,S©([(X,(!pi)@t)]),
                        (([t~?(pi|.X)]\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))
                          \cup(C/?(S©([(X,(!pi)@t)])))).
     apply equ_sys_inst; trivial. right~. left~.

  (* both t and t0 are not suspensions *)
   destruct t.
   (* t = <<>> *)
    left~. intros T' H2. inverts H2; simpl in *|-;
       try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
       false. false. destruct H9; try contradiction. inverts H2. 
   (* t = %a *)
    left~. intros T' H2. inverts H2; simpl in *|-;
       try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
       false. false. destruct H9; try contradiction. inverts H2. 
   (* t = [a]^s0 *)
    destruct t0.
     (* t0 = <<>> *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = %a0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = [a0]^s0 *)
      right~. case (a ==at a0); intro H2. rewrite H2 in *|-*. clear H2.
      exists (C,S,[([a0]^t)~?([a0]^t0)]|+(t~?t0)\(([a0]^t)~?([a0]^t0))).
      apply equ_sys_Ab1; trivial. left~. 
      exists (C,S,(([([a]^t)~?([a0]^t0)]|+(t~?([(a,a0)]@t0))|+(a#?t0)))\(([a]^t)~?([a0]^t0))).
      apply equ_sys_Ab2; trivial. left~.
     (* t0 = <| t0_1, t0_2|> *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = Fc n n0 s0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = p|.v *)
      false.        
   (* t = <|s1, s2|> *)
    destruct t0.
     (* t0 = <<>> *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = %a0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = [a0]^s0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = <| t0_1, t0_2|> *)
        right~. exists (C,S,(([(<|t1,t2|>)~?(<|t0_1,t0_2|>)]|+
                       (t1~?t0_1))|+(t2~?t0_2))\(<|t1,t2|>~?<|t0_1,t0_2|>)).
        apply equ_sys_Pr; trivial. left~.
     (* t0 = Fc n n0 s0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = p|.v *)
      false.  
   (* t = Fc n n0 s0 *)
    destruct t0.
     (* t0 = <<>> *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = %a0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = [a0]^s0 *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = <| t0_1, t0_2|> *)
      left~. intros T' H2. inverts H2; simpl in *|-;
        try destruct H7; try inverts H2; try destruct H8; try inverts H2; try inverts H3.
        false. destruct H9; try contradiction. inverts H2.
     (* t0 = Fc n n0 s0 *)
      case ((n, n0) ==np (n1, n2)); intro H2. inverts H2.
      case (eq_nat_dec n1 2); intro H2. rewrite H2 in *|-*; clear H2.
      case (Pr_eqdec t); intro H2. case (Pr_eqdec t0); intro H3.
      case H2; clear H2; intros u0 H2. case H2; clear H2; intros u1 H2.
      case H3; clear H3; intros v0 H3. case H3; clear H3; intros v1 H3.
      rewrite H2 in *|-*. rewrite H3 in *|-*. clear H2 H3.
      right~. exists (C,S,(([Fc 2 n2 (<|u0,u1|>)~?Fc 2 n2 (<|v0,v1|>)]
                     |+(u0~?v0))|+(u1~?v1))\(Fc 2 n2 (<|u0,u1|>)~?(Fc 2 n2 (<|v0,v1|>)))).
      apply equ_sys_C1; trivial. left~.
      left~. intros T' H4. inverts H4; simpl in *|-;
        try destruct H9; trivial; try inverts H4; try destruct H10; trivial;
        try inverts H4; trivial.
      symmetry in H7. contradiction. false. false. false. false.
      destruct H11; try contradiction. false.
      left~. intros T' H3. inverts H3; simpl in *|-;
        try destruct H8; trivial; try inverts H3; try destruct H9; trivial;
        try inverts H3; trivial.
      symmetry in H6. contradiction. false. false. false. false.
      destruct H10; try contradiction. false.
      right~. exists (C,S,([Fc n1 n2 t ~? Fc n1 n2 t0]|+(t~?t0))\(Fc n1 n2 t ~?(Fc n1 n2 t0))).
      apply equ_sys_Fc; trivial. left~.
      left~. intros T' H3. inverts H3; simpl in *|-; try destruct H8; trivial; try inverts H3.
      false. false. false. false. destruct H9; try contradiction. false.
      destruct H9; destruct H3; try contradiction; try inverts H3.
      destruct H10; trivial. false.
     (* t0 = p|.v *)
      false.  
   (* t = p|.v *) 
    false. 
Qed.  


Lemma equ_sys_red_singleton : forall C S P,
                               (exists c T0, set_In c P /\  equ_sys (C, S, [c]) T0) <->
                               (exists T1, equ_sys (C, S, P) T1).
                                           
Proof.
  intros. split~; intros.

  case H; clear H; intros c H.
  case H; clear H; intros T0 H0.
  destruct H0. destruct T0. destruct p.
  inverts H0; simpl in *|-;
   try destruct H2; try contradiction; try rewrite H0 in *|-.

  exists (c0, s, P\(s0~?s0)). apply equ_sys_refl; trivial.
  exists (c0, s, P|+(s0~?t0)|+(s1~?t1)\((<|s0, s1|>)~?(<|t0, t1|>))).
   apply equ_sys_Pr; trivial.
  destruct H3; try contradiction; rewrite H0 in H.
  exists (c0, s, P|+(t~?t')\(Fc E n t ~? Fc E n t')).
   apply equ_sys_Fc; trivial. 
  exists (c0, s, P|+(s0~?t0)|+(s1~?t1)\(Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>))).
   apply equ_sys_C1; trivial.   
  exists (c0, s, P|+(s0~?t1)|+(s1~?t0)\(Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>))).
   apply equ_sys_C2; trivial.   
  exists (c0, s, P|+(t~?t')\(([a]^t) ~? ([a]^t'))).
   apply equ_sys_Ab1; trivial.      
  destruct H8; try contradiction; rewrite H0 in H. 
  exists (c0, s, P|+(t~?(([(a,b)])@t'))|+(a#?t')\(([a]^t) ~? ([b]^t'))).
   apply equ_sys_Ab2; trivial.
  destruct H8; try contradiction. destruct H0; try contradiction; rewrite H0 in H.  
  exists (c0, S©([(X,(!pi)@t)]),((P\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))
                          \cup(c0/?(S©([(X,(!pi)@t)])))).
   apply equ_sys_inst; trivial. left~.
  destruct H0; try contradiction; rewrite H0 in H.  
  exists (c0, S©([(X,(!pi)@t)]),((P\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))
                          \cup(c0/?(S©([(X,(!pi)@t)])))).
   apply equ_sys_inst; trivial. right~.
  destruct H9; try contradiction; rewrite H0 in H. 
  exists (c0, s, (P|+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X))).
   apply equ_sys_inv; trivial.

  case H; clear H; intros T1 H.
  destruct T1. destruct p. inverts H.
  exists (s0~?s0) (c, s, [s0~?s0]\(s0~?s0)).
   split~. apply equ_sys_refl. left~.
   exists ((<|s0, s1|>)~?(<|t0, t1|>))
          (c, s, [(<|s0, s1|>)~?(<|t0, t1|>)]|+(s0~?t0)|+(s1~?t1)\((<|s0, s1|>)~?(<|t0, t1|>))).
   split~. apply equ_sys_Pr. left~.
  exists (Fc E n t ~? Fc E n t') (c, s, [Fc E n t ~? Fc E n t']|+(t~?t')\(Fc E n t ~? Fc E n t')).
   split~. apply equ_sys_Fc; trivial. left~.
   exists (Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>))
          (c, s, [Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>)]
                   |+(s0~?t0)|+(s1~?t1)\(Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>))).
   split~. apply equ_sys_C1. left~.  
   exists (Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>))
          (c, s, [Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>)]
                   |+(s0~?t1)|+(s1~?t0)\(Fc 2 n (<|s0, s1|>) ~? Fc 2 n (<|t0, t1|>))).
   split~. apply equ_sys_C2. left~.     
  exists (([a]^t) ~? ([a]^t')) (c, s, [([a]^t) ~? ([a]^t')]|+(t~?t')\(([a]^t) ~? ([a]^t'))).
   split~. apply equ_sys_Ab1. left~.
  exists (([a]^t) ~? ([b]^t')) (c, s, [([a]^t) ~? ([b]^t')]
              |+(t~?(([(a,b)])@t'))|+(a#?t')\(([a]^t) ~? ([b]^t'))).
   split~. apply equ_sys_Ab2; trivial. left~.
  destruct H7.
  exists (pi|.X~?t) (c, S©([(X,(!pi)@t)]),(([pi|.X~?t]\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))
                          \cup(c/?(S©([(X,(!pi)@t)])))).
   split~. apply equ_sys_inst; trivial. left~. left~.
  exists (t~?(pi|.X)) (c, S©([(X,(!pi)@t)]),(([t~?(pi|.X)]\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))
                          \cup(c/?(S©([(X,(!pi)@t)])))).
   split~. apply equ_sys_inst; trivial. right~. left~.
   exists ((pi|.X)~?(pi'|.X)) (c, s, ([(pi|.X)~?(pi'|.X)]
                                        |+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X))).
   split~. apply equ_sys_inv; trivial. left~.
Qed.


Lemma equ_sys_NF_singleton : forall C S P, NF _ equ_sys (C, S, P) <->
                                           (forall c, set_In c P -> NF _ equ_sys (C, S, [c])).
Proof.
  intros. split~; intros.
  
  intros T H'.
  assert (Q : exists T1, equ_sys (C, S, P) T1).
   apply equ_sys_red_singleton.
   exists c T. split~.
  case Q; clear Q; intros T' Q.
  apply H in Q. trivial.

  intros T' H0.
  assert (Q : exists c T0, set_In c P /\ equ_sys (C, S, [c]) T0).
   apply equ_sys_red_singleton. exists T'; trivial.
  case Q; clear Q; intros c Q.    
  case Q; clear Q; intros T'' Q.
  destruct Q. gen H2. apply H; trivial. 
Qed.



Lemma equ_sys_NF_dec_singleton'  : forall C S P,
                             (NF _ equ_sys (C, S, P)) \/        
                             (exists c T', set_In c P /\ equ_sys (C, S, [c]) T') .
Proof.
  intros. induction P.
  left~. intros T' H. 
  inverts H; simpl in *|-; trivial. destruct H5; trivial.
  destruct IHP.
  case equ_sys_NF_dec_singleton with (C:=C) (S:=S) (c:=a); intro H'.
  left~. apply equ_sys_NF_singleton.
  intros c H0. simpl in H0. destruct H0.
  rewrite <- H0. trivial.
  apply equ_sys_NF_singleton with (c:=c) in H; trivial.
  right~. case H'; clear H'; intros T' H'.
  exists a T'. split~. left~.
  right~. case H; clear H; intros c H.
  case H; clear H; intros T' H. destruct H.
  exists c T'. split~. right~.
Qed.
    


Lemma equ_sys_NF_dec : forall T, NF _ equ_sys T \/ exists T', equ_sys T T'.
Proof.
  intros. destruct T. destruct p.
  case equ_sys_NF_dec_singleton' with (C:=c) (S:=s) (P:=p0); intro H.
  left~. right~. case H; clear H; intros a H.
  case H; clear H; intros T' H. destruct H.
  apply equ_sys_red_singleton.
  exists a T'. split~.
Qed.


Corollary equ_sys_neg_NF : forall T, ~ NF _ equ_sys T <-> exists T', equ_sys T T'.
Proof.
  intros. split~; intro.
  
  case (equ_sys_NF_dec T); intro H0; try contradiction; trivial.

  intro H'. case H; clear H; intros T' H.
  apply H' in H. trivial.
Qed.



Lemma unif_step_NF_dec :  forall T, NF _ unif_step T \/ exists T', unif_step T T'.
Proof.
  intros.
  case (equ_sys_NF_dec T); intro H.
  case (fixpoint_Problem_eqdec (equ_proj (snd T))); intro H0.
  case (fresh_sys_NF_dec T); intro H1.
  left~. intros T' H2. destruct H2.
   apply H in H2; trivial. apply H1 in H3; trivial.
   right~. case H1; clear H1; intros T' H1. exists T'.
   apply fresh_unif_step; trivial.   
  left~. intros T' H2. destruct H2; try contradiction.
  apply H in H1; trivial.
  right~. case H; clear H; intros T' H.
  exists T'. apply equ_unif_step; trivial.
Qed.
  
Corollary unif_step_neg_NF : forall T, ~ leaf T <-> exists T', unif_step T T'.
Proof.
  intros. split~; intro.
  
  case (unif_step_NF_dec T); intro H0; try contradiction; trivial.

  intro H'. case H; clear H; intros T' H.
  apply H' in H. trivial.
Qed.

