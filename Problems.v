(**
============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Problems.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation

 Description : This contains the definitions and basic lemmas related to
               unification problems.  

 Last Modified On: Sep 17, 2018.
 ============================================================================
*)

Require Export C_Equiv.

Close Scope nat_scope.


(** Definitions *)

(** A constraint is inductive defined as being 
    an equation or a freshness constraint *)

Inductive Constraint : Set :=
  | fresh_constraint : Atom -> term -> Constraint
  | equ_constraint : term -> term -> Constraint                 
.


(** A substitution, a problem and a triple are respectively 
    a set of pairs of variables and terms, a set of constraints 
    and a triple of freshness contexts, substitutions and problems. *) 

Definition Subst := set (Var * term) .
Definition Problem := set (Constraint).
Definition Triple := (Context * Subst * Problem) .

(** Decidability between constraints *)

Lemma Constraint_eqdec : forall x y : Constraint, {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y.
  case (atom_eqdec a a0); intro H.
  case (term_eqdec t t0); intro H0.
  rewrite H. rewrite H0. left~.
  right~. intro. inverts H1. apply H0; trivial.
  right~. intro. inverts H0. apply H; trivial.  
  right~. discriminate. right~. discriminate.
  case (term_eqdec t t1); intro H.
  case (term_eqdec t0 t2); intro H0.
  rewrite H. rewrite H0. left~.
  right~. intro. inverts H1. apply H0; trivial.  
  right~. intro. inverts H0. apply H; trivial.  
Qed.

(** Decidability between constraints pairs of atoms and variables (elements of a 
    freshness context). *)

Lemma Context_eqdec : forall x y : (Atom * Var), {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y.
  case (atom_eqdec a a0); intro H.
  case (var_eqdec v v0); intro H0.
  rewrite H. rewrite H0. left~.
  right~. intro. inverts H1. apply H0; trivial.
  right~. intro. inverts H0. apply H; trivial.  
Qed.


(** Some notations *)

Notation "a #? t" := (fresh_constraint a t) (at level 67).
Notation "s ~? t" := (equ_constraint s t) (at level 67).

Notation "P \ u" := (set_remove Constraint_eqdec u P) (at level 67).
Notation "P |+ u" := (set_add Constraint_eqdec u P) (at level 67).
Notation "C |++ u" := (set_add Context_eqdec u C) (at level 67).
Notation "P0 \cup P1" := (set_union Constraint_eqdec P0 P1) (at level 67).


(** Variables of a problem *)

Fixpoint Problem_vars (P : Problem) : set Var :=
  match P with
    | [] => []
    | (a#?t)::P0 => set_union var_eqdec (term_vars t) (Problem_vars P0)
    | (s~?t)::P0 => set_union var_eqdec (term_vars s)
                   (set_union var_eqdec (term_vars t) (Problem_vars P0))                         
  end.


(** Subsets of equations and freshness contexts of a problem *)


Fixpoint equ_proj (P : Problem) : Problem :=
  match P with
    | [] => []
    | (a#?t)::P0 => equ_proj P0
    | (s~?t)::P0 => (s~?t)::(equ_proj P0)                        
  end.  

Fixpoint fresh_proj  (P : Problem) : Problem :=
  match P with
    | [] => []
    | (a#?t)::P0 => (a#?t)::(fresh_proj P0) 
    | (s~?t)::P0 =>  fresh_proj P0                      
  end.


(** Fixpoint equations are defined as pi|.X ~? []|.X, where
    pi <> [] *)

Definition fixpoint_equ (u : Constraint) :=
  exists pi, exists X, pi <> [] /\ u = pi|.X ~? []|.X.


(** Fixpoint problems are composed only by fixpoint equations *)

Definition fixpoint_Problem (P : Problem) := forall u, set_In u P -> fixpoint_equ u.


(** Proper problems contais only proper terms in its equations. *) 
  
Definition Proper_Problem (P : Problem) :=
  (forall s t, set_In (s~?t) P -> ((Proper_term s) /\ (Proper_term t))) .

(** Right-hand vars of a problem *)

Fixpoint rhvars_Probl (P : Problem) :=
  match P with
  | [] => []
  | (a#?s) :: P0 => rhvars_Probl P0
  | (s~?t) :: P0 => set_union var_eqdec (term_vars t) (rhvars_Probl P0)
  end.  


(** Building freshness contexts over a variable *)

Fixpoint fresh_context (S : set Atom) (X : Var) :=
  match S with
    | [] => []
    | a :: S0 => (a, X) :: fresh_context S0 X
  end.




(** Lemmas *)

(** Decidability of existence of equations and freshness constraints
  in a problem *)

Lemma  set_In_equ_Problem_eqdec : forall P, {exists s, exists t, set_In (s~?t) P} + {forall s t, ~ set_In (s~?t) P}.
Proof.
  intros. induction P.
  right~. destruct IHP.
  left~.  destruct e. destruct H.
  exists x. exists x0. right~.
  destruct a. right~; intros. intro H.
  simpl in H. destruct H. inverts H.
  apply (n s t0); trivial.
  left~. exists t. exists t0. left~.
Qed.   

Lemma set_In_fresh_Problem_eqdec : forall P, {exists a, exists s, set_In (a#?s) P} + {forall a s, ~ set_In (a#?s) P}.
Proof.
  intros. induction P.
  right~. destruct IHP.
  left~.  destruct e. destruct H.
  exists x. exists x0. right~.
  destruct a. left~. exists a. exists t. left~.
  right~; intros. intro H. simpl in H.
  destruct H. inverts H. apply (n a s); trivial.
Qed.


(** Basic results about fixpoint equations and fixpoint problems *)

Lemma fixpoint_equ_eqdec : forall u, {fixpoint_equ u} + {~ fixpoint_equ u}.
Proof.
  intros. unfold fixpoint_equ. destruct u.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  destruct t. 
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  destruct t0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  destruct p0.
  case (perm_eqdec p ([])); intro H'.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.
  symmetry in H1; contradiction.
  case (var_eqdec v v0); intro H. rewrite H.
  left~. exists p. exists v0. split~.
  right~. intro H''. destruct H''. destruct H0. destruct H0. inverts H1. 
  apply H; trivial.
  right~. intro H. destruct H. destruct H. destruct H. inverts H0.   
Qed.

Lemma fixpoint_Problem_nil : fixpoint_Problem ([]).
Proof.
  unfold fixpoint_Problem; intros. simpl in H. contradiction.
Qed.

Lemma fixpoint_Problem_eqdec : forall P, {fixpoint_Problem P} + {~ fixpoint_Problem P}.
Proof.
  intro. induction P. left~. apply fixpoint_Problem_nil.
  destruct IHP. case (fixpoint_equ_eqdec a); intro H.
  left~. unfold fixpoint_Problem in *|-*; intros.
  simpl in H0. destruct H0. rewrite <- H0; trivial.
  apply f; trivial.
  right~. intro H'. apply H.
  unfold fixpoint_Problem in H'. apply H'. left~.
  right~. intro H. apply n. clear n.
  unfold fixpoint_Problem in *|-*; intros.
  apply H. right~.
Qed.

Lemma non_fixpoint_equ_proj : forall P, ~ fixpoint_Problem (equ_proj P) ->
                              exists s t, set_In (s~?t) P /\ ~ fixpoint_equ (s~?t).          
Proof.
  intros. induction P.
  false. apply H; intros. simpl.
  apply fixpoint_Problem_nil.
  destruct a. simpl in *|-*.
  apply IHP in H. destruct H. destruct H.
  exists x. exists x0. destruct H. split~.
  simpl in H. case (fixpoint_equ_eqdec (t ~? t0)); intro H0.
  destruct IHP. intro H1. apply H.
  unfold fixpoint_Problem; intros.
  simpl in H2. destruct H2. rewrite <- H2; trivial. apply H1; trivial.
  destruct H1. destruct H1. exists x. exists x0. split~. simpl. right~.
  exists t. exists t0. split~. left~.
Qed.


Lemma set_In_fixpoint_eq_proj : forall P,  (forall s t,  set_In (s ~? t) P -> fixpoint_equ (s ~? t)) ->
                                            fixpoint_Problem (equ_proj P).
Proof.
  intros. case (fixpoint_Problem_eqdec (equ_proj P)); intro H1; trivial.
  apply non_fixpoint_equ_proj in H1.
  case H1; clear H1; intros s H1. case H1; clear H1; intros t H1.
  destruct H1. apply H in H0. contradiction.
Qed.

Lemma fixpoint_not_In_fresh : forall P, fixpoint_Problem (equ_proj P) ->
                                        (forall (a : Atom) (s : term), ~ set_In (a #? s) P) ->
                                        fixpoint_Problem P.
Proof.
  intros. induction P.
  apply fixpoint_Problem_nil. destruct a.
  false. apply (H0 a t). left~.
  simpl in H. unfold fixpoint_Problem; intros.
  simpl in H1. destruct H1. rewrite <- H1.
  apply H. left~. apply IHP; intros; trivial.
  unfold fixpoint_Problem; intros. apply H. right~.
  assert (Q : ~ set_In (a #? s) ((t ~? t0) :: P)). apply H0.
  intro H2. apply Q. right~.
Qed. 

(** Basic results about subsets of equations and freshness constraints *)

Lemma fresh_not_In_equ_proj : forall a s P, ~ set_In (a #? s) (equ_proj P).
Proof.
  intros. intro H. induction P.
  simpl in H; trivial. destruct a0; simpl in H; try contradiction.
  destruct H. inverts H. contradiction.
Qed.

Lemma equ_proj_append : forall P P',  equ_proj (P ++ P') =
                                     (equ_proj P)++(equ_proj P').
Proof.
  intros. induction P; simpl; trivial.
  destruct a; trivial. simpl. fequals.
Qed.

Lemma fresh_proj_append : forall P P',  fresh_proj (P ++ P') =
                                       (fresh_proj P)++(fresh_proj P').
Proof.
  intros. induction P; simpl; trivial.
  destruct a; trivial. simpl. fequals.
Qed.

Lemma equ_proj_set_In_eq : forall P s t, set_In (s~?t) P <-> set_In (s~?t) (equ_proj P).
Proof.
  intros. induction P; simpl. split~; intro; trivial.
  destruct a. split~; intro. destruct H. inverts H.
  apply IHP; trivial. right~. apply IHP; trivial.
  simpl. split~; intro. destruct H.
  left~. right~. apply IHP; trivial.
  destruct H. left~. right~.
  apply IHP; trivial.  
Qed.

Lemma equ_proj_rem_eq : forall P u, equ_proj (P\u) = (equ_proj P)\u .
Proof.
  intros. induction P; simpl; trivial.
  destruct a. case (Constraint_eqdec u (a #? t)); intro H.
  rewrite H. clear IHP H. induction P; simpl; trivial.
  destruct a0; trivial. rewrite IHP; trivial.
  simpl. case (Constraint_eqdec (a #? t) (t0 ~? t1)); intro H. inverts H.
  rewrite <- 2 IHP; trivial. simpl; trivial.
  case (Constraint_eqdec u (t ~? t0)); intro H.
  rewrite H. simpl. case (Constraint_eqdec (t ~? t0) (t ~? t0)); intro H0; trivial.
  false. simpl. case (Constraint_eqdec u (t ~? t0)); intro H0; try contradiction.
  rewrite IHP. trivial. 
Qed.

Lemma equ_proj_add_fresh : forall P a s, equ_proj (P|+(a#?s)) = equ_proj P .
Proof.
  intros. case (in_dec Constraint_eqdec (a#?s) P); intro H.
  rewrite set_add_In; trivial. rewrite set_add_not_In; trivial.
  rewrite equ_proj_append; trivial. simpl.
  rewrite app_nil_r; trivial.
Qed.

Lemma fresh_proj_add_equ : forall P s t, fresh_proj (P|+(s~?t)) = fresh_proj P.
Proof.
  intros. case (in_dec Constraint_eqdec (s~?t) P); intro H.
  rewrite set_add_In; trivial. rewrite set_add_not_In; trivial.
  rewrite fresh_proj_append. simpl.
  rewrite app_nil_r; trivial.
Qed.  
  
Lemma equ_proj_rem_fresh : forall P a s, equ_proj (P\(a#?s)) = equ_proj P .
Proof.
  intros. induction P; simpl; trivial.
  destruct a0.
  case (Constraint_eqdec (a #? s) (a0 #? t)); intro H0; trivial.
  case (Constraint_eqdec (a #? s) (t ~? t0)); intro H1; trivial.
  inverts H1. simpl. rewrite IHP; trivial.
Qed.

Lemma fresh_proj_rem_equ : forall P s t, fresh_proj (P\(s~?t)) = fresh_proj P .
Proof.
  intros. induction P; simpl; trivial. destruct a.
  case (Constraint_eqdec (s ~? t) (a #? t0)); intro H0. inverts H0.
  simpl. rewrite IHP. trivial.
  case (Constraint_eqdec (s ~? t) (t0 ~? t1)); intro H1; trivial.
Qed.

Lemma equ_proj_add_eq : forall P s t, equ_proj (P|+(s~?t)) = (equ_proj P)|+(s~?t).
Proof.
  intros. case (in_dec Constraint_eqdec (s~?t) P); intro H.
  rewrite 2 set_add_In; trivial. apply -> equ_proj_set_In_eq; trivial.
  rewrite 2 set_add_not_In; trivial.
  rewrite equ_proj_append; trivial.
  intro. apply H. apply equ_proj_set_In_eq; trivial.
Qed.

Lemma equ_proj_union : forall P P', equ_proj (P \cup P') = (equ_proj P) \cup (equ_proj P').
Proof.
  intros. induction P'; simpl; trivial.
  destruct a. rewrite equ_proj_add_fresh; trivial.
  simpl. rewrite equ_proj_add_eq. rewrite IHP'; trivial.
Qed.

Lemma Problem_vars_equ_proj : forall X P,
                              set_In X (Problem_vars (equ_proj P)) -> set_In X (Problem_vars P).
Proof.
  intros. induction P; simpl in *|-*; trivial.
  destruct a. apply set_union_intro2. apply IHP; trivial.
  simpl in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro2. apply IHP; trivial.
Qed.
  
Lemma Problem_exists_equ : forall P, equ_proj P <> [] <-> exists s t, set_In (s~?t) P.
Proof.
  split~; intro.
  induction P.
  simpl in H. false. 
  destruct a. simpl in H. apply IHP in H.
  case H; clear H; intros s0 H. case H; clear H; intros t0 H.
  exists s0. exists t0. simpl. right~.
  simpl. exists t. exists t0. left~.
  case H; clear H; intros s H.
  case H; clear H; intros t H.
  induction P; simpl in H. false.
  destruct H.
  rewrite H. simpl. discriminate.
  apply IHP in H. clear IHP.
  destruct a; simpl; trivial.
  intro H'. inverts H'.
Qed.



(** Basic results about adding and removing constraints and also the operation of union of problems *)

Lemma Problem_add_fresh_rem_equ : forall P a s t u,
                                 (P|+(a#?s))\(t~?u) = (P\(t~?u))|+(a#?s).  
Proof.
  intros. induction P; simpl.
  case (Constraint_eqdec (t~?u) (a#?s)); intro H; trivial. inverts H.  
  case (Constraint_eqdec (a#?s) a0); case (Constraint_eqdec (t~?u) a0); intros H H0; simpl; 
   try rewrite IHP; trivial. 
  rewrite <- H in H0. inverts H0.
  case (Constraint_eqdec (a#?s) a0); case (Constraint_eqdec (t~?u) a0); intros H1 H2;
   try contradiction; trivial.
  case (Constraint_eqdec (t ~? u) a0); intro H1; try contradiction; trivial.  
  case (Constraint_eqdec (a#?s) a0); case (Constraint_eqdec (t~?u) a0); intros H1 H2;
   try contradiction; trivial.
Qed.  

Lemma Problem_vars_remove : forall P X u, set_In X (Problem_vars (P \ u)) ->
                                          set_In X (Problem_vars P).
Proof.
  intros.
  induction P. simpl in H. contradiction.
  simpl in *|-*. gen H. case (Constraint_eqdec u a); destruct a; intros H0 H.
  apply set_union_intro2; trivial.
  apply set_union_intro2; apply set_union_intro2; trivial.
  simpl in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial. apply set_union_intro2; apply IHP; trivial.
  simpl in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  simpl in H. apply set_union_elim in H. destruct H.
  apply set_union_intro2; apply set_union_intro1; trivial.
  apply set_union_intro2; apply set_union_intro2; apply IHP; trivial.
Qed.

Lemma Problem_vars_set_In : forall u X P, set_In u P ->
                                          set_In X (Problem_vars (|[u]|)) -> set_In X (Problem_vars P).  
Proof.
  intros. induction P; simpl in H; try contradiction.
  
  destruct H; destruct a; try rewrite <- H in H0; simpl in *|-*.
  apply set_union_intro1; trivial.
  
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1; trivial.  
  apply set_union_intro2; apply set_union_intro1; trivial. 

  destruct u.
  apply set_union_intro2; apply IHP; trivial.
  apply set_union_intro2; apply IHP; trivial.
  
  destruct u.
  apply set_union_intro2;
  apply set_union_intro2; apply IHP; trivial.
  apply set_union_intro2;
  apply set_union_intro2; apply IHP; trivial. 
Qed.

Lemma Problem_vars_set_In_app : forall X P P',
                                set_In X (Problem_vars (P ++ P'))  <->
                                set_In X (set_union var_eqdec (Problem_vars P) (Problem_vars P')).
Proof.
  intros. induction P; simpl; split~; intros.
  apply set_union_intro2; trivial.
  apply set_union_elim in H. destruct H; trivial.
  simpl in H; contradiction.
  destruct a.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro1; trivial.
  apply IHP in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.  
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro1; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro2;
   apply set_union_intro1; trivial.
  apply IHP in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro2;
   apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.  
  destruct a.
  apply set_union_elim in H. destruct H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply IHP.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply IHP.
  apply set_union_intro2; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro2; apply set_union_intro1; trivial. 
  apply set_union_intro2; apply set_union_intro2. apply IHP.
  apply set_union_intro1; trivial.
  apply set_union_intro2; apply set_union_intro2. apply IHP.
  apply set_union_intro2; trivial.
Qed. 

  
Lemma Problem_vars_add : forall P u X, set_In X (Problem_vars (P|+u)) <->
                         set_In X (set_union var_eqdec (Problem_vars P) (Problem_vars (|[u]|))).  
Proof.
  intros. case (in_dec Constraint_eqdec u P); intro H.
  rewrite set_add_In; trivial. split~; intro.
  apply set_union_intro1; trivial.
  apply set_union_elim in H0. destruct H0; trivial.
  apply Problem_vars_set_In with (u:=u); trivial.
  rewrite set_add_not_In; trivial.
  apply Problem_vars_set_In_app.
Qed.  

Lemma Problem_vars_union : forall P P' X, set_In X (Problem_vars (P \cup P')) <->
                                          set_In X (set_union var_eqdec (Problem_vars P) (Problem_vars P')).
Proof.
  intros. induction P'; simpl. split~; intro; trivial.
  split~; intro. apply Problem_vars_add in H. 
  apply set_union_elim in H. destruct H.
  apply IHP' in H. apply set_union_elim in H.
  destruct H. apply set_union_intro1; trivial.
  destruct a. apply set_union_intro2;
    apply set_union_intro2; trivial.
  apply set_union_intro2;
  apply set_union_intro2;  
  apply set_union_intro2; trivial.
  destruct a. simpl in H.
  apply set_union_intro2;
    apply set_union_intro1; trivial.
  simpl in H. apply set_union_elim in H.
  destruct H. apply set_union_intro2;
    apply set_union_intro1; trivial.
  apply set_union_intro2;
  apply set_union_intro2;  
  apply set_union_intro1; trivial.
  apply set_union_elim in H.
  apply Problem_vars_add. destruct H; simpl.
  apply set_union_intro1. apply IHP'.
  apply set_union_intro1; trivial.
  destruct a; apply set_union_elim in H; destruct H.
  apply set_union_intro2; trivial.
  apply set_union_intro1. apply IHP'.
  apply set_union_intro2; trivial.
  apply set_union_intro2;
    apply set_union_intro1; trivial.
  apply set_union_elim in H; destruct H.
  apply set_union_intro2;
    apply set_union_intro2; trivial.
  apply set_union_intro1. apply IHP'.
  apply set_union_intro2; trivial.
Qed.

(** Sets of variables have no repeated elements *)


Lemma NoDup_term_vars : forall t, NoDup (term_vars t).
Proof.
  intros. induction t; simpl;
  try apply NoDup_nil; trivial.
  apply set_union_nodup; trivial.
  apply NoDup_cons. intro H. simpl in H; trivial.
  apply NoDup_nil; trivial.
Qed.

Lemma NoDup_Problem_vars : forall P, NoDup (Problem_vars P).
Proof.
  intros. induction P; intros.
  apply NoDup_nil.
  destruct a; simpl.
  apply set_union_nodup; trivial.
  apply NoDup_term_vars.
  apply set_union_nodup.
  apply NoDup_term_vars.
  apply set_union_nodup; trivial.
  apply NoDup_term_vars.
Qed.

Open Scope nat_scope.


(** Sizes of sets of variables} % *)

Lemma length_Problem_vars_rem : forall P u,  length (Problem_vars P) >= length (Problem_vars (P\u)).
Proof.
  intros.
  apply nat_leq_inv. apply subset_list; intros.
  apply var_eqdec. apply NoDup_Problem_vars.  
  apply Problem_vars_remove in H. trivial.
Qed.


Lemma length_Problem_vars_add : forall P u,  length (Problem_vars (P|+u)) =
                                             length (set_union var_eqdec (Problem_vars P) (Problem_vars (|[u]|))).
Proof.
  intros. apply subset_list_eq; intros.
  apply var_eqdec. apply NoDup_Problem_vars.
  apply set_union_nodup; apply NoDup_Problem_vars.  
  apply Problem_vars_add.
Qed.
  
  
(**  Auxiliary definitions and lemmas to 
    prove termination of fresh\_sys and equ\_sys *)


Fixpoint fresh_Problem_size (P : Problem) {struct P} : nat :=
  match P with
    | [] => 0
    | (a#?s)::P0 => (term_size s) + (fresh_Problem_size P0)
    | (s~?t)::P0 => (fresh_Problem_size P0)                                      
  end.

Fixpoint equ_Problem_size (P : Problem) {struct P} : nat :=
  match P with
    | [] => 0
    | (a#?s)::P0 => (equ_Problem_size P0)
    | (s~?t)::P0 => (term_size s) + (term_size t) + (equ_Problem_size P0)    
  end.

  
Fixpoint non_fixpoint_equ (P : Problem) {struct P} : nat :=
  match P with
    | [] => 0
    | (a#?s)::P0 => non_fixpoint_equ P0          
    | (s~?t)::P0 => if (fixpoint_equ_eqdec (s~?t)) then (non_fixpoint_equ P0) else
                  (1 + (non_fixpoint_equ P0))
  end.  
           

(** Basic results about the size of problems *)


Lemma equ_Problem_size_term : forall s t,
      equ_Problem_size (|[s~?t]|) = term_size s + term_size t. 
Proof.
  intros. simpl. omega.
Qed.  
  
Lemma fresh_Problem_size_remove : forall P a s, set_In (a#?s) P ->
                         fresh_Problem_size (P\(a#?s)) = fresh_Problem_size P - (term_size s). 
Proof.
  intros. induction P. simpl in H. contradiction.
  simpl in H. destruct H. rewrite H. clear H.
  simpl. case (Constraint_eqdec (a #? s) (a #? s)); intro H. clear H. omega. false. 
  destruct a0. simpl. case (Constraint_eqdec (a #? s) (a0 #? t)); intro H'.
  inverts H'. omega.
  simpl. rewrite IHP; trivial. clear IHP H'.
  assert (Q : fresh_Problem_size P >= term_size s).
   induction P. simpl in H. contradiction. destruct a1.
   simpl in *|-*. destruct H. inverts H. omega.
   apply IHP in H. omega. simpl in H. destruct H.
   inverts H. simpl. apply IHP; trivial.
  omega.
  simpl in *|-*. case (Constraint_eqdec (a #? s) (t ~? t0)); intro H'.
  inverts H'. simpl. rewrite IHP; trivial.
Qed.

Lemma fresh_Problem_size_add : forall P a s,
                               fresh_Problem_size (P|+(a#?s)) <= fresh_Problem_size P + term_size s.
Proof.
  intros. induction P. simpl. omega.
  destruct a0. simpl.
  case (Constraint_eqdec (a #? s) (a0 #? t)); intro H; simpl; try omega.
  simpl. case (Constraint_eqdec (a #? s) (t ~? t0)); intro H.
  inverts H. simpl. trivial.
Qed.    

Lemma fresh_Problem_size_gt_0 : forall a s P, set_In (a#?s) P -> fresh_Problem_size P > 0.
Proof.
  intros. induction P. simpl in H. contradiction.
  destruct a0. simpl in *|-*. destruct H. 
  assert (Q : term_size t > 0).
   apply term_size_gt_0.
  omega. apply IHP in H. omega.
  simpl in *|-*. destruct H.
  inverts H. apply IHP; trivial.
Qed.

Lemma equ_Problem_size_neq_nil : forall u P, set_In u P -> equ_Problem_size P >= equ_Problem_size (|[u]|).
Proof.
  intros. induction P; intros. simpl in H. contradiction.
  simpl in H. destruct H. rewrite H. destruct u. simpl. omega.
  simpl. assert (Q : term_size t > 0). apply term_size_gt_0. omega.
  apply IHP in H. clear IHP. simpl in *|-*. destruct u; destruct a; trivial.
  assert (Q : term_size t0 > 0). apply term_size_gt_0. omega.
  omega.  
Qed.
  
Lemma equ_Problem_size_remove : forall P s t, set_In (s~?t) P ->
                                equ_Problem_size (P\(s~?t)) =  equ_Problem_size P - ((term_size s) + (term_size t)). 
Proof.
  intros. induction P. simpl in H. contradiction.
  simpl in H. destruct H. rewrite H. clear H.
  simpl. case (Constraint_eqdec (s ~? t) (s ~? t)); intro H. clear H.
  omega. false. 
  simpl. destruct a. case (Constraint_eqdec (s ~? t) (a #? t0)); intro H0.
  inverts H0. simpl. apply IHP; trivial.
  case (Constraint_eqdec (s ~? t) (t0 ~? t1)); intro H0.
  inverts H0. omega. simpl. rewrite IHP; trivial.
  assert (Q : equ_Problem_size P >= equ_Problem_size (|[s ~? t]|)).
    apply equ_Problem_size_neq_nil; trivial.
  simpl in Q. omega.
Qed.

Lemma equ_Problem_size_gt_0 : forall s t P, set_In (s~?t) P -> equ_Problem_size P > 0.
Proof.
  intros. induction P. simpl in H. contradiction.
  destruct a. simpl in *|-*. destruct H. inverts H.
  apply IHP in H. clear IHP. trivial. 
  simpl in *|-*. assert (Q : term_size t0 > 0). apply term_size_gt_0.
  omega.  
Qed.

Lemma equ_Problem_size_add : forall P u, equ_Problem_size P + (equ_Problem_size (|[u]|)) >= equ_Problem_size (P|+u). 
Proof.
  intros. induction P. simpl; omega.
  simpl in *|-*. destruct u; destruct a.

  case (Constraint_eqdec (a0 #? t) (a #? t0)); intro H; simpl; try omega.
  case (Constraint_eqdec (a0 #? t) (t0 ~? t1)); intro H; simpl; try omega. 
  case (Constraint_eqdec (t ~? t0) (a #? t1)); intro H; simpl; try omega. 
  case (Constraint_eqdec (t ~? t0) (t1 ~? t2)); intro H; simpl; try omega. 
Qed.


Lemma equ_Problem_size_add' : forall P u,
      ~ set_In u P ->
      equ_Problem_size (P|+u) =
      equ_Problem_size P + equ_Problem_size (|[u]|).
Proof.
  intros. rewrite set_add_not_In; trivial.
  induction P; trivial; simpl in *|-*.
  destruct a; destruct u; rewrite IHP; try omega;
  intro H0; apply H; right~.  
Qed.
  
Lemma equ_Problem_size_add'' : forall P u,
      set_In u P -> equ_Problem_size (P|+u) = equ_Problem_size P.
Proof.
  intros. rewrite set_add_In; trivial.
Qed.


Lemma equ_Problem_size_add_fresh : forall P a s,
                                   equ_Problem_size (P|+(a#?s)) = equ_Problem_size P.  
Proof.
 intros. induction P; simpl; trivial.
 destruct a0.
 case (Constraint_eqdec (a #? s) (a0 #? t)); intro H0; simpl; trivial.
 case (Constraint_eqdec (a #? s) (t ~? t0)); intro H0; simpl; trivial.
 rewrite IHP; trivial.
Qed.

Lemma equ_Problem_size_rem_fresh : forall P a s,
                                   equ_Problem_size (P\(a#?s)) = equ_Problem_size P.  
Proof.
 intros. induction P; simpl; trivial.
 destruct a0.
 case (Constraint_eqdec (a #? s) (a0 #? t)); intro H0; simpl; trivial.
 case (Constraint_eqdec (a #? s) (t ~? t0)); intro H0; simpl; trivial.
 inverts H0. rewrite IHP; trivial.
Qed.
 

Lemma non_fixpoint_equ_gt_0 : forall P s t, set_In (s~?t) P -> ~ fixpoint_equ (s~?t) ->
                                          non_fixpoint_equ P > 0.
Proof.
  intros. induction P; simpl in *|-*; try contradiction.
  destruct a. destruct H. inverts H.
  apply IHP; trivial.
  case (fixpoint_equ_eqdec (t0 ~? t1)); intro H1.
  destruct H. inverts H. contradiction.
  apply IHP; trivial. omega.
Qed.
  
Lemma non_fixpoint_equ_remove : forall P s t, set_In (s~?t) P -> ~ fixpoint_equ (s~?t) ->
                                non_fixpoint_equ (P\(s~?t)) =  non_fixpoint_equ P - 1.
Proof.
  intros. induction P; simpl in *|-*; trivial.
  destruct a. case (Constraint_eqdec (s ~? t) (a #? t0)); intro H1. inverts H1.
  simpl. destruct H. inverts H. apply IHP; trivial.
  case (Constraint_eqdec (s ~? t) (t0 ~? t1)); intro H1.
  case (fixpoint_equ_eqdec (t0 ~? t1)); intro H2.
  inverts H1. contradiction. omega.
  simpl. case (fixpoint_equ_eqdec (t0 ~? t1)); intro H2.
  destruct H. inverts H. contradiction. apply IHP; trivial.
  destruct H. inverts H. false.
  generalize H. intro H3. apply IHP in H3. 
  assert (Q : non_fixpoint_equ P > 0).
   apply non_fixpoint_equ_gt_0 with (s := s) (t:=t); trivial.
  omega.
Qed.

Lemma non_fixpoint_equ_add : forall P pi X, pi <> [] -> non_fixpoint_equ (P|+(pi|.X~?([]|.X))) =
                                            non_fixpoint_equ P.
Proof.
  intros. induction P; simpl.
  case (fixpoint_equ_eqdec ((pi|.X) ~? (([])|.X))); intro H0; trivial.
  false. apply H0. unfold fixpoint_equ. exists pi. exists X. split~.
  destruct a.
  case (Constraint_eqdec ((pi|.X) ~? (([])|.X)) (a #? t)); intro H0.
  inverts H0. simpl. rewrite IHP; trivial.
  case (Constraint_eqdec ((pi|.X) ~? (([])|.X)) (t ~? t0)); intro H0; simpl; trivial.
  case (fixpoint_equ_eqdec (t ~? t0)); intro H1; trivial.
  omega.
Qed.


Lemma non_fixpoint_equ_add_fresh : forall P a s,
                                   non_fixpoint_equ (P|+(a#?s)) = non_fixpoint_equ P.  
Proof.
  intros. induction P; simpl; trivial.
  destruct a0.
  case (Constraint_eqdec (a #? s) (a0 #? t)); intro H0; simpl; trivial.
  case (Constraint_eqdec (a #? s) (t ~? t0)); intro H0; simpl; trivial.
  rewrite IHP; trivial.
Qed.

Lemma non_fixpoint_equ_rem_fresh : forall P a s,
                                   non_fixpoint_equ (P\(a#?s)) = non_fixpoint_equ P.  
Proof.
 intros. induction P; simpl; trivial.
 destruct a0.
 case (Constraint_eqdec (a #? s) (a0 #? t)); intro H0; simpl; trivial.
 case (Constraint_eqdec (a #? s) (t ~? t0)); intro H0; simpl; trivial.
 inverts H0. rewrite IHP; trivial.
Qed.


(** Characterising the memebers of the set (fresh_context St X)  *)

Lemma fresh_context_mem : forall a X Y St, set_In (a, Y) (fresh_context St X) <->
                                           (X = Y /\ set_In a St).
Proof.
  intros. induction St;
    simpl; split~; intros; try contradiction.
  destruct H; trivial.
  destruct H. inverts H. split~.
  apply IHSt in H. destruct H. split~.
  destruct H. rewrite H in *|-*. destruct H0.
  rewrite H0. left~. right~. 
  apply <- IHSt. split~.
Qed.
  
(* If a term is an right-hand position of a problem P, its 
   varialbes are in the set rhvars_Probl *)

Lemma rh_term_Probl_vars : forall s t P, set_In (s~?t) P ->
                           (forall X, set_In X (term_vars t) -> set_In X (rhvars_Probl P)).              
Proof.
  intros. induction P; simpl in *|-*; trivial.
  destruct H. rewrite H. apply set_union_intro1; trivial.
  apply IHP in H. clear IHP H0.
  destruct a; trivial. apply set_union_intro2; trivial.
Qed.


(* If X is a right-hand var in (P\u) then it is in P *)

Lemma rhvars_Prob_rem : forall X P u, set_In X (rhvars_Probl (P\u)) ->
                                      set_In X (rhvars_Probl P).
Proof.
  intros. induction P; simpl in *|-*; auto.
  gen H. case (Constraint_eqdec u a); intros H H0.
  rewrite H in *|-*. clear H. destruct a; simpl in *|-*; auto.
  apply set_union_intro2; trivial.
  simpl in H0. destruct a; auto.
  apply set_union_elim in H0. apply set_union_intro.
  destruct H0; auto.
Qed.  
  
Lemma rhvars_Prob_add : forall X P u, set_In X (rhvars_Probl (P|+u)) ->
                                      (set_In X (rhvars_Probl (|[u]|)) \/ set_In X (rhvars_Probl P)).
Proof.
  intros. induction P; simpl in *|-*; auto.
  gen H. case (Constraint_eqdec u a); intros H H0.
  rewrite H in *|-*. clear H. destruct a; simpl in *|-*; auto.
  destruct u; destruct a; simpl in *|-*; auto.
  apply set_union_elim in H0. right~. destruct H0.
  apply set_union_intro1; trivial.
  apply IHP in H0. destruct H0; try contradiction.
  apply set_union_intro2; trivial.
  apply set_union_elim in H0. destruct H0.
  right~. apply set_union_intro1; trivial.
  apply IHP in H0. destruct H0; auto.
  right~. apply set_union_intro2; trivial.
Qed.  
  

Lemma rhvars_Prob_union : forall P P' X, set_In X (rhvars_Probl (P \cup P')) ->
                                         (set_In X (rhvars_Probl P) \/ set_In X (rhvars_Probl P')).
Proof.
  intros. induction P'; simpl in *|-*; auto.
  apply rhvars_Prob_add in H. destruct a; simpl in *|-*.
  destruct H; try contradiction. apply IHP'; trivial.
  destruct H. right~. apply set_union_intro1; trivial.
  apply IHP' in H. destruct H; auto.
  right~. apply set_union_intro2; trivial.
Qed.
