(**
%\begin{verbatim}
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : C_Unif.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : This file is dedicated to the definition of 
               the C-unification algorithm and somes basics
               results over this definition.


 Last Modified On: Nomvember 10, 2017.
 ============================================================================
\end{verbatim}%
*)

Require Export Substs.


(** %\section{Definition of a solution for a C-unification problem}% *)

Definition sol_c (Sl : Context * Subst) (T : Triple) :=
  let C := (fst (fst T)) in
  let S := (snd (fst T)) in
  let P := (snd T) in
  let D := (fst Sl) in
  let W := (snd Sl) in
(* 1 *) ( fresh_env C D W ) /\
(* 2 *) ( forall a t, set_In (a#?t) P -> D |- a # (t|^W) ) /\
(* 3 *) ( forall s t, set_In (s~?t) P -> D |- (s|^W) ~c (t|^W) ) /\
(* 4 *) ( exists S'', D |- (S©S'') ~:c W ) .
                                    

(** %\section{The fresh\_sys relation}% *)

Inductive fresh_sys : Triple -> Triple -> Prop :=
  
 | fresh_sys_Ut : forall C S P a, (set_In (a#?(<<>>)) P) ->
                                  fresh_sys (C,S,P)
                                            (C,S,P\(a#?(<<>>)))
                                         
  
 | fresh_sys_At : forall C S P a b, a <> b -> (set_In (a#?(%b)) P) ->
                                    fresh_sys (C,S,P)
                                              (C,S,(P\(a#?(%b))))

 | fresh_sys_Fc : forall C S P a E n s, (set_In (a#?(Fc E n s)) P) ->
                                        fresh_sys (C,S,P)
                                                  (C,S,(P|+(a#?s))\(a#?(Fc E n s))) 

 | fresh_sys_Ab_1 : forall C S P a s, (set_In (a#?([a]^s)) P) ->
                                      fresh_sys (C,S,P)
                                                (C,S,(P\(a#?([a]^s))))  

 | fresh_sys_Ab_2 : forall C S P a b s, a <> b -> (set_In (a#?([b]^s)) P) ->
                                        fresh_sys (C,S,P)
                                                  (C,S,(P|+(a#?s))\(a#?([b]^s)))

 | fresh_sys_Su : forall C S P a pi X, (set_In (a#?(pi|.X)) P) ->
                                       fresh_sys (C,S,P)
                                                 (C|++((!pi) $ a,X),S,(P\(a#?(pi|.X))))                                                   
 | fresh_sys_Pr : forall C S P a s t, (set_In (a#?(<|s,t|>)) P) ->
                                      fresh_sys (C,S,P)
                                                (C,S,(((P|+(a#?s))|+(a#?t))\(a#?(<|s,t|>))))   
.

(** %\section{The equ\_sys relation}% *)
            
Inductive equ_sys : Triple -> Triple -> Prop :=
  
 | equ_sys_refl : forall C S P s, (set_In (s~?s) P) ->
                                   equ_sys (C,S,P)
                                           (C,S,P\(s~?s))
                                           
 | equ_sys_Pr : forall C S P s0 s1 t0 t1,
                  (set_In ((<|s0,s1|>)~?(<|t0,t1|>)) P) ->
                   equ_sys (C,S,P)
                           (C,S,(((P|+(s0~?t0))|+(s1~?t1))\((<|s0,s1|>)~?(<|t0,t1|>))))
                           
                          
 | equ_sys_Fc : forall C S P E n t t', (set_In ((Fc E n t)~?(Fc E n t')) P) -> E <> 2 ->
                                                                                      
                                        equ_sys (C,S,P)
                                                (C,S,(P|+(t~?t'))\((Fc E n t)~?(Fc E n t'))) 


 | equ_sys_C1 : forall C S P n s0 s1 t0 t1,    
                  
   (set_In ((Fc 2 n (<|s0,s1|>))~?(Fc 2 n (<|t0,t1|>)))) P ->
                  
     equ_sys (C,S,P)
             (C,S,((P|+(s0~?t0))|+(s1~?t1))\(Fc 2 n (<|s0,s1|>)~?(Fc 2 n (<|t0,t1|>))))


 | equ_sys_C2 : forall C S P n s0 s1 t0 t1,    
                  
   (set_In ((Fc 2 n (<|s0,s1|>))~?(Fc 2 n (<|t0,t1|>)))) P ->
                  
     equ_sys (C,S,P)
             (C,S,((P|+(s0~?t1))|+(s1~?t0))\(Fc 2 n (<|s0,s1|>)~?(Fc 2 n (<|t0,t1|>))))


 | equ_sys_Ab1 : forall C S P a t t', (set_In (([a]^t)~?([a]^t')) P) ->
                                       equ_sys (C,S,P)
                                               (C,S,(P|+(t~?t'))\(([a]^t)~?([a]^t')))

 | equ_sys_Ab2 : forall C S P a b t t',
                    a <> b -> (set_In (([a]^t)~?([b]^t')) P) ->
                    equ_sys (C,S,P)
                            (C,S,((P|+(t~?([(a,b)]@t'))|+(a#?t')))\(([a]^t)~?([b]^t')))

 | equ_sys_inst : forall C S S' P pi X t,

                    (~ set_In X (term_vars t)) ->

                    ((set_In (pi|.X~?t) P) \/ (set_In (t~?(pi|.X)) P)) ->

                    S' = S©([(X,(!pi)@t)]) ->

                    equ_sys (C,S,P)
                            (C,S',((P\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))\cup(C/?S'))
                                                          
 | equ_sys_inv : forall C S P pi pi' X,
                   pi <> pi' -> pi' <> [] -> (set_In ((pi|.X)~?(pi'|.X)) P) ->
                   equ_sys (C,S,P)
                   (C,S,(P|+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X)))
.

(** %\section{Definition of valid triples}% *)

Definition valid_triple (T : Triple) :=
  let C := (fst (fst T)) in
  let S := (snd (fst T)) in
  let P := (snd T) in
  (* 1 *) ( set_inter Var_eqdec (dom_rec S) (Problem_vars P) = [] ) /\
  (* 2 *) ( set_inter Var_eqdec (dom_rec S) (im_vars S) = [] ) .


(** %\section{Definition of proper terms and proper problems}% *)  
  
(**
	The following is a restriction over the syntax. 
	Commutative function symbols can have only pairs as 
	arguments.
*)  
  
Definition Proper_term (t : term) :=
  forall n s, set_In (Fc 2 n s) (subterms t) -> is_Pr s .

(**
	Proper problems contais only proper terms in its equations.
*) 
  
Definition Proper_Problem (P : Problem) :=
  (forall s t, set_In (s~?t) P -> ((Proper_term s) /\ (Proper_term t))) .

  
(** %\section{Definitions of normal forms and of a reflexive-transitive closure}% *)    
  
Definition NF (T:Type) (R:T->T->Prop) (s:T) := forall t, ~ R s t.

Inductive tr_clos (T:Type) (R:T->T->Prop) : T->T->Prop :=
 | tr_rf : forall s, tr_clos T R s s
 | tr_os : forall s t, R s t -> tr_clos T R s t
 | tr_ms : forall s t u, R s t -> tr_clos T R t u -> tr_clos T R s u
.


(** %\section{Definition of unif\_step}% *) 

(**
	A unification step is an equ_sys reduction,
	or a fresh_sys reduction over a triple whose equational 
	constraints are all fixpoint equations.
*)

Inductive unif_step : Triple -> Triple -> Prop :=

 | equ_unif_step   : forall T T', equ_sys T T' -> unif_step T T'
  
 | fresh_unif_step : forall T T', fixpoint_Problem (equ_proj (snd T)) ->
                                  fresh_sys T T' -> unif_step T T'
.
 
(** %\section{Definition of leaf and unif\_path}% *) 
 
(**
	A leaf T is a normal form of relation unif_step.
*) 
 
Definition leaf (T : Triple) := NF _ unif_step T .  

(**
	A unifcation path from T to T' (unif_path T T') is zero
	or more steps of unif_step from T and T' 
	where T' is a normal form (w.r.t. unif_path), ie, a leaf.
*) 

Definition unif_path (T T' : Triple) := tr_clos _ unif_step T T' /\ leaf T'.

 

(** %\section{Some basic lemmas regarding fresh\_sys, equ\_sys, unif\_step and unif\_path}% *) 

(** 
	If all equational constraints of P in T = (C, S, P) 
	are fixpoint equations, then T is a normal form w.r.t equ_sys. 
*)
  
Lemma equ_proj_fixpoint_is_NF : forall C S P, fixpoint_Problem (equ_proj P) ->
                                NF _ equ_sys (C,S,P).
Proof.
  intros. unfold NF; intro T. intro H0.
  unfold fixpoint_Problem in H.
  unfold fixpoint_equ in H.
  destruct T. destruct p.
  inverts H0;
    try apply equ_proj_set_In_eq in H2;
    try apply equ_proj_set_In_eq in H3;  
    try apply H in H2; try destruct H2;
    try apply H in H3; try destruct H3;
    try destruct H0; try destruct H0; try inverts H1.
  inverts H4. apply H0; trivial.
  apply equ_proj_set_In_eq in H8.
  apply H in H8. destruct H8.
  destruct H0. destruct H0. inverts H1. 
  destruct H8;  apply equ_proj_set_In_eq in H0;  apply H in H0;
  destruct H0; destruct H0; destruct H0; inverts H1;
  apply H5; simpl; left~.
  apply equ_proj_set_In_eq in H9. apply H in H9.
  destruct H9. destruct H0. destruct H0.  
  inverts H1. apply H8; trivial.
Qed.

(** 
	The fixpoint equations are preserved by unif_step 
*)


Lemma fixpoint_preserv : forall T T',
                           unif_step T T' ->
                           fixpoint_Problem (equ_proj (snd T)) -> 
                           fixpoint_Problem (equ_proj (snd T')).
Proof.
  intros. destruct H. destruct T. destruct p.
  simpl in H0. apply equ_proj_fixpoint_is_NF with (C:=c) (S:=s) in H0.
  apply H0 in H. contradiction.
  inverts H1; simpl in *|-*;
  rewrite equ_proj_rem_eq; rewrite set_remove_eq;
  try apply fresh_not_In_equ_proj;
  try rewrite equ_proj_add_fresh; trivial.
  rewrite equ_proj_add_fresh; trivial.  
Qed.
                                       
(** 
	%\subsection{Problem properness is preserved by fresh\_sys, equ\_sys, unif\_step and unif\_path}% 
*)

  
Lemma Proper_subterm : forall s t, set_In s (subterms t) -> Proper_term t -> Proper_term s.
Proof.
  intros. unfold Proper_term in *|-*; intros.
  apply H0 with (n:=n).
  apply subterms_trans with (t := s); trivial.
Qed.

Lemma perm_is_Pr : forall pi t, is_Pr t -> is_Pr (pi @ t).
Proof.
  intros. induction t; autorewrite with perm; simpl in *|-*; trivial.
Qed.

Lemma subs_is_Pr : forall s t X, is_Pr s -> is_Pr (s|^([(X,t)])).
Proof.
  intros. induction s; simpl in *|-*; trivial.
  contradiction.
Qed.

Lemma perm_Proper_term : forall pi t, Proper_term t -> Proper_term (pi @ t) .
Proof.
  intros. induction t; autorewrite with perm; trivial.
  unfold Proper_term; intros. 
  simpl in H0. destruct H0; try contradiction. inverts H0.
  unfold Proper_term in *|-*; intros. apply IHt with (n:=n); intros.
  apply H with (n:=n0). simpl. apply set_add_intro1; trivial.
  simpl in H0. apply set_add_elim in H0. destruct H0; trivial. inverts H0.
  unfold Proper_term in *|-*; intros.
  simpl in H0. apply set_add_elim in H0. destruct H0. inverts H0.
  apply set_union_elim in H0. destruct H0.
  apply IHt1 with (n:=n); intros; trivial. 
  apply H with (n := n0). simpl.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply IHt2 with (n:=n); intros; trivial. 
  apply H with (n := n0). simpl.
  apply set_add_intro1. apply set_union_intro2; trivial.
  unfold Proper_term in *|-*; intros.
  simpl in H0. apply set_add_elim in H0. destruct H0.
  inverts H0. apply perm_is_Pr. apply H with (n:=n0).
  simpl. apply set_add_intro2; trivial.
  apply IHt with (n:=n1); trivial; intros.
  apply H with (n1:=n2); trivial. simpl.
  apply set_add_intro1; trivial.
  unfold Proper_term in *|-*; intros.
  simpl in H0. destruct H0; try contradiction. inverts H0.
Qed.


Lemma subs_Proper_term : forall s t X, Proper_term s -> Proper_term t -> Proper_term (s|^([(X,t)])).
Proof.
  intros. induction s; simpl; trivial.
  unfold Proper_term in *|-*; intros.
  simpl in H1. apply set_add_elim in H1; destruct H1. inverts H1.
  apply IHs with (n:=n); intros; trivial. apply H with (n:=n0); trivial.
  simpl. apply set_add_intro1; trivial.
  unfold Proper_term in *|-*; intros.
  simpl in H1. apply set_add_elim in H1; destruct H1. inverts H1.
  apply set_union_elim in H1. destruct H1.
  apply IHs1 with (n:=n); intros; trivial. apply H with (n:=n0); trivial.
  simpl. apply set_add_intro1. apply set_union_intro1; trivial.
  apply IHs2 with (n:=n); intros; trivial. apply H with (n:=n0); trivial.
  simpl. apply set_add_intro1. apply set_union_intro2; trivial.
  unfold Proper_term in *|-*; intros.
  simpl in H1. apply set_add_elim in H1; destruct H1. inverts H1.
  apply subs_is_Pr. apply H with (n:=n0). simpl. apply set_add_intro2; trivial.
  apply IHs with (n:=n1); intros; trivial. apply H with (n1:=n2); trivial.
  simpl. apply set_add_intro1; trivial.
  case (X ==v v); intro H1; autorewrite with perm; simpl; trivial.
  apply perm_Proper_term; trivial.
Qed.

  
Lemma fresh_Proper_Problem : forall T T', fresh_sys T T' ->
                                          Proper_Problem (snd T) -> Proper_Problem (snd T').
Proof.
  intros. destruct T. destruct T'. simpl in *|-*.
  destruct p. destruct p1. unfold Proper_Problem in *|-*; intros.
  inverts H; apply set_remove_1 in H1; apply H0; trivial; 
  try apply set_add_elim in H1; try  destruct H1; try inverts H; trivial.
  apply set_add_elim in H. destruct H; trivial. inverts H.
Qed.  


Lemma equ_Proper_Problem : forall T T', equ_sys T T' ->
                                        Proper_Problem (snd T) -> Proper_Problem (snd T').
Proof.
  intros. destruct T. destruct T'. simpl in *|-*.
  destruct p. destruct p1. unfold Proper_Problem in *|-*; intros.
  inverts H; try apply set_remove_1 in H1.
  apply H0; trivial.
  apply set_add_elim in H1. destruct H1. inverts H.
  apply H0 in H3. destruct H3. split~.
  apply Proper_subterm with (t :=<|s2,s3|>); trivial. 
  simpl. apply set_add_intro1. apply set_union_intro2. apply In_subterms.
  apply Proper_subterm with (t :=<|t0,t1|>); trivial. 
  simpl. apply set_add_intro1. apply set_union_intro2. apply In_subterms.
  apply set_add_elim in H. destruct H. inverts H. apply H0 in H3. destruct H3. split~. 
  apply Proper_subterm with (t :=<|s2,s3|>); trivial. 
  simpl. apply set_add_intro1. apply set_union_intro1. apply In_subterms.
  apply Proper_subterm with (t :=<|t0,t1|>); trivial. 
  simpl. apply set_add_intro1. apply set_union_intro1. apply In_subterms.
  apply H0; trivial.
  apply set_add_elim in H1. destruct H1. inverts H.
  apply H0 in H4. destruct H4. split~.
  apply Proper_subterm with (t :=Fc E n t0); trivial.  
  simpl. apply set_add_intro1. apply In_subterms.  
  apply Proper_subterm with (t :=Fc E n t'); trivial.  
  simpl. apply set_add_intro1. apply In_subterms.
  apply H0; trivial.
  apply H0 in H3. destruct H3. 
  apply set_add_elim in H1. destruct H1. inverts H1. split~.
  apply Proper_subterm with (t :=Fc 2 n (<|s2,s3|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro2. apply In_subterms.
  apply Proper_subterm with (t :=Fc 2 n (<|t0,t1|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro2. apply In_subterms.
  apply set_add_elim in H1. destruct H1. inverts H1. split~.
  apply Proper_subterm with (t :=Fc 2 n (<|s2,s3|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro1. apply In_subterms.
  apply Proper_subterm with (t :=Fc 2 n (<|t0,t1|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro1. apply In_subterms.  
  apply H0; trivial.
  apply H0 in H3. destruct H3. 
  apply set_add_elim in H1. destruct H1. inverts H1. split~.
  apply Proper_subterm with (t :=Fc 2 n (<|s2,s3|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro2. apply In_subterms.
  apply Proper_subterm with (t :=Fc 2 n (<|t0,t1|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro1. apply In_subterms.
  apply set_add_elim in H1. destruct H1. inverts H1. split~.
  apply Proper_subterm with (t :=Fc 2 n (<|s2,s3|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro1. apply In_subterms.
  apply Proper_subterm with (t :=Fc 2 n (<|t0,t1|>)); trivial. 
  simpl. apply set_add_intro1. apply set_add_intro1.
  apply set_union_intro2. apply In_subterms.  
  apply H0; trivial.
  apply set_add_elim in H1. destruct H1. inverts H.
  apply H0 in H3. destruct H3. split~.
  apply Proper_subterm with (t :=[a]^t0); trivial.  
  simpl. apply set_add_intro1. apply In_subterms.  
  apply Proper_subterm with (t :=[a]^t'); trivial.  
  simpl. apply set_add_intro1. apply In_subterms.
  apply H0; trivial.
  apply set_add_elim in H1. destruct H1. inverts H.
  apply set_add_elim in H. destruct H. inverts H.  
  apply H0 in H9. destruct H9. split~.
  apply Proper_subterm with (t :=[a]^t0); trivial.
  simpl. apply set_add_intro1. apply In_subterms.
  apply perm_Proper_term.
  apply Proper_subterm with (t :=[b]^t'); trivial.
  simpl. apply set_add_intro1. apply In_subterms.
  apply H0; trivial.
  apply set_union_elim in H1. destruct H1.
  apply set_In_subs_remove_problem in H.
  apply set_In_subs_remove_problem in H.
  apply set_In_subs in H.
  case H; clear H; intros u H. destruct H.
  destruct u. simpl in H. inverts H.
  simpl in H. inverts H.
  apply H0 in H1. destruct H1.
  split; apply subs_Proper_term; trivial;
  apply perm_Proper_term; destruct H9; apply H0 in H2; destruct H2; trivial.
  apply equ_subs_fresh in H. contradiction.
  apply set_add_elim in H1.
  destruct H1. inverts H.
  split; unfold Proper_term; intros; simpl in H; destruct H;
   try contradiction; inverts H.
  apply H0; trivial.  
Qed.


Lemma unif_step_Proper_Problem : forall T T', unif_step T T' ->
                                              Proper_Problem (snd T) -> Proper_Problem (snd T').
Proof.
  intros. inverts H.
  apply equ_Proper_Problem with (T:=T); trivial.
  apply fresh_Proper_Problem with (T:=T); trivial.
Qed.

Lemma unif_path_Proper_Problem : forall T T', unif_path T T' ->
                                              Proper_Problem (snd T) -> Proper_Problem (snd T').
Proof.
  intros. inverts H. induction H1; trivial.
  apply unif_step_Proper_Problem with (T:=s); trivial.
  apply IHtr_clos; trivial.
  apply unif_step_Proper_Problem with (T:=s); trivial. 
Qed.
  

(** 
	%\subsection{Validity is preserved by fresh\_sys, equ\_sys, unif\_step and unif\_path}% 
*)


Lemma fresh_valid_preservation : forall T T', valid_triple T -> fresh_sys T T' -> valid_triple T'.
Proof.
  intros. unfold valid_triple in *|-*. destruct H;
  destruct H0; simpl in *|-*; split~;
  apply set_inter_nil; intro X0; apply set_inter_nil with (a:=X0) in H;
  intro H'; apply H; clear H; apply set_inter_elim in H';
  case H'; clear H'; intros Q Q';
  apply set_inter_intro; trivial;
  try apply Problem_vars_remove in Q';
  try apply Problem_vars_add in Q';
  try apply set_union_elim in Q';
  try destruct Q'; 
  try apply Problem_vars_add in H;
  try apply set_union_elim in H;
  try destruct H; try simpl in H;
  try apply set_union_elim in H;
  try destruct H; trivial;
  try apply Problem_vars_set_In
  with (X:=X0) in H0; simpl; trivial.
  apply Problem_vars_set_In with (X:=X0) in H2; simpl; trivial.
  apply set_union_intro1; trivial.
  apply set_union_intro2; trivial.
Qed.


Lemma equ_valid_preservation_aux : forall T T',
                     valid_triple T -> equ_sys T T' ->
                     (set_inter Var_eqdec (dom_rec (snd (fst T'))) (im_vars (snd (fst T'))) = []) .
                                                
Proof.
  intros. unfold valid_triple in *|-. destruct H;
    destruct H0; simpl in *|-*; trivial.

  assert (Q : ~ set_In X (dom_rec S)).
   apply set_inter_nil with (a:=X) in H.
   intro H4. apply H. apply set_inter_intro; trivial.
   destruct H2;
     apply Problem_vars_set_In with (X:=X) in H2; simpl; trivial.
   apply set_union_intro1; simpl; left~.
   apply set_add_intro2; trivial.

  assert (Q' : set_inter Var_eqdec (dom_rec S) (term_vars t) = []).
   apply set_inter_nil. intro Y. intro H4.
   apply set_inter_elim in H4. destruct H4.
   apply set_inter_nil with (a:=Y) in H.
   apply H. apply set_inter_intro; trivial.
   destruct H2;
     apply Problem_vars_set_In with (X:=Y) in H2; simpl; trivial.
   apply set_union_intro2; trivial. apply set_add_intro1; trivial.
     
  apply set_inter_nil. intro Y. intro H4.
  apply set_inter_elim in H4. destruct H4.
  rewrite H3 in H4. rewrite H3 in H5.
  apply In_dom_eq_dom_rec in H4.
  apply dom_comp_add1 in H4.
  destruct H4. rewrite H4 in H5.
  apply im_vars_comp_add2 in H5; trivial.
  autorewrite with perm in H5. contradiction.
  apply im_vars_comp_add1 in H5; trivial.
  apply set_union_elim in H5. destruct H5.
  apply set_inter_nil with (a:=Y) in H1.
  apply H1. apply set_inter_intro; trivial.
  apply In_dom_eq_dom_rec; trivial.
  autorewrite with perm in H5.

  apply set_inter_nil with (a:=Y) in Q'.
  apply Q'. apply set_inter_intro; trivial.
  apply In_dom_eq_dom_rec; trivial.
  
Qed.
   
Lemma equ_valid_preservation : forall T T',
                               valid_triple T -> equ_sys T T' -> valid_triple T' .   
Proof.
  intros. unfold valid_triple in *|-*. split~.
  Focus 2. apply equ_valid_preservation_aux with (T:=T); trivial.
   destruct H. apply set_inter_nil. intros Y H2.
   apply set_inter_elim in H2. destruct H2.
  generalize H; intro H'.
  apply set_inter_nil with (a:=Y) in H;
  apply H; destruct H0; simpl in *|-*;
      repeat apply Problem_vars_remove in H3; simpl; trivial.
       
  apply set_inter_intro; trivial.
  
  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3;
  apply set_union_elim in H3; destruct H3;
  try apply Problem_vars_add in H3;
  try apply set_union_elim in H3; try destruct H3; simpl in H3; trivial;
  apply set_union_elim in H3; destruct H3;
  apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.
  apply set_union_intro1; apply set_union_intro1; trivial.
  apply set_union_intro2; apply set_union_intro1; trivial.
  apply set_union_intro1; apply set_union_intro2; trivial.
  apply set_union_intro2; apply set_union_intro2; trivial.

  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3; trivial.
  apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.
  
  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3; trivial. 
  simpl in H3. apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  simpl in H3. apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.
  
  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3; trivial. 
  simpl in H3. apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.
  simpl in H3. apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.

  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3; trivial.
  apply Problem_vars_set_In
  with (X:=Y) in H0; simpl; trivial.

  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3;
  apply set_union_elim in H3; destruct H3;
  try apply Problem_vars_add in H3;
  try apply set_union_elim in H3; try destruct H3; simpl in H3; trivial;
  try apply set_union_elim in H3; try destruct H3;
  apply Problem_vars_set_In
  with (X:=Y) in H4; simpl; trivial.
  apply set_union_intro1; trivial.
  rewrite perm_term_vars in H3.
  apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.
  
  apply Problem_vars_union in H3.
  apply set_union_elim in H3. destruct H3.
  rewrite H5 in H2. apply In_dom_eq_dom_rec in H2.
  apply dom_comp_add1 in H2. destruct H2.
  rewrite H2 in H3. apply In_im_subst_term_Problem in H3.
  autorewrite with perm in H3. contradiction.
  apply In_im_subst_term_Problem' in H3. 
  apply set_union_elim in H3. destruct H3.
  repeat apply Problem_vars_remove in H3.
  apply set_inter_intro; trivial.
  apply In_dom_eq_dom_rec; trivial.
  autorewrite with perm in H3.
  destruct H4; apply Problem_vars_set_In
  with (X:=Y) in H4; simpl; trivial.                          
  apply set_inter_intro; trivial.
  apply In_dom_eq_dom_rec; trivial.
  apply set_union_intro2; trivial.
  apply set_inter_intro; trivial.
  apply In_dom_eq_dom_rec; trivial.  
  apply set_add_intro1; trivial.
  apply subs_fresh_vars_im in H3.
  assert (Q:  set_inter Var_eqdec (dom_rec S') (im_vars S') = []).
   replace S' with (snd (fst (C,S',((P\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))\cup(C/?S')))).
   apply equ_valid_preservation_aux with (T := (C,S,P)).
   unfold valid_triple. simpl. split~.
   apply equ_sys_inst; trivial.
   simpl; trivial.
  apply set_inter_nil with (a:=Y) in Q.   
  simpl. false. apply Q. apply set_inter_intro; trivial.

  apply set_inter_intro; trivial.
  apply Problem_vars_add in H3.
  apply set_union_elim in H3. destruct H3; trivial.
  apply Problem_vars_set_In
  with (X:=Y) in H5; simpl; trivial.
 
Qed.


Lemma unif_step_valid_preserv : forall T T', valid_triple T -> unif_step T T' -> valid_triple T'.
Proof.
  intros. destruct H0. 
  apply equ_valid_preservation with (T:=T); trivial.
  apply fresh_valid_preservation with (T:=T); trivial. 
Qed.


Lemma unif_path_valid_preserv : forall T T', valid_triple T -> unif_path T T' -> valid_triple T'.
Proof.
  intros. destruct H0. induction H0; trivial.
  apply unif_step_valid_preserv with (T := s); trivial.
  apply IHtr_clos; trivial.
  apply unif_step_valid_preserv with (T := s); trivial.
Qed.


 