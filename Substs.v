(**
%\begin{verbatim}
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Substs.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation

 Description : This file contains all the definitions and lemmas regarding
               substitutions of variables by terms.
 
 Last Modified On: November 10, 2017.
 ============================================================================
\end{verbatim}%
*)

Require Export Problems.
Require Import Max GenericMinMax.

(** %\section{Definitions}% *)

(** look_up searches a variable in the domain of a substitution and 
 replaces this variable by the term in its correspondent image *) 

Fixpoint look_up (X : Var) (S : Subst) {struct S}: term :=
match S with
 | []         => []|.X
 | (Y,t)::S0  => if Y ==v X then t else (look_up X S0)
end.

(** subs extends the application of look_up of any term of the grammar *) 

Fixpoint subs (t: term) (S : Subst) {struct t} : term :=
 match  t with 
      | <<>>       => <<>>
      | % a        => % a  
      | [a]^t1     => [a]^(subs t1 S)
      | <|t1,t2|>  => <|(subs t1 S),(subs t2 S)|>
      | Fc E n t1    => Fc E n (subs t1 S)
      | p|.X        => p @ (look_up X S)
 end.
Notation "t |^ S" := (subs t S) (at level 67).


Definition In_dom (X : Var) (S : Subst) :=  ([]|.X)|^S <> []|.X . 
Notation "X € S" := (In_dom X S) (at level 67).

Lemma In_dom_dec : forall X S, {X € S} + {~ X € S}. 
Proof. 
 intros. case (term_eqdec (([]|.X)|^S) ([]|.X)); intros; unfold In_dom.
 right~. left~. 
Qed.


(** alist_rec allows the construction of a fuction of composition of substitutions *)

Fixpoint alist_rec (S1 S2: Subst) 
                   (F: Var -> term -> Subst -> Subst -> Subst) : Subst :=
 match S1 with 
    | []          =>  S2
    | (X,t)::S0  =>  F X t S2 (alist_rec S0 S2 F)
 end.

Definition F_rec (S1: Subst) (X:Var) (t:term) (S2 S3: Subst) := (X,t|^S1)::S3.


(** Subst_comp operates the substitution composition *)

Definition Subst_comp (S1 S2: Subst) := alist_rec S1 S2 (F_rec S2). 
Notation "S1 © S2" := (Subst_comp S1 S2) (at level 67).

(** subs_fresh_constraints applies a substitution to a freshness context *)

Fixpoint subs_fresh_constraints (C : Context) (S : Subst) : Problem :=
  match C with
    | [] => []
    | (a,X)::C0 => if (In_dom_dec X S) then
                      set_add Constraint_eqdec (a#?(([]|.X)|^S))
                      (subs_fresh_constraints C0 S)
                    else
                      (subs_fresh_constraints C0 S)
  end.                                           

Notation "C /? S" := (subs_fresh_constraints C S) (at level 67).

(** subs_Constraint applies a subtitution to a atomic problem *)

Definition subs_Constraint (u : Constraint) (S : Subst) : Constraint :=
  match u with
    | a#?t => a#?(t|^S)
    | s~?t => s|^S~?(t|^S)
  end.

(** subs_Problem applies a subtitution to a generic problem *)

Fixpoint subs_Problem (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (a#?t)::P0 => (a#?(t|^S))::(subs_Problem P0 S)
    | (s~?t)::P0 => ((s|^S)~?(t|^S))::(subs_Problem P0 S)
  end.

Notation "P |^^ S" := (subs_Problem P S) (at level 67).
 
(** fresh_env is a property over two freshness contexts and a substitution *)

Definition fresh_env (C C' : Context) (S : Subst) :=
  forall a X, set_In (a, X) C -> C' |- a # (([]|.X)|^S) .

(** subs_equiv is a equivalence property between two substitutions under a freshness context  *)

Definition subs_equiv (C: Context) (E : Context -> term -> term -> Prop) (S S' : Subst) :=
forall X, (X € S) \/ (X € S') -> E C (([]|.X)|^S) (([]|.X)|^S').

(** subst_dom_vars extracts the variables that contains the substitution domain *)

Fixpoint subst_dom_vars (S : Subst) : set Var :=
  match S with
    | [] => []   
    | (X,t)::S0 => set_add Var_eqdec X (subst_dom_vars S0)
  end.  

(** dom_rec_aux is a auxiliar function to build the correct domain of a substitution *)

Fixpoint dom_rec_aux (S : Subst) (St : set Var) : set Var :=
  match St with
    | [] => []
    | X::St0 => if (term_eqdec (([]|.X)|^S) ([]|.X)) then
                   (dom_rec_aux S St0) else
                   (set_add Var_eqdec X (dom_rec_aux S St0))
  end.                  

(** dom_rec is the recursive function that gives the domain of a substitution *)

Definition dom_rec (S : Subst) := dom_rec_aux S (subst_dom_vars S).

(** im_rec_aux is a auxiliar function to build the correct image of a substitution *)

Fixpoint im_rec_aux (S : Subst) (St : set Var) : set term :=
  match St with
    | [] => []  
    | X::St0 => ([]|.X|^S)::(im_rec_aux S St0) 
  end.

(** im_rec is the recursive function that gives the image of a substitution *)

Definition im_rec (S : Subst) := im_rec_aux S (dom_rec S).

(** terms_set_vars gives the set of variables that occur in a set of terms *)

Fixpoint terms_set_vars (T: set term) : set Var :=
  match T with
    | [] => []
    | s::T0 => set_union Var_eqdec (term_vars s) (terms_set_vars T0)        
  end.

(** im_vars gives the set of variables that occur in the image of a substiturion *)

Definition im_vars (S : Subst) := terms_set_vars (im_rec S). 

(** set_subst applies a substitution in a set of terms *)

Fixpoint set_subst (St : set term) (S : Subst) : set term :=
  match St with
    | [] => []  
    | s::St0 => set_add term_eqdec (s|^S) (set_subst St0 S) 
  end.

(** left_terms gives the set of terms that occurs on the lhs of the equational 
constraints of a problem *)

Fixpoint left_terms (P : Problem) : set term :=
  match P with
    | [] => []
    | (a#?t)::P0 => left_terms P0
    | (s~?t)::P0 => set_add term_eqdec s (left_terms P0)                         
  end.

(** right_terms gives the set of terms that occurs on the rhs of the equational 
constraints of a problem *)

Fixpoint right_terms (P : Problem) : set term :=
  match P with
    | [] => []
    | (a#?t)::P0 => right_terms P0
    | (s~?t)::P0 => set_add term_eqdec t (right_terms P0)                         
  end.

(** left_vars gives the variables of the left_terms *)

Definition left_vars (P : Problem) := terms_set_vars (left_terms P).

(** right_vars gives the variables of the right_terms *)

Definition right_vars (P : Problem) := terms_set_vars (right_terms P).

(** Context_vars gives the variables of a freshness context *)

Fixpoint Context_vars (C : Context) : set Var :=
  match C with
    | [] => []
    | (a,X)::C0 => X::Context_vars C0
  end.

(** gt_idx gives greatest variable index occuring in a set of variables *)

Fixpoint gt_idx (St : set Var) : nat :=
  match St with
    | []  => 0
    | (var n)::St0 => max n (gt_idx St0)                  
  end.

(** ren_subst is a renaming of variables that chooses all "new" variables 
  with index greather then n *)

Fixpoint ren_subst (St : set Var) (n : nat) : Subst :=
  match St with
    | [] => []
    | X::St0 => (X,[]|.(var (S n)))::(ren_subst St0 (S n)) 
  end.                                 

(** left_subst applies a substitution to the lrs of equational constraints of a given problem *)

Fixpoint left_subst (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (a#?t)::P0 => left_subst P0 S
    | (s~?t)::P0 => (s|^S~?t)::(left_subst P0 S)
  end.

Notation "P ||^ S" := (left_subst P S) (at level 67).


(** left_ren renames all the variables in the intersection of left_vars and right_vars 
 to variables with indexes greather then n *)
                        
Definition left_ren (P : Problem) (n : nat) :=
  P||^(ren_subst (set_inter Var_eqdec (left_vars P) (right_vars P)) n). 

(** Triple_vars is set of variables that occurs in a given Triple *)

Definition Triple_vars (T : Triple) :=
  set_union Var_eqdec (Context_vars (fst (fst T)))
   (set_union Var_eqdec (dom_rec (snd (fst T)))
     (set_union Var_eqdec (im_vars (snd (fst T))) (Problem_vars (snd T)))) .         


(** gt_idx_Triple is the greatest index of a variable occuring in a Triple *)

Definition gt_idx_Triple (T : Triple) := gt_idx (Triple_vars T).
  
                           

(** %\section{Lemmas}% *)

(** %\subsection{Basic results about substitutions}% *)

(** Substitutions and permutations commutes. *) 

Lemma subst_perm_comm : forall S pi t, (pi @ t)|^S = pi @ (t|^S).
Proof.
  intros; induction t;
  autorewrite with perm; simpl subs;
  autorewrite with perm; auto.
  rewrite IHt; trivial.
  rewrite IHt1; rewrite IHt2; trivial.
  rewrite IHt; trivial.
  rewrite perm_comp; trivial.
Qed.


(** The empty substitution has no action over a term. *)

Lemma subst_id : forall t, t|^([]) = t.
Proof. 
  intros. induction t; auto.
  simpl. rewrite IHt; trivial.
  simpl. rewrite IHt1; rewrite IHt2; trivial.
  simpl. rewrite IHt; trivial.
  destruct p; simpl; trivial.
Qed.


(** The singleton substitution [(X,t)] applied over pi|.X
 will result in pi @ t. *)

Lemma subst_var_eq : forall X pi t, (pi|.X)|^([(X,t)]) = pi @ t.
Proof.
  intros. simpl. case (X ==v X); intro H; trivial. false. 
Qed. 


(** A suspension will not be 
    affect the action of a substitution if and only if 
    it is not in its domain. *)

Lemma not_In_dom : forall X S pi, ~ X € S -> (pi|.X)|^S = pi|.X.
Proof.
  intros. replace (pi|.X) with (pi @ ([]|.X)).
  rewrite subst_perm_comm. rewrite <- perm_term_invariance.
  unfold In_dom. case (term_eqdec ((([])|.X) |^ S) (([])|.X));
    intro H0; try contradiction; trivial.
  autorewrite with perm. simpl; trivial.
Qed.


Lemma not_In_dom_iff : forall X S pi, ~ X € S <-> (pi|.X)|^S = pi|.X.
Proof.
  intros. split~; intro. apply not_In_dom; trivial.
  intro H0. unfold In_dom in H0. apply H0.
  apply perm_term_invariance with (pi:=pi).
  rewrite <- subst_perm_comm.
  autorewrite with perm. simpl; trivial.
Qed.


(** A recursive definition for the domain of a substitution. *)

Lemma dom_rec_aux_to_In_dom : forall X S St, set_In X (dom_rec_aux S St) -> X € S.
Proof.
  intros. unfold In_dom. simpl. autorewrite with perm.
  induction St; simpl in H; try contradiction.
  gen H. autorewrite with perm.
  case (term_eqdec (look_up a S) (([])|.a)); intros H0 H.
  apply IHSt; trivial. apply set_add_elim in H.
  destruct H. rewrite H; trivial. apply IHSt; trivial.
Qed.  

Lemma In_dom_to_dom_rec_aux : forall X S St,                             
                                X € S -> set_In X St -> set_In X (dom_rec_aux S St).
Proof.
  intros. unfold In_dom in H.
  simpl in H. autorewrite with perm in H.
  induction St; simpl in H0|-*; try contradiction.
  autorewrite with perm. case (term_eqdec (look_up a S) (([])|.a)); intro H1.
  destruct H0. rewrite H0 in H1. contradiction.
  apply IHSt; trivial. destruct H0.
  rewrite H0. apply set_add_intro2; trivial.
  apply set_add_intro1. apply IHSt; trivial.
Qed.

Lemma In_dom_to_subst_dom_vars : forall X S,
                                 X € S -> set_In X (subst_dom_vars S).   
Proof.
  intros. unfold In_dom in H.
  simpl in H. autorewrite with perm in H.
  induction S; simpl in *|-*. apply H; trivial.
  destruct a. gen H. case (v ==v X); intros H0 H.
  rewrite H0. apply set_add_intro2; trivial.
  apply set_add_intro1. apply IHS; trivial.
Qed.

Lemma In_dom_eq_dom_rec : forall X S, X € S <-> set_In X (dom_rec S).
Proof.
  intros. split~; intro H.
  apply In_dom_to_dom_rec_aux; trivial.
  apply In_dom_to_subst_dom_vars; trivial.
  apply dom_rec_aux_to_In_dom in H; trivial.
Qed.


(** If the domain of a substitution is empty than it is 
    the identity. *)

Lemma dom_rec_nil : forall S t, dom_rec S = [] -> t|^S = t.
Proof.
  intros. induction t; simpl; trivial.
  rewrite IHt; trivial.
  rewrite IHt1. rewrite IHt2; trivial.
  rewrite IHt; trivial.
  replace (p @ look_up v S) with ((p|.v)|^S); trivial.
  apply not_In_dom. intro H0.
  apply In_dom_eq_dom_rec in H0.
  rewrite H in H0. simpl in H0; trivial.
Qed.


(** For a "singleton" substitution ([(X, t)]), 
    if X is not in its domain, then it has 
    a empty domain. *)

Lemma singleton_dom_rec_nil : forall X t, ~ X € ([(X, t)]) -> dom_rec ([(X, t)]) = [] .
Proof.
  intros. apply not_In_dom with (pi := []) in H.
  simpl in H. unfold dom_rec. simpl. gen H.
  autorewrite with perm. case (X ==v X); intros.
  case (term_eqdec t (([])|.X)); intro H1; trivial. 
  contradiction. false.
Qed.


(** 
The intersection between the variables of a term and the 
domain of a substitution is empty if, and only if, this substitution 
has no action over the term.
*)

Lemma inter_dom_term_vars : forall t S,
      set_inter Var_eqdec (term_vars t) (dom_rec S) = [] -> t|^S = t.
Proof.
  intros. induction t; simpl; trivial.
  simpl in H. rewrite IHt; trivial.
  simpl in H. rewrite IHt1. rewrite IHt2; trivial.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_nil with (a:=a) in H.
  apply H. apply set_inter_elim in H0. destruct H0.
  apply set_inter_intro; trivial. apply set_union_intro2; trivial.
  apply set_inter_nil; intros. intro H0.
  apply set_inter_nil with (a:=a) in H.
  apply H. apply set_inter_elim in H0. destruct H0.
  apply set_inter_intro; trivial. apply set_union_intro1; trivial.
  simpl in H. rewrite IHt; trivial.
  replace (p @ look_up v S) with ((p|.v)|^S).
  apply not_In_dom. intro H0.
  apply set_inter_nil with (a:=v) in H.
  apply H. apply set_inter_intro.
  simpl. left~. apply In_dom_eq_dom_rec; trivial.
  simpl; trivial.
Qed.  


Lemma inter_dom_term_vars_iff : forall t S,
      set_inter Var_eqdec (term_vars t) (dom_rec S) = [] <-> t|^S = t.
Proof.
  intros. split~; intro. apply inter_dom_term_vars; trivial.
  apply set_inter_nil; intros X H0.
  apply set_inter_elim in H0. destruct H0.
  induction t; simpl in *|-; trivial.
  inverts H. apply IHt in H3; trivial.
  apply set_union_elim in H0. inverts H. destruct H0.
  apply IHt1 in H3; trivial. apply IHt2 in H4; trivial.
  inverts H. apply IHt in H3; trivial.  
  destruct H0; try contradiction. rewrite <- H0 in H1.
  apply In_dom_eq_dom_rec in H1. 
  replace (p|.v) with (p @ ([]|.v)) in H; autorewrite with perm; simpl; trivial.
  apply perm_term_invariance in H.
  apply H1. simpl. autorewrite with perm. trivial.
Qed.  
  

(** A corollary of the previous result *)

Corollary not_occurs : forall X t1 t2, (~ set_In X (term_vars t1)) -> t1|^([(X,t2)]) = t1.
Proof.
  intros. apply inter_dom_term_vars.
  apply set_inter_nil; intros Y H0.
  apply set_inter_elim in H0.
  destruct H0. unfold dom_rec in H1.
  simpl in H1. autorewrite with perm in H1.
  gen H1. case (X ==v X); intro H1.
  case (term_eqdec t2 (([])|.X)); intros H2 H3;
  simpl in H3; trivial. destruct H3; trivial.
  rewrite H3 in H. contradiction.
  false.
Qed.
 


(** A recursive definition for the image of a substitution. *)

Lemma im_rec_aux_std : forall t S St,
       set_In t (im_rec_aux S St) ->
       exists X, set_In X St /\ t = ([]|.X)|^S.                   
Proof.
  intros. simpl. induction St; simpl in H.
  contradiction. destruct H.
  exists a. rewrite H. simpl. split~.
  apply IHSt in H. case H; clear H; intros X H.
  destruct H. exists X. simpl. split~.
Qed.

Lemma In_dom_to_im_rec : forall X S, X € S -> set_In (([]|.X)|^S) (im_rec S).
Proof.
  intros. generalize H. intro H'.
  unfold In_dom in H.
  apply In_dom_eq_dom_rec in H'.
  unfold im_rec. induction (dom_rec S).
  simpl in H'. contradiction.
  simpl in *|-*. autorewrite with perm in *|-*.
  destruct H'. rewrite H0. left~. right~.
Qed.

Lemma im_rec_to_In_dom : forall t S,
                                set_In t (im_rec S) <-> exists X, X € S /\ t = ([]|.X)|^S.
Proof.
  intros. unfold im_rec.
  setoid_rewrite In_dom_eq_dom_rec.
  split~; intro. apply im_rec_aux_std; trivial.
  case H; clear H; intros X H. destruct H.
  rewrite H0. apply In_dom_to_im_rec.
  apply In_dom_eq_dom_rec; trivial.
Qed.


(** Some results about composition of substitutions *)

Lemma subst_comp_id_left : forall S, (([]) © S) = S.
Proof.
  intros. unfold Subst_comp. simpl; trivial.
Qed.

Lemma subst_comp_id_right : forall S, (S © ([])) = S.
Proof.
  intros. unfold Subst_comp.
  induction S; simpl; trivial.
  destruct a. rewrite IHS.
  unfold F_rec. rewrite subst_id; trivial.
Qed.

Lemma look_up_comp_expand : forall X S1 S2, look_up X (S1 © S2) = (look_up X S1)|^S2 . 
Proof.
  intros. induction S1; simpl; autorewrite with perm.
  rewrite subst_comp_id_left; trivial.
  destruct a. simpl. case (v ==v X); intro H; trivial.
Qed.  
  
Lemma subst_comp_expand : forall t S1 S2, t|^(S1 © S2) = (t|^S1)|^S2.
Proof.
 intros. induction t; simpl; trivial.
 rewrite IHt; trivial.
 rewrite IHt1; rewrite IHt2; trivial.
 rewrite IHt; trivial. 
 rewrite subst_perm_comm.
 fequals. apply look_up_comp_expand.
Qed.
  
Lemma subst_comp_assoc: forall S1 S2 S3 t, t|^(S1 © (S2 © S3)) = t|^((S1 © S2) © S3).
Proof.
  intros. rewrite 4 subst_comp_expand; trivial.
Qed.

Lemma fresh_subst: forall C1 C2 S a t,
C1 |- a # t ->  fresh_env C1 C2 S -> C2 |- a # (t|^S).
Proof.
  intros. induction H; simpl; auto.
  apply H0 in H. simpl in H.
  autorewrite with perm in H.
  apply fresh_lemma_2 in H.
  rewrite rev_involutive in H; trivial.
Qed.


(** Some results about "C-equivalence" between substitutions. *)

Notation "C |- S ~:c S'" := (subs_equiv C (equiv ([2])) S S') (at level 67).

Lemma c_equiv_subst: forall C1 C2 S t1 t2, 
C1|- t1 ~c t2 -> fresh_env C1 C2 S -> C2 |- (t1|^S) ~c (t2|^S).
Proof.
  intros. induction H; simpl; auto.
  apply IHequiv in H0. clear IHequiv.
  apply c_equiv_Fc; trivial.
   rewrite subst_perm_comm in IHequiv.  
  apply equiv_Ab_2; trivial.
  apply IHequiv; trivial.
  apply fresh_subst with (C1 := C); trivial.
  apply c_equiv_pi; intros.
  replace (look_up X S) with (([]|.X)|^S).
  apply fresh_subst with (C1 := C); trivial.
  apply fresh_Su. simpl. apply H; trivial.
  simpl. autorewrite with perm; trivial.
  simpl in H. omega.
  simpl in H. omega. 
Qed.

Lemma c_equiv_unif: forall C X S pi t,
C|- (pi|.X)|^S ~c (t|^S) -> C |- ([(X,(!pi) @ t)] © S) ~:c S.
Proof.
 intros. simpl in H. unfold subs_equiv. intros Y H'. simpl.
 autorewrite with perm. case (X ==v Y); intro H''.
 rewrite subst_perm_comm. apply c_equiv_pi_inv_side. 
 rewrite rev_involutive. rewrite <- H''.
 apply c_equiv_sym; trivial.
 apply c_equiv_refl. 
Qed.

Lemma c_equiv_look_up : forall C S1 S2 X,  
C |- S1 ~:c S2 -> C |- look_up X S1 ~c look_up X S2 .
Proof.
  intros. unfolds in H. simpl in H.
  setoid_rewrite perm_id in H.
  case (In_dom_dec X S1); intro H0.
  apply H. left~.
  case (In_dom_dec X S2); intro H1.
  apply H. right~.
  replace (look_up X S1) with ([]|.X).
  replace (look_up X S2) with ([]|.X).
  apply c_equiv_refl.
  replace (look_up X S2) with (([]|.X)|^S2).
  symmetry. apply not_In_dom; trivial.
  simpl; autorewrite with perm; trivial.
  replace (look_up X S1) with (([]|.X)|^S1).
  symmetry. apply not_In_dom; trivial.  
  simpl; autorewrite with perm; trivial.
Qed.
  
Lemma subst_c_equiv: forall C S1 S2 t,  
C |- S1 ~:c S2 -> C|- t|^S1 ~c (t|^S2) .
Proof.
  intros. induction t; simpl; auto.
  apply c_equiv_Fc; trivial.
  apply c_equiv_equivariance.
  apply c_equiv_look_up; trivial.  
Qed.

Lemma c_equiv_unif_2: forall C S1 S2 t1 t2, C|- S1 ~:c S2 ->  
              C|- t1|^S1 ~c (t2|^S1) -> C |- t1|^S2 ~c (t2|^S2).
Proof.
  intros.
  apply c_equiv_trans with (t2:=t1|^S1).
  apply c_equiv_sym. apply subst_c_equiv; trivial.
  apply c_equiv_trans with (t2:=t2|^S1); trivial.
  apply subst_c_equiv; trivial.
Qed.

Lemma c_equiv_unif_fresh: forall C S1 S2 t a, C|- S1 ~:c S2 ->
               C|- a # (t|^S1) -> C|- a # (t|^S2) .
Proof.
  intros. apply subst_c_equiv with (t:=t) in H.
  apply c_equiv_fresh with (a:=a) in H; trivial.
Qed.

Lemma subst_cancel_left: forall C S1 S2 S,
   C|- S1 ~:c S2 -> C|- (S © S1) ~:c (S © S2) .
Proof.
  intros. unfold subs_equiv. intros.
  rewrite 2 subst_comp_expand.
  apply subst_c_equiv; trivial.  
Qed.

Lemma subst_cancel_right: forall C1 C2 S1 S2 S,
   fresh_env C1 C2 S ->                         
   C1 |- S1 ~:c S2 -> C2|- (S1 © S) ~:c (S2 © S).
Proof.
  intros. unfold subs_equiv. intros.
  rewrite 2 subst_comp_expand.
  apply c_equiv_subst with (C1:=C1); trivial.
  apply subst_c_equiv; trivial.
Qed.

Lemma subst_assoc : forall C S1 S2 S3 S4,
                      C |- (S1 © S2) © S3 ~:c S4 <->
                      C |- S1 © (S2 © S3) ~:c S4.
Proof.
  intros. unfold subs_equiv; split; intros.
  rewrite subst_comp_assoc. apply H.
  destruct H0. left~. unfold In_dom in H0|-*.
  rewrite <- subst_comp_assoc; trivial. right~.
  rewrite <- subst_comp_assoc.
  apply H. destruct H0. left~. unfold In_dom in H0|-*.
  rewrite subst_comp_assoc; trivial. right~.
Qed.
  
Lemma subst_refl : forall C S, C|- S ~:c S.
Proof.
  intros. unfold subs_equiv; intros.
  apply c_equiv_refl.
Qed.

Lemma subst_sym : forall C S1 S2, C|- S1 ~:c S2 -> C|- S2 ~:c S1.
Proof.
  intros. unfold subs_equiv in *|-*.
  intros. apply c_equiv_sym. apply H.
  destruct H0. right~. left~.
Qed.
  
Lemma subst_trans: forall C S1 S2 S3,  
 C|- S1 ~:c S2 -> C|- S2 ~:c S3 -> C|- S1 ~:c S3 .
Proof.
  intros.
  unfold subs_equiv in *|-*. simpl in *|-*. intros.
  autorewrite with perm.
  setoid_rewrite perm_id in H.
  setoid_rewrite perm_id in H0.
  apply c_equiv_trans with (t2:=look_up X S2); destruct H1.
  apply H. left~.  
  case (In_dom_dec X S1); intro H2. apply H. left~.
  case (In_dom_dec X S2); intro H3. apply H. right~.  
  replace (look_up X S1) with ([]|.X).
  replace (look_up X S2) with ([]|.X).
  apply c_equiv_refl.
  replace (look_up X S2) with (([]|.X)|^S2).
  symmetry. apply not_In_dom; trivial.
  simpl; autorewrite with perm; trivial.
  replace (look_up X S1) with (([]|.X)|^S1).
  symmetry. apply not_In_dom; trivial.  
  simpl; autorewrite with perm; trivial.
  case (In_dom_dec X S2); intro H2. apply H0. left~.
  case (In_dom_dec X S3); intro H3. apply H0. right~.  
  replace (look_up X S2) with ([]|.X).
  replace (look_up X S3) with ([]|.X).
  apply c_equiv_refl.
  replace (look_up X S3) with (([]|.X)|^S3).
  symmetry. apply not_In_dom; trivial.
  simpl; autorewrite with perm; trivial.
  replace (look_up X S2) with (([]|.X)|^S2).
  symmetry. apply not_In_dom; trivial.  
  simpl; autorewrite with perm; trivial.
  apply H0. right~.
Qed.


(** %\subsection{Substitutions and sets of variables}% *)

(** Results about the set of variables of a term. *)

Lemma set_In_terms_set_vars : forall St X,
       set_In X (terms_set_vars St) <->
       exists t, set_In t St /\ set_In X (term_vars t).
Proof.
  intros. induction St; simpl.
  split~; intro. contradiction.
  destruct H. destruct H. contradiction.
  split~; intro. apply set_union_elim in H. destruct H.
  exists a. split~. 
  apply IHSt in H. case H; clear H; intros t H.
  exists t. destruct H. split~.
  case H; clear H; intros t H. destruct H. destruct H.
  apply set_union_intro1. rewrite H; trivial.
  apply set_union_intro2. apply IHSt.
  exists t. split~.
Qed.
  

Lemma terms_set_vars_add : forall St t X,
                             set_In X (terms_set_vars (set_add term_eqdec t St)) <->
                             set_In X (set_union Var_eqdec (term_vars t) (terms_set_vars St)).
Proof.
  intros. split~; intro.
  apply set_In_terms_set_vars in H.
  case H; clear H; intros s  H.
  destruct H. apply set_add_elim in H. destruct H.
  rewrite H in H0. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_In_terms_set_vars.
  exists s. split~.
  apply set_In_terms_set_vars.
  apply set_union_elim in H. destruct H.
  exists t. split~. apply set_add_intro2; trivial.
  apply set_In_terms_set_vars in H.
  case H; clear H; intros s H. destruct H.
  exists s. split~. apply set_add_intro1; trivial.
Qed.  

Lemma terms_set_vars_subset : forall St0 St1,
                          (forall s, set_In s St0 -> set_In s St1) ->
                          (forall X, set_In X (terms_set_vars St0) -> set_In X (terms_set_vars St1)). 
Proof.
  intros. induction St0;
    simpl in *|-*; try contradiction.
  apply set_union_elim in H0. destruct H0. 
  assert (Q: set_In a St1). apply H. left~.
  clear H IHSt0 St0. induction St1;
    simpl in *|-*; try contradiction.
  destruct Q. rewrite H.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  apply IHSt1; trivial.
  apply IHSt0; intros; trivial.
  apply H. right~.
Qed.  

Lemma In_terms_vars_set : forall s X St, set_In s St ->
                                        set_In X (term_vars s) -> set_In X (terms_set_vars St).  
Proof.
  intros. induction St. simpl in H. contradiction.
  simpl in H|-*. destruct H.
  apply set_union_intro1. rewrite H; trivial.
  apply set_union_intro2. apply IHSt; trivial.
Qed.

(** A lemma about idempotent substitutions. *)

Lemma subst_idem : forall C S1 S2, set_inter Var_eqdec (dom_rec S1) (im_vars S1) = [] ->
                               C |- S1 © S1 © S2 ~:c (S1 © S2).
Proof.
  intros. unfold subs_equiv. intros.
  rewrite 3 subst_comp_expand.
  rewrite inter_dom_term_vars with (t:=(([])|.X)|^S1).
  apply c_equiv_refl.
  apply set_inter_nil. intros Y H1.
  apply set_inter_elim in H1. destruct H1.
  apply set_inter_nil with (a:=Y) in H.
  apply H. clear H. apply set_inter_intro; trivial.
  clear H0. case (In_dom_dec X S1); intro H3.
  apply In_dom_to_im_rec in H3.
  unfold im_vars. apply In_terms_vars_set with (s:=(([])|.X)|^S1); trivial.
  replace (([]|.X)|^S1) with ([]|.X) in H1.
  simpl in H1. destruct H1; try contradiction.
  apply In_dom_eq_dom_rec in H2. rewrite <- H in H2. contradiction.
  symmetry. apply not_In_dom; trivial.
Qed.


(** Results about the set of variables that occurs in the image of a substitution. *)

Lemma set_In_im_vars : forall S X,
      set_In X (im_vars S) <->
      exists t, set_In t (im_rec S) /\ set_In X (term_vars t).                   
Proof.
  intros. apply set_In_terms_set_vars.
Qed.

  
Lemma set_In_subst_term_im : forall X S t,
      X € S ->
      set_In X (term_vars (t|^S)) ->                           
      set_In X (im_vars S).
Proof.
 intros. induction t; simpl in *|-*; try contradiction.
 apply IHt; trivial.
 apply set_union_elim in H0. destruct H0.
 apply IHt1; trivial. apply IHt2; trivial.
 apply IHt; trivial. 
 replace (look_up v S) with (([]|.v)|^S) in H0;
  simpl; autorewrite with perm; trivial.
 rewrite perm_term_vars in H0.
 case (In_dom_dec v S); intro.
 apply In_terms_vars_set with (s:= ([]|.v)|^S); trivial.
 apply In_dom_to_im_rec; trivial.
 replace (([]|.v)|^S) with ([]|.v) in H0.  
 simpl in H0. destruct H0; try contradiction; trivial.
 rewrite H0 in n. contradiction.
 symmetry. apply not_In_dom; trivial.
Qed.


(** %\subsection{Substitutions applied over set of terms}% *)


Lemma set_subst_element : forall s St S,
      set_In s (set_subst St S) <-> exists t, s = t|^S /\ set_In t St.
Proof.
  intros. induction St; simpl. split~; intro.
  contradiction. destruct H. destruct H. trivial.
  split~; intros. 
  apply set_add_elim in H. destruct H.
  exists a. split~. 
  apply IHSt in H. case H; clear H; intros u H.
  exists u. destruct H. split~.
  case H; clear H; intros u H. destruct H. destruct H0.
  rewrite H0. apply set_add_intro2; trivial.
  apply set_add_intro1. apply IHSt. exists u. split~.  
Qed.  

Lemma set_subst_add : forall s t St S,
      set_In s (set_subst (set_add term_eqdec t St) S) <->
      set_In s (set_add term_eqdec (t|^S) (set_subst St S)). 
Proof.
  intros. split~; intro.
  apply set_subst_element in H. case H; clear H; intros u H.
  destruct H. apply set_add_elim in H0. destruct H0.
  rewrite H0 in H. apply set_add_intro2; trivial.
  apply set_add_intro1. apply set_subst_element.
  exists u. split~.
  apply set_subst_element. apply set_add_elim in H.
  destruct H. exists t. split~. apply set_add_intro2; trivial.
  apply set_subst_element in H. case H; clear H; intros u H.
  destruct H. exists u. split~. apply set_add_intro1; trivial.
Qed.
  

(** %\subsection{Technical results about domain, image and variable sets}% *)

Lemma dom_comp_add1 : forall S t X Y, Y € (S © [(X,t)]) -> (Y = X \/ Y € S).  
Proof.
  intros. case (Y ==v X); intro H0. left~.
  right~. unfold In_dom in *|-*.
  intro H1. apply H. clear H.
  rewrite subst_comp_expand. rewrite H1.
  rewrite not_occurs; trivial. simpl.
  intro. destruct H; contradiction.
Qed.

Lemma dom_comp_add2 : forall S t X, t <> []|.X -> ~ X € S -> X € (S © [(X,t)]).
Proof.
  intros. 
  apply not_In_dom with (pi:=[]) in H0. 
  unfold In_dom. simpl in *|-*.
  autorewrite with perm in *|-*.
  rewrite look_up_comp_expand.
  rewrite H0. simpl.
  autorewrite with perm.
  case (X ==v X); intro H1; trivial. false. 
Qed.

Lemma subst_eq_var : forall X Y s t, s <> []|.Y ->
                                     s|^([(X,t)]) = []|.Y ->
                                    (s = []|.X /\ t = []|.Y).  
Proof.
  intros. destruct s; simpl in H0.
  inverts H0. inverts H0. inverts H0. inverts H0. inverts H0.
  gen H0. case (X ==v v); intros. rewrite e.
  destruct t; autorewrite with perm in H0; inverts H0.
  rewrite H2. destruct p0; simpl in H2.
  rewrite H2. split~. inverts H2.
  autorewrite with perm in H0. simpl in H0.
  contradiction.
Qed. 

Lemma dom_comp_add3: forall S t X Y,  ~ set_In Y (term_vars t) -> Y € S -> Y € (S © [(X,t)]) .
Proof.
  intros. unfold In_dom in *|-*.
  rewrite subst_comp_expand. intro H1.
  apply subst_eq_var in H1; trivial.
  destruct H1. apply H. rewrite H2.
  simpl. left~.
Qed.  

Lemma dom_comp_add_gen: forall S t X Y,  t <> []|.X -> ~ X € S -> ~ set_In Y (term_vars t) -> 
                                        (Y € (S © [(X,t)]) <-> (Y = X \/ Y € S)).
Proof.
  intros. split~; intro.
  apply dom_comp_add1 in H2; trivial.
  destruct H2. rewrite H2 in *|-*.
  apply dom_comp_add2; trivial.
  apply dom_comp_add3; trivial.
Qed.

Lemma var_in_dom_rec_singleton : forall X Y t, set_In Y (dom_rec ([(X,t)])) -> Y = X.
Proof.
  intros X Y t. unfold dom_rec. simpl.
  autorewrite with perm. case (X ==v X).
  case (term_eqdec t (([])|.X)); intros.
  simpl in H. contradiction. simpl in H.
  destruct H; try contradiction.
  symmetry in H. trivial.
  intros. false.
Qed.  

Lemma set_In_subst_term : forall X S t,
      set_In X (term_vars (t|^S)) ->
     (set_In X (term_vars t) \/ set_In X (im_vars S)).
Proof.
  intros. induction t; simpl in *|-*; try contradiction.
  apply IHt; trivial. 
  apply set_union_elim in H. destruct H.
   apply IHt1 in H. destruct H.
    left~. apply set_union_intro1; trivial. right~.
   apply IHt2 in H. destruct H.
    left~. apply set_union_intro2; trivial. right~.
  apply IHt in H; trivial.
  replace (look_up v S) with (([]|.v)|^S) in H;
    simpl; autorewrite with perm; trivial.
  rewrite perm_term_vars in H.
  case (In_dom_dec v S); intro.
  right~. apply In_terms_vars_set with (s:= ([]|.v)|^S); trivial.
  apply In_dom_to_im_rec; trivial.
  left~. left~. replace (([]|.v)|^S) with ([]|.v) in H.  
  simpl in H. destruct H; try contradiction; trivial.
  symmetry. apply not_In_dom; trivial.
Qed.

Lemma set_In_subst_Problem : forall X S P,
      set_In X (Problem_vars (P|^^S)) ->
     (set_In X (Problem_vars P) \/ set_In X (im_vars S)).
Proof.
  intros. induction P; simpl in H.
  contradiction. destruct a; simpl in *|-*.
  apply set_union_elim in H.
  destruct H. apply set_In_subst_term in H. destruct H.
  left~. apply set_union_intro1; trivial. right~.
  apply IHP in H. destruct H.
  left~. apply set_union_intro2; trivial. right~.
  apply set_union_elim in H. destruct H.
  apply set_In_subst_term in H. destruct H.
  left~. apply set_union_intro1; trivial. right~.
  apply set_union_elim in H. destruct H.
  apply set_In_subst_term in H. destruct H.
  left~. apply set_union_intro2.
  apply set_union_intro1; trivial. right~.
  apply IHP in H. destruct H.
  left~. apply set_union_intro2.
  apply set_union_intro2; trivial. right~.
Qed.

Lemma set_In_set_subst : forall X S St,
      set_In X (terms_set_vars (set_subst St S)) ->
     (set_In X (terms_set_vars St) \/ set_In X (im_vars S)).
Proof.
  intros. apply set_In_terms_set_vars in H.
  case H; clear H; intros t H. destruct H.
  apply set_subst_element in H.
  case H; clear H; intros s H. destruct H.
  rewrite H in H0. clear H. apply set_In_subst_term in H0.
  destruct H0. left~. apply set_In_terms_set_vars.  
  exists s. split~. right~.
Qed.  

Lemma set_In_subst_set_im : forall X S St,
      X € S ->
      set_In X (terms_set_vars (set_subst St S)) ->                           
      set_In X (im_vars S).
Proof.
  intros. apply set_In_terms_set_vars in H0.
  case H0; clear H0; intros s H0. destruct H0.
  induction St; simpl in *|-*; try contradiction.
  apply set_add_elim in H0. destruct H0.
  rewrite H0 in H1. apply set_In_subst_term_im in H1; trivial.
  apply IHSt; trivial.
Qed.

  
Lemma In_im_subst_term : forall X s t,
                            set_In X (term_vars (s|^([(X,t)]))) -> set_In X (term_vars t).
Proof.
  intros. case (In_dom_dec X ([(X, t)])); intro H0.
  apply set_In_subst_term_im in H; trivial.
  apply set_In_im_vars in H.
  case H; clear H; intros u H.
  destruct H. apply im_rec_aux_std in H.
  case H; clear H; intros Y H. destruct H.
  simpl in H2. autorewrite with perm in H2.
  gen H2. case (X ==v Y); intros.
  rewrite H2 in H1; trivial.
  rewrite H2 in H1. simpl in H1. destruct H1; try contradiction.
  symmetry in H1. contradiction.
  rewrite dom_rec_nil in H.
  apply not_In_dom with (pi:=[]) in H0.
  simpl in H0. autorewrite with perm in H0.
  gen H0. case (X ==v X); intros.
  rewrite H0. simpl. left~. false.
  apply singleton_dom_rec_nil; trivial.
Qed.

Lemma In_im_subst_term' : forall X Y s t,   set_In Y (term_vars (s|^([(X,t)]))) ->
                                            set_In Y (set_union Var_eqdec (term_vars s) (term_vars t)).
Proof.
  intros. apply set_In_subst_term in H.
  destruct H. apply set_union_intro1; trivial.
  apply set_In_im_vars in H. case H; clear H; intros u H.
  destruct H. apply im_rec_aux_std in H.
  case H; clear H; intros Z H. destruct H.
  apply var_in_dom_rec_singleton in H.
  rewrite H in H1. clear H.
  rewrite subst_var_eq in H1.
  autorewrite with perm in H1.
  rewrite H1 in H0. clear H1.
  apply set_union_intro2; trivial.
Qed.

Lemma In_subst_terms_im_1 : forall X Y s t,
                            set_In Y (set_remove Var_eqdec X (term_vars s)) ->
                            set_In Y (term_vars (s|^([(X,t)])))  .
Proof.
  intros. 
  generalize H. intro H'.
  apply set_remove_1 in H.
  apply set_remove_2 in H'.  
  induction s; simpl in *|-*; trivial.
  apply IHs; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply IHs1; trivial.
  apply set_union_intro2. apply IHs2; trivial.
  apply IHs; trivial.
  case (X ==v v); intro H1.
  destruct H; try contradiction.
  rewrite H in H1. symmetry in H1. contradiction.
  rewrite perm_term_vars. simpl; trivial.
  apply NoDup_term_vars.
Qed.

Lemma In_subst_terms_im_2 : forall X Y s t, 
                            set_In X (term_vars s) ->
                            set_In Y (term_vars t) ->
                            set_In Y (term_vars (s|^([(X,t)]))).
Proof.
  intros. 
  induction s; simpl in *|-*; trivial.
  apply IHs; trivial.
  apply set_union_elim in H. destruct H.   
  apply set_union_intro1. apply IHs1; trivial.
  apply set_union_intro2. apply IHs2; trivial.
  apply IHs; trivial.
  destruct H; try contradiction. rewrite H; clear H.
  case (X ==v X); intro H. rewrite perm_term_vars; trivial. false.
Qed.

Lemma In_subst_terms_im : forall X Y s t,
      set_In X (term_vars s) ->
      set_In Y (set_union Var_eqdec (set_remove Var_eqdec X (term_vars s)) (term_vars t)) ->
      set_In Y (term_vars (s|^([(X,t)])))  .
Proof.
  intros. apply set_union_elim in H0. destruct H0.
  apply In_subst_terms_im_1; trivial.
  apply In_subst_terms_im_2; trivial.
Qed.
  

Lemma In_im_subst_terms_set : forall X St t, set_In X (terms_set_vars (set_subst St ([(X,t)]))) ->
                                             set_In X (term_vars t).
Proof.
  intros. apply set_In_terms_set_vars in H.
  case H; clear H; intros s H. destruct H.
  apply set_subst_element in H.
  case H; clear H; intros u H. destruct H.
  rewrite H in H0. clear H s.
  apply In_im_subst_term in H0. trivial.
Qed.

Lemma In_im_subst_terms_set' : forall X Y St t,
      set_In Y (terms_set_vars (set_subst St ([(X,t)]))) ->
      set_In Y (set_union Var_eqdec (terms_set_vars St) (term_vars t)).
Proof.
  intros. apply set_In_terms_set_vars in H.
  case H; clear H; intros s H. destruct H.
  apply set_subst_element in H.
  case H; clear H; intros u H. destruct H.
  rewrite H in H0. clear H s.  
  apply In_im_subst_term' in H0.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1.
  apply set_In_terms_set_vars.
  exists u. split~.
  apply set_union_intro2; trivial.
Qed.
  
  
Lemma In_im_comp_add : forall S X s t, ~ set_In X (dom_rec S) -> 
                       set_In s (im_rec (S © [(X,t)])) ->
                       set_In s (set_add term_eqdec t (set_subst (im_rec S) ([(X,t)]))).
Proof.
  intros. apply im_rec_to_In_dom in H0.
  case H0; clear H0; intros Y H0. destruct H0.
  apply dom_comp_add1 in H0. destruct H0.
  rewrite subst_comp_expand in H1. rewrite H0 in H1.
  replace (([]|.X)|^S) with ([]|.X) in H1.
  rewrite subst_var_eq in H1.
  autorewrite with perm in H1. apply set_add_intro2; trivial.
  symmetry. apply not_In_dom.
  rewrite In_dom_eq_dom_rec; trivial.
  rewrite In_dom_eq_dom_rec in H0.
  rewrite subst_comp_expand in H1. rewrite H1.
  clear H H1. unfold im_rec.
  apply set_add_intro1. induction (dom_rec S).
  simpl in H0. contradiction. simpl in H0.
  destruct H0. rewrite H. simpl.
  autorewrite with perm. apply set_add_intro2; trivial.
  apply IHs0 in H. clear IHs0.
  simpl. apply set_add_intro1; trivial.
Qed.  

Lemma im_vars_comp_add1 : forall S t X Y,
                             ~ set_In X (dom_rec S) ->
                             set_In Y (im_vars (S © [(X,t)])) ->
                             set_In Y (set_union Var_eqdec  (im_vars S) (term_vars t)).
Proof.
  intros. unfold im_vars in *|-.
  apply terms_set_vars_subset with
  (St1:= set_add term_eqdec t (set_subst (im_rec S) ([(X,t)]))) in H0.
  apply terms_set_vars_add in H0.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro2; trivial.
  apply In_im_subst_terms_set' in H0.
  unfold im_vars. trivial.
  intros. apply In_im_comp_add; trivial.
Qed.

Lemma im_vars_comp_add2 : forall S t X,
                             ~ set_In X (dom_rec S) ->
                             set_In X (im_vars (S © [(X,t)])) ->
                             set_In X (term_vars t).
Proof.
 intros. apply terms_set_vars_subset with
  (St1:= set_add term_eqdec t (set_subst (im_rec S) ([(X,t)]))) in H0.
 apply terms_set_vars_add in H0. apply set_union_elim in H0.
 destruct H0; trivial. apply In_im_subst_terms_set in H0; trivial.
 intros. apply In_im_comp_add; trivial.
Qed.


Lemma subs_fresh_vars_im : forall X C S,
                             set_In X (Problem_vars (C /? S)) ->
                             set_In X (im_vars S).
Proof.
  intros. unfold im_vars. induction C.
  simpl in H. contradiction. simpl in H.
  destruct a. gen H. case (In_dom_dec v S); intros H0 H.
  apply Problem_vars_add in H.
  apply set_union_elim in H. destruct H.
  apply IHC; trivial.
  autorewrite with perm in H. simpl in H.
  clear IHC C a. apply In_dom_eq_dom_rec in H0.
  unfold im_rec. induction (dom_rec S);
  simpl in *|-*; autorewrite with perm in *|-*; trivial.
  destruct H0. rewrite H0 in *|-*.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply IHs; trivial.
  apply IHC; trivial.
Qed.

Lemma subterms_subs : forall X S t,
                       set_In X (term_vars t) ->
                       exists pi, set_In ((pi|.X)|^S) (subterms (t |^ S)).
Proof.
  intros. induction t; simpl in H; try contradiction.
  apply IHt in H. case H; clear H; intros pi H.
  exists pi. simpl. apply set_add_intro1; trivial.
  apply set_union_elim in H. destruct H.
  apply IHt1 in H. case H; clear H; intros pi H.
  exists pi. simpl. apply set_add_intro1. apply set_union_intro1; trivial.
  apply IHt2 in H. case H; clear H; intros pi H.
  exists pi. simpl. apply set_add_intro1. apply set_union_intro2; trivial.  
  apply IHt in H. case H; clear H; intros pi H.
  exists pi. simpl. apply set_add_intro1; trivial.
  destruct H; try contradiction. rewrite H; clear H.
  exists p. apply In_subterms.
Qed.

Lemma psubterms_subs : forall X S t,   
                      (forall pi, t <> pi|.X) ->  
                       set_In X (term_vars t) ->
                       exists pi, set_In ((pi|.X)|^S) (psubterms (t |^ S)).
Proof.
  intros. generalize H0. intro H1.
  apply subterms_subs with (S:=S) in H1.
  case H1; clear H1; intros pi H1. exists pi.
  unfold psubterms. apply set_remove_3; trivial.
  clear H1. simpl; autorewrite with perm.
  destruct t; simpl in *|-*; try contradiction.
  intro H1.
  assert (Q : term_size (pi @look_up X S) = term_size ([a]^(t|^S))).   
   rewrite H1; trivial.
  apply subterms_subs with (S:=S) in H0. 
  case H0; clear H0; intros pi' H0. simpl in H0.
  apply subterms_term_size_leq in H0.
  rewrite perm_term_size in *|-. simpl in Q. omega.
  intro H1.
  assert (Q : term_size (pi @look_up X S) = term_size (<| t1 |^ S, t2 |^ S |>)).   
   rewrite H1; trivial.  
  apply set_union_elim in H0;
  destruct H0; apply subterms_subs with (S:=S) in H0;
  case H0; clear H0; intros pi' H0; simpl in H0;
  apply subterms_term_size_leq in H0;
  rewrite perm_term_size in *|-; simpl in Q; omega.  
  intro H1.
  assert (Q : term_size (pi @look_up X S) = term_size (Fc n n0 (t |^ S))).   
   rewrite H1; trivial.
  apply subterms_subs with (S:=S) in H0. 
  case H0; clear H0; intros pi' H0. simpl in H0.
  apply subterms_term_size_leq in H0.
  rewrite perm_term_size in *|-. simpl in Q. omega.
  inverts H0. false. apply (H p); trivial.
  contradiction.  
Qed.

Lemma equ_proj_subs_fresh : forall C S, equ_proj (C /? S) = [] .
Proof.
  intros. induction C; simpl; trivial.
  destruct a. case (In_dom_dec v S); intro H; trivial.
  case (in_dec Constraint_eqdec (a #? (([]) @ look_up v S)) (C /? S)); intro H0.
  rewrite set_add_In; trivial.
  rewrite set_add_not_In; trivial.
  rewrite equ_proj_append.
  rewrite IHC. simpl; trivial.
Qed.

Lemma equ_proj_subs : forall P S, equ_proj (P|^^S) = (equ_proj P)|^^S.
Proof.
  intros. induction P; simpl; trivial.
  destruct a; simpl; trivial. fequals.
Qed.

Lemma equ_subs_fresh : forall C S s t, ~ set_In (s~?t) (C /? S).
Proof.
  intros. induction C; simpl. intro; trivial.
  destruct a. case (In_dom_dec v S); intro H; trivial.
  intro H0. apply set_add_elim in H0.
  destruct H0; try contradiction. inverts H0.
Qed.

Lemma not_occurs_Problem : forall X P t, (~ set_In X (Problem_vars P)) -> P|^^([(X,t)]) = P.
Proof.
  intros. induction P; simpl in *|-*; trivial.
  destruct a. rewrite not_occurs. rewrite IHP; trivial.
  intro H0. apply H. apply set_union_intro2; trivial.
  intro H0. apply H. apply set_union_intro1; trivial.
  rewrite 2 not_occurs. rewrite IHP; trivial.
  intro H0. apply H. apply set_union_intro2.
  apply set_union_intro2; trivial.
  intro H0. apply H. apply set_union_intro2.
  apply set_union_intro1; trivial.
  intro H0. apply H. apply set_union_intro1; trivial.
Qed.
  
Lemma In_im_subst_term_Problem : forall X P t,
                                    set_In X (Problem_vars (P|^^([(X,t)]))) -> set_In X (term_vars t).
Proof.
  intros. induction P; simpl in H; try contradiction.
  destruct a; simpl in H. apply set_union_elim in H.
  destruct H; [apply In_im_subst_term with (s:=t0) | apply IHP]; trivial.
  apply set_union_elim in H. destruct H.
  apply In_im_subst_term with (s:=t0); trivial.
  apply set_union_elim in H.
  destruct H; [apply In_im_subst_term with (s:=t1) | apply IHP]; trivial.
Qed.

Lemma In_im_subst_term_Problem' : forall X Y P t,  set_In Y (Problem_vars (P|^^([(X,t)]))) ->
                                                   set_In Y (set_union Var_eqdec (Problem_vars P) (term_vars t)).
Proof.
  intros. induction P; simpl in H; try contradiction.
  destruct a; simpl in *|-*.
  apply set_union_elim in H. destruct H.
  apply In_im_subst_term' in H; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro1; trivial.
  apply set_union_intro2; trivial.
  apply IHP in H.  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.
  apply set_union_elim in H. destruct H.
  apply In_im_subst_term' in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro1; trivial.
  apply set_union_intro2; trivial.  
  apply set_union_elim in H. destruct H.
  apply In_im_subst_term' in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro2;
  apply set_union_intro1; trivial.
  apply set_union_intro2; trivial.
  apply IHP in H.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; apply set_union_intro2;
  apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.  
Qed.

Lemma In_subst_Problem_im_1 : forall X Y P t,
                            set_In Y (set_remove Var_eqdec X (Problem_vars P)) ->
                            set_In Y (Problem_vars (P|^^([(X,t)])))  .
Proof.
  intros. induction P; simpl in *|-*; trivial.
  destruct a; simpl in *|-*.
  generalize H. intro H'.
  apply set_remove_1 in H.
  apply set_remove_2 in H'.  
  apply set_union_elim in H. destruct H.
  apply set_union_intro1.
  apply In_subst_terms_im_1. apply set_remove_3; trivial.
  apply set_union_intro2. apply IHP.
  apply set_remove_3; trivial.
  apply set_union_nodup.
  apply NoDup_term_vars.  
  apply NoDup_Problem_vars.
  generalize H. intro H'.  
  apply set_remove_1 in H.
  apply set_remove_2 in H'.  
  apply set_union_elim in H. destruct H.
  apply set_union_intro1.
  apply In_subst_terms_im_1. apply set_remove_3; trivial.
  apply set_union_intro2.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1.
  apply In_subst_terms_im_1. apply set_remove_3; trivial.
  apply set_union_intro2. apply IHP.
  apply set_remove_3; trivial.
  apply set_union_nodup.
  apply NoDup_term_vars.  
  apply set_union_nodup.
  apply NoDup_term_vars.  
  apply NoDup_Problem_vars. 
Qed.

Lemma In_subst_Problem_im_2 : forall X Y P t, 
                            set_In X (Problem_vars P) ->
                            set_In Y (term_vars t) ->
                            set_In Y (Problem_vars (P|^^([(X,t)]))).
Proof.
  intros. induction P; simpl in *|-*; trivial.
  destruct a; simpl in *|-*. apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply In_subst_terms_im_2; trivial.
  apply set_union_intro2. apply IHP; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply In_subst_terms_im_2; trivial. 
  apply set_union_elim in H. destruct H.
  apply set_union_intro2. apply set_union_intro1.
  apply In_subst_terms_im_2; trivial. 
  apply set_union_intro2. apply set_union_intro2.
  apply IHP; trivial.
Qed.
  
Lemma In_subst_Problem_im : forall X Y P t,
                            set_In X (Problem_vars P) ->
                            set_In Y (set_union Var_eqdec (set_remove Var_eqdec X (Problem_vars P)) (term_vars t)) ->
                            set_In Y (Problem_vars (P|^^([(X,t)])))  .
Proof.
  intros. apply set_union_elim in H0. destruct H0.
  apply In_subst_Problem_im_1; trivial.
  apply In_subst_Problem_im_2; trivial.
Qed.

Lemma set_In_subs_problem : forall u P S, set_In u P -> set_In (subs_Constraint u S) (P|^^S).
Proof.
  intros. induction P; simpl in H. contradiction.
  destruct a; simpl. destruct H; try rewrite <- H.
  left~. right~. destruct H; try rewrite <- H. 
  left~. right~.
Qed.

Lemma set_In_subs_remove_problem  : forall u u' S P,
                                      set_In u ((P\u')|^^S) -> set_In u (P|^^S).
Proof.
  intros. induction P. simpl in H. contradiction.
  simpl in *|-*. gen H. case (Constraint_eqdec u' a); intros H0 H.
  destruct a. simpl. right~. simpl. right~.
  destruct a; simpl in H|-*;
  destruct H. left~. right~. left~. right~.
Qed.

Lemma set_In_subs : forall u S P, set_In u (P|^^S) ->
                                  exists u', u = subs_Constraint u' S /\ set_In u' P. 
Proof.
  intros. induction P. simpl in H. contradiction.
  destruct a; simpl in H; destruct H.
  exists (a#?t). unfold subs_Constraint. rewrite H. split~. left~.
  apply IHP in H. case H; clear H; intros u' H. destruct H.
  exists u'. split~. right~.
  exists (t~?t0). unfold subs_Constraint. rewrite H. split~. left~.
  apply IHP in H. case H; clear H; intros u' H. destruct H.
  exists u'. split~. right~.  
Qed.

Lemma set_In_subs_fresh_constraints : forall C S a s, set_In (a#?s) (C /? S) ->
                                                      exists X, set_In (a,X) C /\ s = []|.X|^S.
Proof.
  intros. induction C. simpl in H. contradiction.
  destruct a0. simpl in H. gen H.
  case (In_dom_dec v S); intros H0 H.
  apply set_add_elim in H. destruct H.
  exists v. inverts H. simpl. split~.
  apply IHC in H. case H; clear H; intros X H.
  destruct H. exists X. split~. right~.
  apply IHC in H. case H; clear H; intros X H.
  destruct H. exists X. split~. right~.
Qed.

Lemma length_Problem_vars_subs : forall P X t, set_In X (Problem_vars P) ->
                                   length (Problem_vars (P|^^([(X,t)]))) =
                                   length (set_union Var_eqdec (set_remove Var_eqdec X (Problem_vars P)) (term_vars t)).         
Proof.
  intros. apply subset_list_eq; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  apply set_union_nodup.
  rewrite <- remove_eq_set_remove. 
  apply NoDup_remove_3. apply NoDup_Problem_vars.
  apply NoDup_Problem_vars. apply NoDup_term_vars.
  split~; intro H0.
  case (set_In_dec Var_eqdec X (term_vars t)); intro H1.
  case (b ==v X); intro H2.
  apply set_union_intro2. rewrite H2; trivial.
  apply In_im_subst_term_Problem' in H0.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_remove_3; trivial.
  apply set_union_intro2; trivial. generalize H0; intro H0'.
  apply In_im_subst_term_Problem' in H0.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_remove_3; trivial.
  intro H2. rewrite H2 in H0'. apply In_im_subst_term_Problem in H0'.
  contradiction. apply set_union_intro2; trivial.
  apply In_subst_Problem_im; trivial.
Qed.