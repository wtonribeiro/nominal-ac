(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Substs.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: April 8, 2017.
 ============================================================================
*)

Require Export Problems.

Fixpoint look_up (X : Var) (S : Subst) {struct S}: term :=
match S with
 | []         => []|.X
 | (Y,t)::S0  => if Y ==v X then t else (look_up X S0)
end.

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


Fixpoint alist_rec (S1 S2: Subst) 
                   (F: Var -> term -> Subst -> Subst -> Subst) : Subst :=
 match S1 with 
    | []          =>  S2
    | (X,t)::S0  =>  F X t S2 (alist_rec S0 S2 F)
 end.

Definition F_rec (S1: Subst) (X:Var) (t:term) (S2 S3: Subst) := (X,t|^S1)::S3.

Definition Subst_comp (S1 S2: Subst) := alist_rec S1 S2 (F_rec S2). 
Notation "S1 © S2" := (Subst_comp S1 S2) (at level 67).

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

Definition subs_Constraint (u : Constraint) (S : Subst) : Constraint :=
  match u with
    | a#?t => a#?(t|^S)
    | s~?t => s|^S~?(t|^S)
  end.

Fixpoint subs_Problem (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (a#?t)::P0 => (a#?(t|^S))::(subs_Problem P0 S)
    | (s~?t)::P0 => ((s|^S)~?(t|^S))::(subs_Problem P0 S)
  end.

Notation "P |^^ S" := (subs_Problem P S) (at level 67).
 

Definition fresh_env (C C' : Context) (S : Subst) :=
forall a X, set_In (a, X) C -> C' |- a # (([]|.X)|^S) .

Definition subs_equiv (C: Context) (E : Context -> term -> term -> Prop) (S S' : Subst) :=
forall X, (X € S) \/ (X € S') -> E C (([]|.X)|^S) (([]|.X)|^S').


Fixpoint subst_dom_vars (S : Subst) : set Var :=
  match S with
    | [] => []   
    | (X,t)::S0 => set_add Var_eqdec X (subst_dom_vars S0)
  end.  
              
Fixpoint dom_rec_aux (S : Subst) (St : set Var) : set Var :=
  match St with
    | [] => []
    | X::St0 => if (term_eqdec (([]|.X)|^S) ([]|.X)) then
                   (dom_rec_aux S St0) else
                   (set_add Var_eqdec X (dom_rec_aux S St0))
  end.                  

Definition dom_rec (S : Subst) := dom_rec_aux S (subst_dom_vars S).

Fixpoint im_rec_aux (S : Subst) (St : set Var) : set term :=
  match St with
    | [] => []  
    | X::St0 => ([]|.X|^S)::(im_rec_aux S St0) 
  end.

Definition im_rec (S : Subst) := im_rec_aux S (dom_rec S).

Fixpoint terms_set_vars (T: set term) : set Var :=
  match T with
    | [] => []
    | s::T0 => set_union Var_eqdec (term_vars s) (terms_set_vars T0)        
  end.

Definition im_vars (S : Subst) := terms_set_vars (im_rec S). 

Fixpoint set_Subst  (T : set term) (S : Subst) : set term :=
  match T with
    | [] => []
    | s::T0 => (s|^S)::(set_Subst T0 S)
  end.                    


(** Lemmas *)

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

Lemma not_In_dom : forall X S pi, ~ X € S -> (pi|.X)|^S = pi|.X.
Proof.
  intros. replace (pi|.X) with (pi @ ([]|.X)).
  rewrite subst_perm_comm.
  case (term_eqdec (([]|.X)|^S) ([]|.X)); intro H0.
  rewrite H0; trivial. unfold In_dom in H.
  contradiction. autorewrite with perm.
  simpl; trivial.
Qed.

Lemma not_occurs : forall X t1 t2, (~ set_In X (term_vars t1)) -> t1|^([(X,t2)]) = t1.
Proof.
 intros. induction t1; simpl; trivial; simpl in H.
 fequals. apply IHt1; trivial.
 fequals; [apply IHt1_1 | apply IHt1_2]; intro H0; apply H.
 apply set_union_intro1; trivial. apply set_union_intro2; trivial.
 fequals; apply IHt1; trivial.
 case (X ==v v); intro H0. false. apply H. left~.
 autorewrite with perm. simpl; trivial.
Qed.

Lemma subst_var_eq : forall X pi t, (pi|.X)|^([(X,t)]) = pi @ t.
Proof.
  intros. simpl. case (X ==v X); intro H; trivial. false. 
Qed.  

Lemma subst_id : forall t, t|^([]) = t.
Proof. 
  intros. induction t; auto.
  simpl. rewrite IHt; trivial.
  simpl. rewrite IHt1; rewrite IHt2; trivial.
  simpl. rewrite IHt; trivial.
  destruct p; simpl; trivial.
Qed.  

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
                                set_In t (im_rec S) -> exists X, X € S /\ t = ([]|.X)|^S.
Proof.
  intros. unfold im_rec in H.
  setoid_rewrite In_dom_eq_dom_rec.
  induction (dom_rec S).
  simpl in H. contradiction.
  simpl in *|-*.  destruct H.
  exists a. rewrite H. split~.
  apply IHs in H. clear IHs.
  case H; clear H; intros X H. destruct H.
  exists X. split~.
Qed.
  
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
  
Lemma In_im_subst_term : forall X s t,
                            set_In X (term_vars (s|^([(X,t)]))) -> set_In X (term_vars t).
Proof.
  intros.
  induction s; simpl in *|-*;
      try contradiction; try apply IHs; trivial.
  apply set_union_elim in H.
  destruct H; [apply IHs1 | apply IHs2]; trivial.
  gen H. case (X ==v v); intros.
  rewrite perm_term_vars in H; trivial.
  autorewrite with perm in H. simpl in H.
  destruct H. symmetry in H. contradiction.
  contradiction.
Qed.

Lemma In_im_subst_term' : forall X Y s t,   set_In Y (term_vars (s|^([(X,t)]))) ->
                                            set_In Y (set_union Var_eqdec (term_vars s) (term_vars t)).
Proof.
  intros.
  induction s; simpl in *|-*;
      try contradiction; try apply IHs; trivial.
  apply set_union_elim in H. destruct H.
  apply IHs1 in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2; trivial.
  apply IHs2 in H. apply set_union_elim in H. destruct H.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2; trivial. 
  gen H. case (X ==v v); intros;
         rewrite perm_term_vars in H.
  apply set_union_intro2; trivial.
  simpl in H. destruct H; try contradiction.
  apply set_union_intro1. simpl. left~.
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
  intros. induction s; simpl in *|-*; trivial.
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
  
Lemma In_im_subst_terms_set : forall X T t, set_In X (terms_set_vars (set_Subst T ([(X,t)]))) ->
                                            set_In X (term_vars t).
Proof.
  intros. induction T. simpl in H. contradiction.
  simpl in H. apply set_union_elim in H.
  destruct H. apply In_im_subst_term in H; trivial.
  apply IHT; trivial.
Qed.

Lemma In_im_subst_terms_set' : forall X Y T t, set_In Y (terms_set_vars (set_Subst T ([(X,t)]))) ->
                                               set_In Y (set_union Var_eqdec (terms_set_vars T) (term_vars t)).
Proof.
  intros. induction T. simpl in H. contradiction.
  simpl in *|-*. apply set_union_elim in H.
  destruct H. case (Y ==v X); intro H0.
  rewrite H0 in *|-*.
  apply In_im_subst_term in H.
  apply set_union_intro2; trivial.
  apply In_im_subst_term' in H; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1.
  apply set_union_intro1; trivial.
  apply set_union_intro2; trivial.
  apply IHT in H; clear IHT.
  apply set_union_elim in H.
  destruct H.
  apply set_union_intro1.
  apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.
Qed.
  
Lemma terms_set_vars_add : forall St t X,
                             set_In X (terms_set_vars (set_add term_eqdec t St)) <->
                             set_In X (set_union Var_eqdec (term_vars t) (terms_set_vars St)).
Proof.
  intros. induction St; simpl.
  split~; intro H; trivial.
  case (term_eqdec t a); intro H0; simpl.
  rewrite H0. split~; intro H.
  apply set_union_intro2; trivial.
  apply set_union_elim in H. destruct H; trivial.
  apply set_union_intro1; trivial.
  split~; intro H. apply set_union_elim in H.
  destruct H. apply set_union_intro2.
  apply set_union_intro1; trivial.
  apply IHSt in H. apply set_union_elim in H.
  destruct H. apply set_union_intro1; trivial.
  apply set_union_intro2.
  apply set_union_intro2; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro2. apply IHSt.
  apply set_union_intro1; trivial.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  apply IHSt. apply set_union_intro2; trivial.
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
  
Lemma In_im_comp_add : forall S X s t, ~ set_In X (dom_rec S) -> 
                       set_In s (im_rec (S © [(X,t)])) ->
                       set_In s (set_add term_eqdec t (set_Subst (im_rec S) ([(X,t)]))).
Proof.
  intros. apply im_rec_to_In_dom in H0.
  case H0; clear H0; intros Y H0. destruct H0.
  apply dom_comp_add1 in H0. destruct H0.
  rewrite subst_comp_expand in H1. rewrite H0 in H1.
  rewrite not_In_dom in H1. rewrite subst_var_eq in H1.
  autorewrite with perm in H1. apply set_add_intro2; trivial.
  rewrite In_dom_eq_dom_rec; trivial.
  rewrite In_dom_eq_dom_rec in H0.
  rewrite subst_comp_expand in H1. rewrite H1.
  clear H H1. unfold im_rec.
  apply set_add_intro1. induction (dom_rec S).
  simpl in H0. contradiction. simpl in H0.
  destruct H0. rewrite H. simpl.
  autorewrite with perm. left~.
  apply IHs0 in H. clear IHs0.
  simpl. right~.
Qed.  

Lemma im_vars_comp_add1 : forall S t X Y,
                             ~ set_In X (dom_rec S) ->
                             set_In Y (im_vars (S © [(X,t)])) ->
                             set_In Y (set_union Var_eqdec  (im_vars S) (term_vars t)).
Proof.
  intros. unfold im_vars in *|-.
  apply terms_set_vars_subset with
  (St1:= set_add term_eqdec t (set_Subst (im_rec S) ([(X,t)]))) in H0.
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
  (St1:= set_add term_eqdec t (set_Subst (im_rec S) ([(X,t)]))) in H0.
 apply terms_set_vars_add in H0. apply set_union_elim in H0.
 destruct H0; trivial. apply In_im_subst_terms_set in H0; trivial.
 intros. apply In_im_comp_add; trivial.
Qed.

Lemma inter_dom_term_vars : forall t S, set_inter Var_eqdec (term_vars t) (dom_rec S) = [] -> t|^S = t.
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
  rewrite not_In_dom; trivial. intro H0.
  apply set_inter_nil with (a:=v) in H.
  apply H. apply set_inter_intro.
  simpl. left~. apply In_dom_eq_dom_rec; trivial.
  simpl; trivial.
Qed.  

Open Scope nat_scope.

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
  apply c_equiv_pi'; intros.
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
  replace (look_up X S1) with (([]|.X)|^S1).
  replace (look_up X S2) with (([]|.X)|^S2).
  rewrite 2 not_In_dom; trivial.
  apply c_equiv_refl.
  simpl; autorewrite with perm; trivial.
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
  replace (look_up X S1) with (([]|.X)|^S1).
  replace (look_up X S2) with (([]|.X)|^S2).
  rewrite 2 not_In_dom; trivial.
  apply c_equiv_refl.
  simpl; autorewrite with perm; trivial.
  simpl; autorewrite with perm; trivial. 
  case (In_dom_dec X S2); intro H2. apply H0. left~.
  case (In_dom_dec X S3); intro H3. apply H0. right~.  
  replace (look_up X S2) with (([]|.X)|^S2).
  replace (look_up X S3) with (([]|.X)|^S3).
  rewrite 2 not_In_dom; trivial.
  apply c_equiv_refl.
  simpl; autorewrite with perm; trivial.
  simpl; autorewrite with perm; trivial. 
  apply H0. right~.
Qed.

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
  rewrite not_In_dom in H1; trivial.
  simpl in H1. destruct H1; try contradiction.
  apply In_dom_eq_dom_rec in H2. rewrite <- H in H2. contradiction.
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