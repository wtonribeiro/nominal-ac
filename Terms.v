(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Terms.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 26, 2017.
 ============================================================================
*)

Set Implicit Arguments.
Require Import Max.
Require Export List ListFacts ListSet Omega LibTactics.

Inductive Atom : Set := atom : nat -> Atom.
Inductive Var  : Set := var  : nat -> Var.
Definition Perm := list (Atom * Atom).


(** Grammar *)

Inductive term : Set :=
  | Ut : term
  | At : Atom -> term 
  | Ab : Atom -> term -> term
  | Pr : term -> term -> term 
  | Fc : nat -> nat -> term -> term
  | Su : Perm -> Var -> term  
.

Notation "<<>>" := (Ut) (at level 67). 
Notation "% a " := (At a) (at level 67). 
Notation "[ a ] ^ t" := (Ab a t) (at level 67).
Notation "<| t1 , t2 |>" := (Pr t1 t2) (at level 67).
Notation "pi |. X" := (Su pi X) (at level 67).


(** Atoms decidability *)

Lemma Atom_eqdec : forall a b : Atom, {a = b} + {a <> b}.
Proof.
 intros. destruct a. destruct b. case (eq_nat_dec n n0); intros.
 left~. right~. intro. inversion H. contradiction.
Qed.

Notation "a ==at b" := (Atom_eqdec a b) (at level 67).


(** Variables decidability *)

Lemma Var_eqdec : forall X Y : Var, {X = Y} + {X <> Y}.
Proof.
 intros. destruct X. destruct Y. case (eq_nat_dec n n0); intros.
 left~. right~. intro. inversion H. contradiction.
Qed.

Notation "X ==v Y" := (Var_eqdec X Y) (at level 67).


(** Decidability of nat pairs *)

Lemma nat_pair_eqdec: forall (p1 p2 : nat * nat), {p1 = p2} + {p1 <> p2}. 
Proof.
  intros. destruct p1. destruct p2.
  case (eq_nat_dec n n1); case (eq_nat_dec n0  n2);
  intros H1 H2; try rewrite H1; try rewrite H2.
  left~; trivial. right~; fequals.
  right~; fequals. right~; fequals.
Qed.

Notation "p1 ==np p2" := (nat_pair_eqdec p1 p2) (at level 67).

(** Decidability of atom pairs *)

Lemma Atom_pair_eqdec: forall (p1 p2 : Atom * Atom), {p1 = p2} + {p1 <> p2}. 
Proof.
  intros. destruct p1. destruct p2.
  case (a ==at a1); case (a0 ==at a2);
  intros H1 H2; try rewrite H1; try rewrite H2.
  left~; trivial. right~; fequals.
  right~; fequals. right~; fequals.
Qed.

Lemma Atom_list_eqdec: forall (l1 l2 : list Atom), {l1 = l2} + {l1 <> l2}. 
Proof.
  intros. gen l2. induction l1; intro l2; destruct l2.
  left~; right~. right~. discriminate.
  right~. discriminate. case (IHl1 l2); intro H0.
  case (a ==at a0); intro H1.
  left~. rewrite H0. rewrite H1. trivial.
  right~. intro H2. inversion H2. contradiction.
  right~. intro H2. inversion H2. contradiction. 
Qed.


Lemma Perm_eqdec : forall p p' : Perm, {p = p'} + {p <> p'}.
Proof.
 intro p. induction p.
 intro p'; destruct p'. left~. right~.
 intro H. inversion H. 
 intro p'. destruct p'. right~.
 intro H. inversion H. destruct a. destruct p0.
 case (Atom_pair_eqdec (a, a0) (a1, a2)); intros. 
 case (IHp p'); intros. left~. rewrite e. rewrite e0; trivial.
 right~. intro H. inverts H. apply n; trivial.
 right~. intro H. inverts H. apply n; trivial.
Qed.

Notation "p0 ==P p1" := (Perm_eqdec p0 p1) (at level 67). 
 
Lemma term_eqdec : forall t1 t2 : term, {t1 = t2} + {t1 <> t2}.
Proof.
 intro t1. induction t1; intro t2; destruct t2. left~.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 case (a ==at a0); intro H. rewrite H. left~.
 right~. intro H'. inverts H'. apply H; trivial.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 case (a ==at a0); intro H. rewrite H.
 case (IHt1 t2); intro H'. rewrite H'. left~.
 right~. intro H''. inverts H''. apply H'; trivial.
 right~. intro H''. inverts H''. apply H; trivial. 
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 case (IHt1_1 t2_1); intro H0. case (IHt1_2 t2_2); intro H1.
 rewrite H0. rewrite H1. left~.
 right~. intro H'. inverts H'. apply H1; trivial.
 right~. intro H'. inverts H'. apply H0; trivial.  
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 case ((n,n0) ==np (n1,n2)); intro H. inverts H.
 case (IHt1 t2); intro H'. rewrite H'. left~.
 right~. intro H''. inverts H''. apply H'; trivial. 
 right~. intro H''. inverts H''. apply H; trivial. 
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 right~; discriminate.  right~; discriminate.
 case (p ==P p0); intro H. case (v ==v v0); intro H'.
 rewrite H. rewrite H'. left~.
 right~. intro H''. inverts H''. apply H'; trivial.
 right~. intro H'. inverts H'. apply H; trivial.  
Qed.  



(** Size of a term  *)

Fixpoint term_size (t : term) {struct t} : nat :=
 match t with
  | [a]^t1  => 1 + term_size t1
  | <|t1,t2|> => 1 + term_size t1 + term_size t2 
  | Fc E n t1  => 1 + term_size t1
  | _   => 1  
 end.


Lemma term_size_Pr_l : forall t1 t2, term_size t1 < term_size (<|t1,t2|>).
Proof. intros. simpl. omega. Qed.

Lemma term_size_Pr_r : forall t1 t2, term_size t2 < term_size (<|t1,t2|>).
Proof. intros. simpl. omega. Qed.

Lemma term_size_Fc : forall E n t, term_size t < term_size (Fc E n t).
Proof. intros. simpl. omega. Qed.

Lemma term_size_Ab : forall a t, term_size t < term_size ([a]^t).
Proof. intros. simpl. omega. Qed.

Hint Resolve term_size_Pr_l.
Hint Resolve term_size_Pr_r.
Hint Resolve term_size_Fc.
Hint Resolve term_size_Ab.

Lemma term_size_gt_0 : forall t, term_size t > 0.
Proof. introv. induction t; simpl; try omega; auto. Qed.

Hint Resolve term_size_gt_0.


(** The set of variables that occur in a term *)

Fixpoint term_vars (t : term) {struct t} : set Var := 
match t with
 | Ut       => empty_set _
 | At a     => empty_set _
 | Su p X   => set_add Var_eqdec X (empty_set _)
 | Pr t1 t2 => set_union Var_eqdec (term_vars t1) (term_vars t2)
 | Ab a t1  => term_vars t1
 | Fc E n t1  => term_vars t1
end.

(** Subterms *)

Fixpoint subterms (t : term) {struct t} : set term :=
match t with
| Ut        => set_add term_eqdec Ut (empty_set _)
| At a      => set_add term_eqdec (At a) (empty_set _)
| Su p Y    => set_add term_eqdec (Su p Y) (empty_set _)
| Ab a t1   => set_add term_eqdec (Ab a t1) (subterms t1)
| Pr t1 t2  => set_add term_eqdec (Pr t1 t2) 
              (set_union term_eqdec (subterms t1) (subterms t2))
| Fc E n t1   => set_add term_eqdec (Fc E n t1) (subterms t1)
end.

Definition psubterms (t : term) := set_remove term_eqdec t (subterms t).


Lemma Pr_eqdec : forall s, {exists u, exists v, s = <|u,v|>} + {forall u v, s <> <|u,v|>} .
Proof.
  intros. destruct s.
  right~; intros; discriminate. right~; intros; discriminate.  
  right~; intros; discriminate.
  left~. exists s1. exists s2; trivial.
  right~; intros; discriminate. right~; intros; discriminate.  
Qed.

Definition is_Pr (s:term) : Prop :=
  match s with
    | <|s0,s1|> => True
    | _ => False
  end . 

Lemma Su_eqdec : forall s, {exists pi, exists X, s = pi|.X} + {forall pi X, s <> pi|.X} .
Proof.
  intros. destruct s.
  right~; intros; discriminate.
  right~; intros; discriminate.  
  right~; intros; discriminate. 
  right~; intros; discriminate.
  right~; intros; discriminate.  
  left~. exists p. exists v; trivial.
Qed.

Definition is_Su (s:term) : Prop :=
  match s with
    | pi|.X => True
    | _ => False
  end .

Lemma is_Pr_exists : forall s, is_Pr s -> exists u, exists v, s = <|u,v|>.
Proof.
  intros. destruct s; simpl in H; try contradiction.
  exists s1. exists s2; trivial.
Qed.

Lemma is_Pr_Su : forall s, is_Su s -> exists pi, exists X, s = pi|.X .
Proof.
  intros. destruct s; simpl in H; try contradiction.
  exists p. exists v; trivial.
Qed.  

Lemma isnt_Pr : forall s, (forall u v, s <> <| u, v |>) -> ~ is_Pr s.
Proof.
  intros. intro H0. destruct s; simpl in H0; trivial.
  apply (H s1 s2); trivial.
Qed.  

Lemma isnt_Su : forall s, (forall pi X, s <> pi|.X) -> ~ is_Su s.
Proof.
  intros. intro H0. destruct s; simpl in H0; trivial.
  apply (H p v); trivial.
Qed.

Lemma Fc_eqdec : forall s, {exists E, exists n, exists u, s = Fc E n u} + {forall E n u, s <> Fc E n u} .
Proof.
  intros. destruct s.
  right~; intros; discriminate.
  right~; intros; discriminate.  
  right~; intros; discriminate. 
  right~; intros; discriminate.
  left~. exists n. exists n0. exists s. trivial.
  right~; intros; discriminate.  
Qed.
  

(** Lemmas about subterms and psubterms *)

Lemma nodup_subterms : forall s, NoDup (subterms s).
Proof.
  induction s; simpl.
  apply NoDup_cons. simpl. intro; trivial. apply NoDup_nil.
  apply NoDup_cons. simpl. intro; trivial. apply NoDup_nil.
  apply set_add_nodup; trivial.
  apply set_add_nodup. apply set_union_nodup; trivial.
  apply set_add_nodup; trivial.
  apply NoDup_cons. simpl. intro; trivial. apply NoDup_nil.
Qed.  

Lemma psubterms_to_subterms : forall s t, set_In s (psubterms t) -> set_In s (subterms t).
Proof.
  intros. unfold psubterms in H. apply set_remove_1 in H; trivial.
Qed.

Lemma In_subterms : forall s, set_In s (subterms s).
Proof.
  intros. destruct s; simpl; auto;
  try apply set_add_intro2; trivial.
Qed.
  
Lemma not_In_psubterms : forall s, ~ set_In s (psubterms s).
Proof.
  intros. intro H. unfold psubterms in H.
  apply set_remove_2 in H.
  apply H; trivial.
  apply nodup_subterms.
Qed.

Lemma Ab_psubterms : forall a s, set_In s (psubterms ([a]^s)).
Proof.
  intros. unfold psubterms. apply set_remove_3; simpl.
  apply set_add_intro1. apply In_subterms.
  intro H. induction s; inverts H. apply IHs; trivial.
Qed.

Lemma Fc_psubterms : forall E n s,  set_In s (psubterms (Fc E n s)).
Proof.
  intros. unfold psubterms. apply set_remove_3; simpl.
  apply set_add_intro1. apply In_subterms.
  intro H. induction s; inverts H. apply IHs; trivial.
Qed.

Lemma Pr_psubterms : forall s t, set_In s (psubterms (<|s,t|>)) /\ set_In t (psubterms (<|s,t|>)).
Proof.
  intros. unfold psubterms. split~; apply set_remove_3; simpl;
  try apply set_add_intro1; try apply In_subterms.
  apply set_union_intro1. apply In_subterms; trivial. 
  intro H. induction s; inverts H. apply IHs1; trivial.
  apply set_union_intro2. apply In_subterms; trivial. 
  intro H. induction t; inverts H. apply IHt2; trivial.
Qed.

  
Lemma subterms_term_size_leq : forall s t, set_In s (subterms t) -> term_size s <= term_size t.
Proof.
  intros. induction t; simpl in *|-*.
  destruct H; try contradiction. rewrite <- H; simpl; omega.
  destruct H; try contradiction. rewrite <- H; simpl; omega.  
  apply set_add_elim in H. destruct H. rewrite H; simpl; omega.
  assert (Q: term_size s <= term_size t).  apply IHt. trivial. omega.
  apply set_add_elim in H. destruct H. rewrite H. simpl; omega.
  apply set_union_elim in H. destruct H.
  assert (Q: term_size s <= term_size t1). apply IHt1; trivial. omega. 
  assert (Q: term_size s <= term_size t2). apply IHt2; trivial. omega.
  apply set_add_elim in H. destruct H. rewrite H; simpl; omega.
  assert (Q: term_size s <= term_size t).  apply IHt. trivial. omega.
  destruct H; try contradiction. rewrite <- H; simpl; omega.
Qed.  

Lemma psubterms_term_size_lt : forall s t, set_In s (psubterms t) -> term_size s < term_size t.
Proof.
  intros. unfold psubterms in H.
  induction t; simpl in *|-*.
  gen H. case (term_eqdec (<<>>) (<<>>));
    intros; simpl in H; try contradiction. false.
  gen H. case (term_eqdec (%a) (%a));
    intros; simpl in H; try contradiction.   
  apply set_remove_add in H.
  case (term_eqdec s t); intro H0. rewrite H0. omega.
  assert (Q : term_size s < term_size t).
   apply IHt. apply set_remove_3; trivial.
  omega.
  apply set_remove_add in H.
  apply set_union_elim in H. destruct H.
  case (term_eqdec s t1); intro H0. rewrite H0. omega.
  assert (Q : term_size s < term_size t1).
   apply IHt1. apply set_remove_3; trivial.
  omega.
  case (term_eqdec s t2); intro H0. rewrite H0. omega.
  assert (Q : term_size s < term_size t2).
   apply IHt2. apply set_remove_3; trivial.
  omega.
  apply set_remove_add in H. 
  case (term_eqdec s t); intro H0. rewrite H0. omega.
  assert (Q : term_size s < term_size t).
   apply IHt. apply set_remove_3; trivial.
  omega.
 gen H. case (term_eqdec (p|.v) (p|.v));
    intros; simpl in H; try contradiction. 
Qed.

Lemma psubterms_not_In_subterms: forall s t, set_In s (psubterms t) -> ~ set_In t (subterms s).
Proof.
  intros. intro H'.
  apply psubterms_term_size_lt in H.
  apply subterms_term_size_leq in H'.
  omega.
Qed.  

Lemma subterms_trans : forall s t u,
                       set_In s (subterms t) -> set_In t (subterms u) -> set_In s (subterms u).
Proof.
  intros. induction u; simpl in *|-*.
  destruct H0; try contradiction.
  rewrite <- H0 in H. simpl in H; trivial.
  destruct H0; try contradiction.
  rewrite <- H0 in H. simpl in H; trivial.
  apply set_add_elim in H0. destruct H0.
  rewrite H0 in H. simpl in H; trivial.
  apply set_add_intro1. apply IHu; trivial.
  apply set_add_elim in H0. destruct H0. 
  rewrite H0 in H. simpl in H; trivial.
  apply set_union_elim in H0. apply set_add_intro1. destruct H0.
  apply set_union_intro1. apply IHu1; trivial. 
  apply set_union_intro2. apply IHu2; trivial.  
  apply set_add_elim in H0. destruct H0.
  rewrite H0 in H. simpl in H; trivial.
  apply set_add_intro1. apply IHu; trivial.
  destruct H0; try contradiction.
  rewrite <- H0 in H. simpl in H; trivial.
Qed.

Lemma psubterms_trans : forall s t u,
                        set_In s (psubterms t) -> set_In t (subterms u) -> set_In s (psubterms u).
Proof.
  intros. unfold psubterms.
  generalize H; intro H'. unfold psubterms in H'.
  apply set_remove_1 in H'.
  apply set_remove_3.
  apply subterms_trans with (t:=t); trivial.
  intro H1. rewrite H1 in H.
  apply psubterms_not_In_subterms in H.
  contradiction.
Qed.

  
Lemma subterms_eq : forall s t, (set_In s (subterms t) /\ set_In t (subterms s)) -> s = t.
Proof.
  intros. destruct H.
  gen t. induction s; intros; simpl in H0.
  destruct H0; try contradiction; trivial.
  destruct H0; try contradiction; trivial.
  apply set_add_elim in H0. destruct H0; auto.
  assert (Q : set_In ([a]^ s) (subterms s)).
   apply subterms_trans with (t:=t); trivial.
  assert (Q': set_In s (psubterms ([a]^s))). 
   apply Ab_psubterms.
  apply psubterms_not_In_subterms in Q'.
  contradiction.   
  apply set_add_elim in H0. destruct H0; auto.
  apply set_union_elim in H0. destruct H0.
  assert (Q : set_In (<|s1,s2|>) (subterms s1)).
   apply subterms_trans with (t:=t); trivial.
  assert (Q': set_In s1 (psubterms (<|s1,s2|>))). 
   apply Pr_psubterms.
  apply psubterms_not_In_subterms in Q'.
  contradiction.      
  assert (Q : set_In (<|s1,s2|>) (subterms s2)).
   apply subterms_trans with (t:=t); trivial.
  assert (Q': set_In s2 (psubterms (<|s1,s2|>))). 
   apply Pr_psubterms.
  apply psubterms_not_In_subterms in Q'.
  contradiction. 
  apply set_add_elim in H0. destruct H0; auto.
  assert (Q : set_In (Fc n n0 s) (subterms s)).
   apply subterms_trans with (t:=t); trivial.
  assert (Q': set_In s (psubterms (Fc n n0 s))). 
   apply Fc_psubterms.
  apply psubterms_not_In_subterms in Q'.
  contradiction. 
  destruct H0; try contradiction; trivial.  
Qed.  


Lemma Ab_neq_psub : forall a s, [a]^s <> s.
Proof.
  intros.
  assert (Q : set_In s (psubterms ([a]^s))).  
   apply Ab_psubterms.
  apply psubterms_not_In_subterms in Q. intro H.   
  assert (Q': set_In s (subterms s)).
   apply In_subterms.
  rewrite H in Q. contradiction.
Qed.

Lemma Fc_neq_psub : forall E n s, Fc E n s <> s.
Proof.
  intros.
  assert (Q : set_In s (psubterms (Fc E n s))).  
   apply Fc_psubterms.
  apply psubterms_not_In_subterms in Q. intro H.   
  assert (Q': set_In s (subterms s)).
   apply In_subterms.
  rewrite H in Q. contradiction.
Qed.

Lemma Pr_neq_psub_1 : forall s t, <|s,t|> <> s.
Proof.
  intros.
  assert (Q : set_In s (psubterms (<|s,t|>))).  
   apply Pr_psubterms.
  apply psubterms_not_In_subterms in Q. intro H.   
  assert (Q': set_In s (subterms s)).
   apply In_subterms.
  rewrite H in Q. contradiction.
Qed.

Lemma Pr_neq_psub_2 : forall s t, <|s,t|> <> t.
Proof.
  intros.
  assert (Q : set_In t (psubterms (<|s,t|>))).  
   apply Pr_psubterms.
  apply psubterms_not_In_subterms in Q. intro H.   
  assert (Q': set_In t (subterms t)).
   apply In_subterms.
  rewrite H in Q. contradiction.
Qed.


Lemma Fc_Pr_neq_psub_1 : forall E n s t, Fc E n (<|s,t|>) <> s.
Proof.
  intros.
  assert (Q : set_In s (psubterms (Fc E n (<|s,t|>)))).  
   apply psubterms_trans with (t := (<|s,t|>)).
   apply Pr_psubterms. simpl. apply set_add_intro1.
   apply set_add_intro2; trivial.
  apply psubterms_not_In_subterms in Q. intro H.
  assert (Q': set_In s (subterms s)).
   apply In_subterms.
  rewrite H in Q. contradiction.
Qed.


Lemma Fc_Pr_neq_psub_2 : forall E n s t, Fc E n (<|s,t|>) <> t.
Proof.
  intros.
  assert (Q : set_In t (psubterms (Fc E n (<|s,t|>)))).  
   apply psubterms_trans with (t := (<|s,t|>)).
   apply Pr_psubterms. simpl. apply set_add_intro1.
   apply set_add_intro2; trivial.
  apply psubterms_not_In_subterms in Q. intro H.
  assert (Q': set_In t (subterms t)).
   apply In_subterms.
  rewrite H in Q. contradiction.
Qed.