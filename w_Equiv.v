(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : w_Equiv.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 3, 2017.
 ============================================================================
*)

Require Export Fresh.

Inductive w_equiv : term -> term -> Prop :=

 | w_equiv_Ut   : w_equiv (<<>>) (<<>>) 

 | w_equiv_Pr   : forall t1 t2 t1' t2', (w_equiv t1 t1') -> (w_equiv t2 t2') -> 
                                          w_equiv  (<|t1,t2|>)  (<|t1',t2'|>)  

 | w_equiv_Fc   : forall m n t t', (w_equiv t t') -> 
                               w_equiv (Fc m n t) (Fc m n t')

 | w_equiv_Ab : forall a t t', (w_equiv t t') -> 
                           w_equiv ([a]^t) ([a]^t')

 | w_equiv_At   : forall a, w_equiv (%a) (%a)

 | w_equiv_Su   : forall p p' X, (forall a, ~ (In_ds p p' a)) -> 
                                  w_equiv (p|.X) (p'|.X) 
.

Hint Constructors w_equiv.

Notation "t ~we t'" := (w_equiv t t') (at level 67).


(** Intro and elim lemmas *)

Lemma w_equiv_At_intro : forall a a', a = a' -> At a ~we At a'.
Proof. intros. rewrite H. apply w_equiv_At. Qed.

Lemma w_equiv_Ab_intro : forall a a' t t',
  a = a' -> t ~we t' -> [a]^t ~we [a']^t'.
Proof. intros. rewrite H. apply w_equiv_Ab; trivial. Qed.


(** Reflexivity of  w_equiv *)

Lemma w_equiv_refl : forall t, t ~we t .
Proof.
 intros. induction t.
 apply w_equiv_Ut. apply w_equiv_At. apply w_equiv_Ab; trivial.
 apply w_equiv_Pr; trivial. apply w_equiv_Fc; trivial.
 apply w_equiv_Su. intros. apply not_In_ds. trivial.
Qed.

(** Symmetry of w_equiv *)

Lemma w_equiv_sym : forall t1 t2, t1 ~we t2 -> t2 ~we t1.
Proof. 
 intros. induction H. apply w_equiv_Ut.
 apply w_equiv_Pr; trivial. apply w_equiv_Fc; trivial.
 apply w_equiv_Ab; trivial. apply w_equiv_At. 
 apply w_equiv_Su; intros. intro. apply (H a).
 apply ds_sym. trivial.
Qed.

(* Transitivity of w_equiv *)

Lemma w_equiv_trans : forall t1 t2 t3, t1 ~we t2 -> t2 ~we t3 -> t1 ~we t3.
Proof.
 intros. generalize t3 H0; clear t3 H0. 
 induction H; intros t3 H'; inversion H'.
 apply w_equiv_Ut. apply w_equiv_Pr; 
[apply IHw_equiv1 | apply IHw_equiv2]; trivial.
 apply w_equiv_Fc; apply IHw_equiv; trivial. 
 apply w_equiv_Ab; apply IHw_equiv; trivial.
 apply w_equiv_At. apply w_equiv_Su. intro a'.
 apply not_In_ds. setoid_rewrite not_In_ds in H3.
 setoid_rewrite not_In_ds in H. rewrite H. apply H3.
Qed.

(* Freshness preservation of w_equiv *)

Lemma w_equiv_fresh : forall C a t1 t2, C |- a # t1 -> t1 ~we t2 -> C |- a # t2.
Proof.
 intros. induction H0; trivial.  
 apply fresh_Pr_elim in H. destruct H.
 apply fresh_Pr; [apply IHw_equiv1 | apply IHw_equiv2]; trivial.
 apply fresh_Fc_elim in H. apply fresh_Fc; apply IHw_equiv; trivial.
 apply fresh_Ab_elim in H. destruct H. rewrite H. apply fresh_Ab_1.
 destruct H. apply fresh_Ab_2; trivial. apply IHw_equiv; trivial.
 apply fresh_Su_elim in H. apply fresh_Su.
 assert (Q : (p $ (!p $ a)) = (p' $ (!p $ a))). apply not_In_ds. apply H0.
 gen_eq g : (!p); intro. replace p with (!g) in Q. rewrite perm_inv_atom in Q.
 symmetry in Q.  apply perm_inv_side_atom in Q. rewrite <- Q. trivial.
 rewrite H1. rewrite rev_involutive. trivial.
Qed.

(* Equivariance of w_equiv *)

Lemma w_equiv_equivariance : forall t1 t2 pi,
      t1 ~we t2 <-> (pi @ t1) ~we (pi @ t2).
Proof.
 split~; intros. generalize pi; clear pi.
 induction H; intros; simpl; auto.
 apply w_equiv_Su. intro. apply not_In_ds. 
 rewrite <- 2 perm_comp_atom. apply perm_eq_atom.
 apply not_In_ds. apply H. 
 generalize t2 H; clear t2 H. induction t1; intro t2; 
 destruct t2; simpl;
 intro H; inversion H; auto. 
 apply perm_eq_atom in H2. rewrite H2; auto. 
 apply perm_eq_atom in H3. rewrite H3.
 apply w_equiv_Ab.  apply IHt1; trivial.
 apply w_equiv_Su. intro. apply not_In_ds. setoid_rewrite not_In_ds in H1.
 apply perm_eq_atom with (p := pi). rewrite 2 perm_comp_atom. apply H1.
Qed.


(** Additional lemmas *)

Lemma w_equiv_perm_inv : forall t pi, (pi ++ !pi) @ t ~we t.
Proof.
 intro t. induction t; intros; simpl;  auto.
 rewrite <- perm_comp_atom. rewrite perm_inv_atom; auto.
 rewrite <- perm_comp_atom. rewrite perm_inv_atom; auto.
 apply w_equiv_Su; intro. apply not_In_ds. rewrite <- 2 perm_comp_atom. 
 rewrite perm_inv_atom; trivial.
Qed. 

Lemma w_equiv_pi_inv_side : forall pi t1 t2, 
 (!pi) @ t1 ~we t2 -> t1 ~we (pi @ t2).
Proof.
 intros. apply w_equiv_equivariance with (pi := pi) in H.
 apply w_equiv_trans with (t2 := (pi @ ((!pi) @ t1))); trivial.
 apply w_equiv_sym. rewrite perm_comp. gen_eq g : (!pi); intros.
 replace pi with (!g).  apply w_equiv_perm_inv. 
 rewrite H0. apply rev_involutive.
Qed.

Lemma w_equiv_swap_inv_side : forall a b t1 t2,
 (|[(a,b)]|) @ t1 ~we t2 -> t1 ~we ((|[(a,b)]|) @ t2).
Proof. intros. apply w_equiv_pi_inv_side. simpl rev; trivial. Qed.

Lemma w_equiv_swap_comm : forall t a b, |[(a, b)]| @ t ~we |[(b, a)]| @ t.
Proof. 
 intros. induction t; simpl; auto.
 apply w_equiv_At_intro. apply swap_comm.
 apply w_equiv_Ab_intro; trivial. apply swap_comm.
 apply w_equiv_Su; intro. apply not_In_ds. 
 rewrite <- 2 perm_comp_atom. apply swap_comm.
Qed.

Lemma w_equiv_pi_comm : forall a b t pi, 
 pi @ (|[(a,b)]| @ t) ~we (|[(pi $ a, pi $ b)]| @ (pi @ t)) . 
Proof.
  intros a b t pi.  
  gen_eq s0 : (|[(a, b)]|). intro Hs0.
  gen_eq s1 : (|[(pi $ a, pi $ b)]|). gen pi.
  induction t; intros pi Hs1; simpl; auto;
    try rewrite Hs0 in *|-*; try rewrite Hs1 in *|-*;
    try rewrite pi_comm_atom; auto.  
  apply w_equiv_Su; intro. apply not_In_ds.
  rewrite <- 4 perm_comp_atom. rewrite pi_comm_atom; auto.
Qed.

Lemma w_equiv_swap_cancel: forall a a' pi t,
  (((a, a')::(a, a')::pi) @ t) ~we (pi @ t).
Proof.
 intros. rewrite 2 swap_app.
 apply w_equiv_equivariance. 
 apply w_equiv_sym.
 apply w_equiv_swap_inv_side.
 apply w_equiv_refl.
Qed.

Lemma w_equiv_swap_cancel2: forall a a' pi t,
 ((pi ++ (|[(a, a')]|)) ++ (|[(a, a')]|) @ t) ~we (pi @ t).
Proof.
 intros. repeat rewrite <- perm_comp.
 apply w_equiv_sym.
 apply w_equiv_swap_inv_side.
 apply w_equiv_refl.
Qed.

