(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Fresh.v
 Authors     : Washington Luis R. de Carvalho Segundo and
               Mauricio Ayala Rincon 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : This file contains de definition of the freshness relation
               and some results about.

 Last Modified On: Sep 17, 2018.
 ============================================================================
 *)

Require Import Tuples.
Require Export Disagr.


Inductive fresh : Context -> Atom -> term -> Prop :=

 | fresh_Ut   : forall C a, fresh C a Ut 

 | fresh_Pr   : forall C a t1 t2, (fresh C a t1) -> (fresh C a t2) -> 
                                  (fresh C a (<|t1,t2|>))  

 | fresh_Fc   : forall C a E n t, (fresh C a t) -> 
                               (fresh C a (Fc E n t))

 | fresh_Ab_1 : forall C a t, fresh C a (Ab a t)

 | fresh_Ab_2 : forall C a a' t, a <> a' -> (fresh C a t) -> 
                                 (fresh C a (Ab a' t))

 | fresh_At   : forall C a a', a <> a' -> 
                               (fresh C a (At a'))

 | fresh_Su   : forall C p a X, set_In (((!p $ a), X)) C -> 
                               fresh C a (Su p X)  
.

Hint Constructors fresh.

Notation "C |- a # t" := (fresh C a t) (at level 67).

(** Basic lemmas *)

Lemma fresh_At_elim : forall C a b, (C |- a # At b) -> a <> b.
Proof. intros. inversion H; trivial. Qed.

Hint Resolve fresh_At_elim.

Lemma fresh_Pr_elim : forall C a t u, 
(C |- a # <|t,u|>) -> ((C |- a # t) /\ (C |- a # u)).  
Proof. intros. inversion H; split~; trivial. Qed.

Hint Resolve fresh_Pr_elim.

Lemma fresh_Fc_elim : forall C a E n t,
(C |- a # Fc E n t) -> C |- a # t.
Proof. intros. inversion H; trivial. Qed. 

Hint Resolve fresh_Fc_elim.

Lemma fresh_Ab_elim : forall C a b t, 
(C |- a # Ab b t) -> (a = b \/ ((a <> b) /\ (C |- a # t))).
Proof. 
 intros. inversion H. 
 left~; trivial.
 right~; split~; trivial.
Qed.

Hint Resolve fresh_Ab_elim.

Lemma fresh_Su_elim : forall C p a X, 
(C |- a # Su p X) -> set_In (((!p $ a), X)) C.
Proof. intros. inversion H; trivial. Qed.

Hint Resolve fresh_Su_elim.


Lemma fresh_lemma_1 : forall C pi a t, 
(C |- a # (pi @ t)) <-> (C |- ((!pi) $ a) # t).
Proof. 
 intros; induction t; simpl.
  
 split~; intros. 

 split~; intro H; inverts H;
   apply fresh_At; intro H0; apply H3;
   symmetry; apply perm_inv_side_atom;
   symmetry; trivial. 

 case (atom_eqdec a (pi $ a0)); intro H0.
 rewrite <- H0. replace ((!pi) $ a) with a0.
 split~; intro H1. apply perm_inv_side_atom.
 symmetry. trivial.
 split~; intro H1; inverts H1; apply fresh_Ab_2;
   try apply IHt; trivial.
   false. false.
   intro H1. apply H0.
   symmetry. apply perm_inv_side_atom;
   symmetry; trivial. 
   false. apply H0. symmetry.
   apply perm_inv_side_atom. trivial.

 split~; intro H; inverts H;
   apply fresh_Pr; try apply IHt1; try apply IHt2; trivial.
 
 split~; intro H; inverts H;
   apply fresh_Fc; apply IHt; trivial.   

 split~; intro H; inverts H;
  apply fresh_Su; try rewrite perm_comp_atom in *|-*;
  try rewrite <- distr_rev in *|-*; trivial.

 Qed.

Hint Resolve fresh_lemma_1.


Lemma fresh_lemma_2 : forall C pi a t, 
(C |- a # t) <-> (C |- (pi $ a) # (pi @ t)).  
Proof. 
  intros. split~; intro H.
  apply fresh_lemma_1. rewrite perm_inv_atom; trivial.
  apply fresh_lemma_1 in H. rewrite perm_inv_atom in H; trivial.
Qed.

Hint Resolve fresh_lemma_2.

Lemma fresh_lemma_3 : forall C C' a t,
      sub_context C C' -> C |- a # t -> C' |- a # t. 
Proof.
  intros. unfold sub_context in H.
  induction t.
  apply fresh_Ut.
  apply fresh_At_elim in H0. apply fresh_At; trivial.
  apply fresh_Ab_elim in H0. destruct H0.
   rewrite H0. apply fresh_Ab_1.
   destruct H0. apply fresh_Ab_2; trivial.
   apply IHt; trivial.
  apply fresh_Pr_elim in H0. destruct H0.
  apply fresh_Pr.
   apply IHt1; trivial.
   apply IHt2; trivial.  
  apply fresh_Fc_elim in H0.
  apply fresh_Fc. apply IHt; trivial. 
  apply fresh_Su_elim in H0.
  apply fresh_Su. apply H; trivial.
Qed.  


Require Import Omega.

(** About freshness, TPith and TPithdel *)
 
Lemma fresh_TPith_TPithdel : forall i a C t E n, 
 C |- a # t <-> (C |- a # TPith i t E n /\ C |- a # TPithdel i t E n).  
Proof.
 intros. gen i. induction t; intro.
 simpl; split~; auto. simpl; split~; intro H; try split~; auto; try apply H.
 simpl; split~; intro H; try split~; auto; try apply H.
 case (le_dec i (TPlength t1 E n)); intro H0.
 rewrite TPith_Pr_le; trivial. case (nat_eqdec (TPlength t1 E n) 1); intro H1.
 rewrite TPithdel_t1_Pr; trivial. split~; intro. apply fresh_Pr_elim in H.
 split~; try apply H. apply IHt1; apply H.
 apply fresh_Pr; try apply H. apply IHt1 with (i:=i); split~; try apply H.
 rewrite TPithdel_TPlength_1; trivial.
 rewrite TPithdel_Pr_le; trivial. split~; intro. apply fresh_Pr_elim in H.
 split~; [apply IHt1; apply H | apply fresh_Pr; [apply IHt1; apply H | apply H]].
 destruct H. apply fresh_Pr_elim in H2. destruct H2. apply fresh_Pr; trivial.
 apply IHt1 with (i:=i); split~; trivial.
 rewrite TPith_Pr_gt; try omega. case (eq_nat_dec (TPlength t2 E n) 1); intro H1.
 rewrite TPithdel_t2_Pr; try omega. split~; intro. apply fresh_Pr_elim in H.
 split~; try apply H. apply IHt2; apply H. apply fresh_Pr; try apply H.
 apply IHt2 with (i:=i - TPlength t1 E n); split~; try apply H.
 rewrite TPithdel_TPlength_1; trivial.
 rewrite TPithdel_Pr_gt; try omega. split~; intro. apply fresh_Pr_elim in H.
 split~; [apply IHt2; apply H | apply fresh_Pr; [apply H |apply IHt2; apply H]].
 destruct H. apply fresh_Pr_elim in H2. destruct H2. apply fresh_Pr; trivial.
 apply IHt2 with (i:=i-TPlength t1 E n); split~; trivial. 
 split~; intro. apply fresh_Fc_elim in H.
 case (nat_pair_eqdec (n0,n1) (E,n)); intro H0.
 inverts H0. autorewrite with tuples. case (eq_nat_dec (TPlength t E n) 1); intro H0.
 rewrite TPithdel_TPlength_1; autorewrite with tuples; trivial. split~; auto.
 apply IHt; trivial. rewrite TPithdel_Fc_eq; trivial.
 split~; try apply fresh_Fc; apply IHt; trivial.
 rewrite TPith_Fc_diff; trivial. rewrite TPithdel_Fc_diff; trivial. split~; auto.
 apply fresh_Fc. destruct H. case (nat_pair_eqdec (n0,n1) (E,n)); intro H1.
 inverts H1. autorewrite with tuples in H. apply IHt with (i:=i); split~; trivial.
 case (eq_nat_dec (TPlength t E n) 1); intro H1.
 rewrite TPithdel_TPlength_1; autorewrite with tuples; trivial.
 rewrite TPithdel_Fc_eq in H0; trivial. apply fresh_Fc_elim in H0; trivial.
 rewrite TPith_Fc_diff in H; trivial. apply fresh_Fc_elim in H; trivial.
 simpl; split~; intro H; try split~; auto; try apply H.
Qed.


(* About rpl_super and freshness *)

Lemma fresh_rpl_super : forall C a S0 m t, C |- a # t <-> C |- a # rpl_super S0 m t.
Proof.
  intros. induction t; simpl; split~; intro;  auto.
  apply fresh_Ab_elim in H. destruct H. rewrite H. apply fresh_Ab_1.
  destruct H. apply fresh_Ab_2; trivial. apply IHt; trivial.
  apply fresh_Ab_elim in H. destruct H. rewrite H. apply fresh_Ab_1.
  destruct H. apply fresh_Ab_2; trivial. apply IHt; trivial.
  apply fresh_Pr_elim in H. destruct H. apply fresh_Pr; [apply IHt1 | apply IHt2]; trivial.
  apply fresh_Pr_elim in H. destruct H. apply fresh_Pr; [apply IHt1 | apply IHt2]; trivial.
  apply fresh_Fc_elim in H. case (set_In_dec nat_eqdec n S0); intro H1;
  apply fresh_Fc; apply IHt; trivial.
  gen H. case (set_In_dec nat_eqdec n S0); intros H H1;
  apply fresh_Fc_elim in H1; apply fresh_Fc; apply IHt; trivial.
Qed.



