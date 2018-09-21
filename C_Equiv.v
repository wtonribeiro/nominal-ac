(**
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : C_Equiv.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
Description : This file contains specific results about alpha-equivalence
              modulo commutativity 

 Last Modified On: Sep 17, 2018.
 ============================================================================
*)

Require Export AACC_Equiv.

(** Inversion lemmas over c\_equiv *)

Lemma c_equiv_At_elim : forall C a a', C |- (%a) ~c (%a') -> a = a'.
Proof. intros. inverts H; trivial. Qed.

Lemma c_equiv_Pr_elim : forall C t1 t2 t1' t2', 
C |- (<|t1,t2|>) ~c (<|t1',t2'|>) -> ((C |- t1 ~c t1') /\ (C |- t2 ~c t2')).  
Proof. intros. inverts H; try split~. Qed.

Lemma c_equiv_Fc_elim : forall C E E' n n' t t',
((~set_In E (0::1::|[2]|)) \/ (E = 2 /\ ((~ is_Pr t) \/ (~ is_Pr t')))) ->                           
C |- Fc E n t ~c Fc E' n' t' -> (E = E' /\ n = n' /\ C |- t ~c t').  
Proof. 
 intros. inverts H0. repeat split~.
 simpl in H6. omega.  simpl in H6. omega.
 false. destruct H. apply H. simpl. right~.
 destruct H. simpl in H0. destruct H0; apply H0; trivial.
 false. destruct H. apply H. simpl. right~.
 destruct H.
 destruct H. simpl in H0. destruct H0; apply H; trivial. 
Qed.

Lemma c_equiv_Fc_c_elim : forall C n n' s1 s2 t1 t2,
 C |- Fc 2 n (<|s1,s2|>) ~c Fc 2 n' (<|t1,t2|>) ->
      (n = n' /\ ((C |- s1 ~c t1 /\ C |- s2 ~c t2) \/
                  (C |- s1 ~c t2 /\ C |- s2 ~c t1))).  
Proof.
  intros. inverts H.
  false. destruct H3. simpl in H. omega.
  destruct H. simpl in H0. destruct H0; apply H0; trivial.
  split~. split~.
Qed.
  
Lemma c_equiv_Ab_elim : forall C t t' a a', 
C |- [a]^t ~c ([a']^t') -> 
((a = a' /\ C |- t ~c t') \/ 
(a <> a' /\ ((C |- t ~c (|[(a,a')]| @ t')) /\ C |- a # t'))). 
Proof.
  intros. inverts H. left~. right~. 
Qed.

Lemma c_equiv_Su_elim : forall C p p' X,
C |- Su p X ~c Su p' X -> (forall a, (In_ds p p' a) -> set_In ((a,X)) C).
Proof. intros. inverts H. apply H3; trivial. Qed.

Hint Resolve c_equiv_At_elim.
Hint Resolve c_equiv_Pr_elim.
Hint Resolve c_equiv_Fc_elim.
Hint Resolve c_equiv_Ab_elim.
Hint Resolve c_equiv_Su_elim.

(** Inversion lemmas Intermediate transitivity for c\_equiv with alpha\_equiv  *)

(** 
     The following lemma is the result that allows to
     transfer some properties from alpha_equiv to
     c_equiv. It is proved by induction in
     C |- t1 ~c t2 with cases analysis over 
     C |- t2 ~alpha t3.  
*)

Lemma c_alpha_equiv_trans : forall C t1 t2 t3, 
  C |- t1 ~c t2 -> C |- t2 ~alpha t3 -> C |- t1 ~c t3.
Proof.
 intros. generalize t3 H0; clear t3 H0. 
 induction H; intros t3 H'; inverts H'; auto.

 apply equiv_Fc.
 destruct H. left~. right~. destruct H. split~.
 destruct H1. left~. right~. apply alpha_neg_is_Pr in H6.
 apply H6; trivial. apply IHequiv; trivial.
  
 apply equiv_Ab_2; trivial. apply IHequiv.
 apply alpha_equiv_equivariance; trivial.
 apply alpha_equiv_fresh with (t1 := t'); trivial.
 case (atom_eqdec a a'0); intro H9. rewrite <- H9.
 apply equiv_Ab_1. apply IHequiv.
 apply perm_inv_side'. simpl. rewrite H9.
 apply ds_empty_equiv_2 with (pi := |[(a', a'0)]|); trivial; intros.
 intro H10. apply H10. apply swap_comm.
 assert (Q : C |- a # t'0).
  apply alpha_equiv_fresh with (t1 := (|[(a',a'0)]|) @ t').
  apply perm_inv_side'. simpl. trivial.
  replace (|[(a', a'0)]|) with (!|[(a', a'0)]|).
  apply fresh_lemma_2. rewrite swap_neither; trivial.
  intro. symmetry in H2. contradiction.
  intro. symmetry in H2. contradiction.
  simpl; trivial.
 apply equiv_Ab_2; trivial. apply IHequiv.
 apply perm_inv_side'.
 apply alpha_equiv_trans with (t2 := (|[(a', a'0)]|) @ t'0); trivial.
 apply alpha_equiv_trans with (t2 := (|[(|[(a,a')]| $ a, |[(a,a')]| $ a'0)]|) @ ((|[(a,a')]|) @ t'0)). 
 rewrite swap_left. rewrite swap_neither; trivial.
 apply alpha_equiv_equivariance.
 apply alpha_equiv_sym.
 apply alpha_equiv_swap_neither; trivial.
 apply alpha_equiv_sym.
 apply alpha_equiv_pi_comm.
 apply equiv_Su; intros.
 apply ds_trans with (pi2:=p') in H0.
 destruct H0; [apply H | apply H4]; trivial.
 
 simpl in H. omega. simpl in H. omega.
 
 inverts H7.
 apply IHequiv1 in H5.
 apply IHequiv2 in H8.
 apply equiv_C1; trivial.

 inverts H7.
 apply IHequiv1 in H8.
 apply IHequiv2 in H5.
 apply equiv_C2; trivial.  
 
Qed.


(** Freshness preservation of c\_equiv *)

(**  
The following lemma is proved by induction in C |- t1 ~c t2.
*)

Lemma c_equiv_fresh : forall C a t1 t2, C |- t1 ~c t2 ->
                                        C |- a # t1 -> C |- a # t2.
Proof.
  intros.

 induction H; trivial.
 apply fresh_Pr_elim in H0. destruct H0.
 apply fresh_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.
 apply fresh_Fc_elim in H0. apply fresh_Fc; apply IHequiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. rewrite H0. apply fresh_Ab_1.
 destruct H0. apply fresh_Ab_2; trivial. apply IHequiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. apply fresh_Ab_2.
 intro. apply H. rewrite <- H0. trivial. rewrite <- H0 in H2. trivial.
 destruct H0. case (atom_eqdec a a'); intros.
 rewrite e. apply fresh_Ab_1. apply fresh_Ab_2; trivial.
 assert (Q : C |- a # ((|[(a0, a')]|) @ t')).  apply IHequiv; trivial.
 apply fresh_lemma_1 in Q. simpl rev in Q. rewrite swap_neither in Q; trivial.
 intro. apply H0. rewrite H4; trivial. intro. apply n. rewrite H4; trivial.
 apply fresh_Su. apply fresh_Su_elim in H0.
 case (atom_eqdec ((!p) $ a) ((!p') $ a)); intros. rewrite <- e; trivial.
 apply H; intros. intro. apply n. gen_eq g : (!p'); intro. 
 replace p' with (!g) in H1. rewrite perm_inv_atom in H1. 
 replace ((!p) $ a) with ((!p) $ (p $ (g $ a))). rewrite perm_inv_atom. trivial.
 rewrite H1. trivial. rewrite H2. rewrite rev_involutive. trivial.

 simpl in H. omega. simpl in H. omega.

 apply fresh_Fc_elim in H0.
 apply fresh_Pr_elim in H0. destruct H0. apply fresh_Fc.
 apply fresh_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.

 apply fresh_Fc_elim in H0.
 apply fresh_Pr_elim in H0. destruct H0. apply fresh_Fc.
 apply fresh_Pr; [apply IHequiv2 | apply IHequiv1]; trivial.
 
Qed.


(** Equivariance of c\_equiv *)

(**  
The following lemma is also proved by induction in C |- t1 ~c t2, and it 
uses lemma c_alpha_equiv_trans.
*)


Lemma c_equiv_equivariance : forall C t1 t2 pi,  
 C |- t1 ~c t2 -> C |- (pi @ t1) ~c (pi @ t2).
Proof.
 intros. induction H; simpl; auto.
 apply equiv_Fc; trivial.
 destruct H. left~. right~. destruct H.
 split~. destruct H1; [left~ | right~]; apply perm_neg_is_Pr; trivial.
 apply equiv_Ab_2. apply perm_diff_atom; trivial.
 apply c_alpha_equiv_trans with (t2 := (pi @ ((|[(a, a')]|) @ t'))).
 apply IHequiv. apply alpha_equiv_pi_comm. apply fresh_lemma_3; trivial.
 apply equiv_Su. intros. apply H.
 apply ds_cancel in H0; trivial.
 simpl in H. omega. simpl in H. omega.
Qed.


(** Equivalence of c\_equiv *)

(**  
The equivalence of c_equiv is proved as corollary of 
the equivalence of aacc_equiv. The prove of the latter 
lemma is the file Equiv.v .
 *)



Lemma c_equiv_refl : forall C t, C |- t ~c t.
Proof.
  intros. apply c_equivalence.
Qed.

Lemma c_equiv_sym : forall C t1 t2, C |- t1 ~c t2 -> C |- t2 ~c t1.
Proof.
  intros C t1 t2. apply c_equivalence.
Qed.

Lemma c_equiv_trans : forall C t1 t2 t3,
                      C |- t1 ~c t2 -> C |- t2 ~c t3 -> C |- t1 ~c t3.
Proof.
  intros C t1 t2 t3. apply c_equivalence.
Qed.


(** Some other basic properties of c\_equiv. *)


(** Invariance of terms under c_equiv and the action of permutations.
This property is inherited from alpha_equiv, and it is proved using   
c_equiv *)

Lemma c_equiv_pi : forall C t pi pi', 
                   (forall a, (In_ds pi pi' a) -> (C |- a # t)) -> C |- pi @ t ~c (pi' @ t).
Proof.
  intros.
  apply c_alpha_equiv_trans with (t2:= pi @ t). 
  apply c_equiv_refl.
  apply alpha_equiv_pi; trivial.
Qed.

(**
Size of terms is preserved by c_equiv.
*)

Lemma c_equiv_term_size : forall C s t, C |- s ~c t -> term_size s = term_size t.
Proof.
  intros. induction H; simpl; try omega.
  rewrite perm_term_size in IHequiv. omega.
  simpl in H. omega. simpl in H. omega.
Qed.

(**
If C |- s ~c t then s is not a proper subterm of t.
*)


Lemma c_equiv_psubterm : forall C s t, C |- s ~c t -> ~ set_In s (psubterms t).
Proof.
  intros. intro H'.
  apply c_equiv_term_size in H.
  apply psubterms_term_size_lt in H'.
  omega.
Qed.

(**
If C |- s ~c t then (pi @ s) is not a proper subterm of t.
*)


Lemma c_equiv_perm_psubterm : forall C pi s t, C |- s ~c t -> ~ set_In (pi @ s) (psubterms t).
Proof.
  intros. intro H'.
  apply c_equiv_term_size in H.
  apply psubterms_term_size_lt in H'.
  rewrite perm_term_size in H'.
  omega.
Qed.


(**
Is possible to change the side of a permutation in c_equiv.
*)


Lemma c_equiv_pi_inv_side : forall C pi t1 t2,
 C |- pi @ t1 ~c t2 <-> C |- t1 ~c ((!pi) @ t2).
Proof.
  intros. split~; intro.
  apply c_equiv_equivariance with (pi:=!pi) in H.
  apply c_equiv_trans with (t2:= (! pi) @ (pi @ t1)); trivial. 
  apply c_alpha_equiv_trans with (t2:=t1). 
  apply c_equiv_refl. apply perm_inv_side.
  apply alpha_equiv_refl.
  apply c_equiv_equivariance with (pi:=pi) in H.
  apply c_alpha_equiv_trans with (t2:= pi @ ((! pi) @ t2)); trivial. 
  apply perm_inv_side'.
  apply alpha_equiv_refl.  
Qed.
