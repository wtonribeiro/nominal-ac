(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Disagr.v
 Authors     : Washington Luis R. de Carvalho Segundo and
               Mauricio Ayala Rincon 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 3, 2017.
 ============================================================================
*)

Require Import Morphisms.
Require Export Perm.


(** Disagreement set *)

Definition In_ds (p0 p1 : Perm) (a : Atom) := p0 $ a <> p1 $ a.

(** Lemmas *)

Lemma In_ds_dec : forall pi pi' a, 
                  (In_ds pi pi' a) \/ ~ (In_ds pi pi' a).  
Proof.
 intros. case ((pi $ a) ==at (pi' $ a)); intro H.
 right~. left~. 
Qed.

Lemma not_In_ds : forall pi pi' a, 
                  (~ In_ds pi pi' a) <-> pi $ a = pi' $ a. 
Proof.
  split~; intros.
  case ((pi $ a) ==at (pi' $ a)); intro; trivial.
  false. apply H. unfold In_ds. trivial.
Qed.

Lemma not_In_ds_inv : forall pi pi' b, 
                      (forall a, ~ In_ds pi pi' a) -> (!pi) $ b = (!pi') $ b. 
Proof.
  intros.
  assert (Q : pi $ ((! pi) $ b) = pi' $ ((!pi) $ b)).
  apply not_In_ds. apply H.
  gen_eq g : (!pi); intro H0.
  replace pi with (!g) in Q.
  rewrite perm_inv_atom in Q.
  symmetry in Q. apply perm_inv_side_atom in Q. trivial.
  rewrite H0. rewrite rev_involutive. trivial.
Qed.


Lemma ds_elem : forall a pi, pi $ a <> a <-> In_ds ([]) pi a.
Proof. split~; intros.
 intro. apply H. simpl in H0. rewrite <- H0; trivial.
Qed.

Lemma ds_sym : forall a pi pi', In_ds pi pi' a <-> In_ds pi' pi a.
Proof.
 intros; split~; intro; intro; apply H; symmetry; trivial.
Qed.

Lemma ds_trans : forall a pi1 pi2 pi3, 
In_ds pi1 pi3 a -> (In_ds pi1 pi2 a \/ In_ds pi2 pi3 a).
Proof.
 intros. case (In_ds_dec pi1 pi2 a); intros. left~; trivial.
 case (In_ds_dec pi2 pi3 a); intros. right~; trivial.
 apply not_In_ds in H0. apply not_In_ds in H1.
 rewrite H1 in H0. contradiction.
Qed.

Lemma ds_cancel : forall pi pi1 pi2 a, 
In_ds (pi1 ++ pi) (pi2 ++ pi) a <-> In_ds pi1 pi2 a.
Proof. split~; intros.
 intro. apply H. rewrite <- 2 perm_comp_atom. 
 rewrite H0; trivial.
 intro. apply H. rewrite <- 2 perm_comp_atom in H0.
 apply perm_eq_atom in H0; trivial.
Qed.

Lemma ds_cancel2 : forall pi pi1 pi2 a, 
In_ds (pi ++ pi1) (pi ++ pi2) a <-> In_ds pi1 pi2 (pi $ a).
Proof.
  intros.  split~; intros.
  intro. apply H. rewrite <- 2 perm_comp_atom; trivial. 
  intro. apply H. rewrite <- 2 perm_comp_atom in H0.
  trivial.
Qed.

Lemma ds_cancel3 : forall pi pi', 
  (forall a, ~ In_ds (pi ++ pi' ++ !pi) ([]) a) ->
  (forall b, ~ In_ds pi' ([]) b).
Proof.
  intros. intro. apply H0. simpl. clear H0.
  setoid_rewrite not_In_ds in H. simpl in H.
  setoid_rewrite <- perm_comp_atom in H.
  setoid_rewrite <- perm_comp_atom in H.
  setoid_rewrite perm_inv_side_atom in H.  
  setoid_rewrite perm_inv_inv_atom in H.
  assert (Q: pi' $ (pi $ (!pi $ b)) = pi $ (!pi $ b)).
   apply H.
  replace (pi $ ((! pi) $ b)) with b in Q; trivial.
  gen_eq pi'' : (! pi); intro Q'.
  replace pi with (!pi''). rewrite perm_inv_atom; trivial.
  rewrite Q'. rewrite rev_involutive.
  trivial.
Qed.
  
Lemma h_ds_cancel : forall s a pi pi', 
~ In_ds ([]) ([s]) a -> In_ds (s::pi) pi' a -> In_ds pi pi' a.
Proof.
 intros. apply not_In_ds in H. intro. apply H0.
 rewrite swap_app_atom. rewrite swap_app_atom in H.
 rewrite 2 perm_id_atom in H. rewrite <- H; trivial.
Qed.

Lemma ds_rev_pi_pi : forall a pi1 pi2, 
In_ds (pi1++!pi1) pi2 a <-> In_ds ([]) pi2 a.
Proof.
 intros; unfold In_ds; split~;    
 rewrite <- perm_comp_atom; rewrite perm_inv_atom;
 simpl; trivial.
Qed. 

Lemma ds_rev : forall a pi1 pi2,
In_ds ([]) (pi2++!pi1) a <-> In_ds pi1 pi2 a.
Proof.
 intros; unfold In_ds; rewrite <- perm_comp_atom; simpl;
 split~; intros; intro; apply H; clear H; 
 apply perm_inv_side_atom; trivial.
Qed.


Lemma ds_inv : forall pi a, 
In_ds pi ([]) a -> In_ds (!pi) ([]) a. 
Proof.
  intros. apply ds_rev.
  simpl. rewrite rev_involutive.
  apply ds_sym. trivial.
Qed.

Lemma ds_perm_left : forall a b pi1 pi2, 
In_ds (pi1) (pi2 ++ [(pi1 $ b, pi2 $ b)]) a -> In_ds pi1 pi2 a .
Proof. 
 intros. intro. apply H. clear H. rewrite <- perm_comp_atom.  
 simpl in *|-*. case ((pi1 $ b) ==at (pi2 $ a)); intros; trivial.
 rewrite <- e in H0. apply perm_eq_atom in H0. rewrite H0 in e.
 rewrite H0; trivial. case ((pi2 $ b) ==at (pi2 $ a)); trivial; intros.
 apply perm_eq_atom. apply perm_eq_atom in e. rewrite e; trivial.
Qed.

Lemma ds_perm_right : forall a b pi1 pi2, 
a <> b -> pi1 $ b <> pi2 $ a -> 
In_ds pi1 pi2 a -> In_ds (pi1) (pi2 ++ [(pi1 $ b, pi2 $ b)]) a .
Proof. 
 intros. unfold In_ds in *|-*. rewrite <- perm_comp_atom. simpl. 
 case ((pi1 $ b) ==at (pi2 $ a)); intros; try contradiction.
 case ((pi2 $ b) ==at (pi2 $ a)); intros; trivial.
 apply perm_eq_atom in e. symmetry in e. contradiction.
Qed.

Lemma equiv_pi_atom : forall pi pi' a, 
                 (forall a', ((In_ds pi pi') a') -> a' <> a) <->
                  pi $ a = pi' $ a.
Proof. 
 split~; intros. 
 apply not_In_ds. intro. case (H a); trivial. 
 unfold In_ds in H0. intro. rewrite H1 in H0. contradiction.
Qed.




