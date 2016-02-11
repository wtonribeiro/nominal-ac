(***************************************************************************
 * Disagr.v                						   *		
***************************************************************************)

Require Import Morphisms.
Require Export Perm.


(** Disagreement set *)

Definition In_ds (p0 p1 : Perm) (a : Atom) := p0 $ a <> p1 $ a.

(** Lemmas *)

Lemma In_ds_dec : forall pi pi' a, 
                  (In_ds pi pi' a) \/ ~ (In_ds pi pi' a).  
Proof.
 intros. case ((pi $ a) ==at (pi' $ a)); intro H.
 right. intro H'. destruct H'. trivial.
 left. unfold In_ds. trivial.
Qed.

Lemma not_In_ds : forall pi pi' a, 
                  (~ In_ds pi pi' a) <-> pi $ a = pi' $ a. 
Proof. split; intros.
 intros. case ((pi $ a) ==at (pi' $ a)).
 intro; trivial. intro H'. apply False_ind.
 apply H. unfold In_ds. trivial.
 intro. unfold In_ds in H0.
 contradiction.
Qed.

Lemma ds_elem : forall a pi, pi $ a <> a <-> In_ds ([]) pi a.
Proof. split; intros.
 intro. apply H. simpl in H0. rewrite <- H0; trivial.
 intro. apply H. simpl. rewrite H0; trivial.
Qed.

Lemma ds_sym : forall a pi pi', In_ds pi pi' a <-> In_ds pi' pi a.
Proof.
 intros; split; intro; intro; apply H; symmetry; trivial.
Qed.

Lemma ds_trans : forall a pi1 pi2 pi3, 
In_ds pi1 pi3 a -> (In_ds pi1 pi2 a \/ In_ds pi2 pi3 a).
Proof.
 intros. case (In_ds_dec pi1 pi2 a); intros. left; trivial.
 case (In_ds_dec pi2 pi3 a); intros. right; trivial.
 apply not_In_ds in H0. apply not_In_ds in H1.
 rewrite H1 in H0. contradiction.
Qed.

Lemma ds_cancel : forall pi pi1 pi2 a, 
In_ds (pi1 ++ pi) (pi2 ++ pi) a <-> In_ds pi1 pi2 a.
Proof. split; intros.
 intro. apply H. rewrite <- 2 perm_comp_atom. 
 rewrite H0; trivial.
 intro. apply H. rewrite <- 2 perm_comp_atom in H0.
 apply perm_eq_atom in H0; trivial.
Qed.

Lemma h_ds_cancel : forall s a pi pi', 
~ In_ds ([]) (|[s]) a -> In_ds (s::pi) pi' a -> In_ds pi pi' a.
Proof.
 intros. apply not_In_ds in H. intro. apply H0.
 rewrite swap_app_atom. rewrite swap_app_atom in H.
 rewrite 2 perm_id_atom in H. rewrite <- H; trivial.
Qed.

Lemma ds_rev_pi_pi : forall a pi1 pi2, 
In_ds (pi1++!pi1) pi2 a <-> In_ds ([]) pi2 a.
Proof.
 intros; unfold In_ds; split;    
 rewrite <- perm_comp_atom; rewrite perm_inv_atom;
 simpl; trivial.
Qed. 

Lemma ds_rev : forall a pi1 pi2,
In_ds ([]) (pi2++!pi1) a <-> In_ds pi1 pi2 a.
Proof.
 intros; unfold In_ds; rewrite <- perm_comp_atom; simpl;
 split; intros; intro; apply H; clear H; 
 apply perm_inv_side_atom; trivial.
Qed.

Lemma ds_perm_left : forall a b pi1 pi2, 
In_ds (pi1) (pi2 ++ |[(pi1 $ b, pi2 $ b)]) a -> In_ds pi1 pi2 a .
Proof. 
 intros. intro. apply H. clear H. rewrite <- perm_comp_atom.  
 simpl in *|-*. case ((pi1 $ b) ==at (pi2 $ a)); intros; trivial.
 rewrite <- e in H0. apply perm_eq_atom in H0. rewrite H0 in e.
 rewrite H0; trivial. case ((pi2 $ b) ==at (pi2 $ a)); trivial; intros.
 apply perm_eq_atom. apply perm_eq_atom in e. rewrite e; trivial.
Qed.

Lemma ds_perm_right : forall a b pi1 pi2, 
a <> b -> pi1 $ b <> pi2 $ a -> 
In_ds pi1 pi2 a -> In_ds (pi1) (pi2 ++ |[(pi1 $ b, pi2 $ b)]) a .
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
 split; intros. 
 apply not_In_ds. intro. case (H a); trivial. 
 unfold In_ds in H0. intro. rewrite H1 in H0. contradiction.
Qed.


Fixpoint flat_perm (pi : Perm) : list Atom :=
match pi with 
 | [] => []
 | (a,b)::pi0 => (a::b::(flat_perm pi0))
end.


Fixpoint mk_ds_set (l : list Atom) (pi : Perm) : set Atom :=
match l with 
| []  => []
| a::l0 => if ((pi $ a) ==at a) then (mk_ds_set l0 pi)
           else set_add Atom_eqdec a (mk_ds_set l0 pi)
end.

Lemma In_ds_to_flat_perm : forall pi a, In_ds pi ([]) a -> In a (flat_perm pi). 
Proof.
 intro pi. induction pi; intros. 
 unfold In_ds in H. simpl in H. apply False_ind. apply H; trivial.
 unfold In_ds in H. simpl in H. destruct a. simpl.
 gen H. case (a ==at a0); intros H0 H. left; trivial.
 gen H. case (a1 ==at a0); intros H1 H. right. left; trivial.
 right. right. apply IHpi. unfold In_ds. simpl. trivial.
Qed.

Lemma mk_ds_set_to_In_ds : forall a l pi, 
set_In a (mk_ds_set l pi) -> In_ds pi ([]) a.  
Proof.
 intros. induction l. simpl in *|-. contradiction.
 simpl in H. gen H. case ((pi $ a0) ==at a0); intros H0 H2.
 apply IHl; trivial. apply set_add_elim in H2. destruct H2.
 unfold In_ds. rewrite H. simpl. trivial.
 apply IHl; trivial.
Qed.

Lemma In_ds_to_mk_ds_set : forall a l pi,
In a l -> In_ds pi ([]) a -> set_In a (mk_ds_set l pi).
Proof.
 intros. induction l. simpl in H. contradiction.
 simpl in H. destruct H. simpl.
 case ((pi $ a0) ==at a0); intro H1. unfold In_ds in H0.
 rewrite H in H1. simpl in H0. contradiction.
 apply set_add_intro2. symmetry. trivial.
 simpl. case (pi $ a0 ==at a0); intro H1. apply IHl; trivial.
 simpl. apply set_add_intro1. apply IHl; trivial.
Qed.

Lemma In_ds_mk_ds_set_eq : forall a pi,
In_ds pi ([]) a <-> set_In a (mk_ds_set (flat_perm pi) pi).
Proof.
 intros. split; intro. 
 apply In_ds_to_mk_ds_set; trivial.
 apply In_ds_to_flat_perm; trivial.
 apply mk_ds_set_to_In_ds with (l:=(flat_perm pi)); trivial. 
Qed.

Definition ds_set (pi1 pi2: Perm) :=
 mk_ds_set (flat_perm (pi1++!pi2)) (pi1++!pi2).


Lemma ds_set_eq : forall a pi1 pi2,
 In_ds pi1 pi2 a <-> set_In a (ds_set pi1 pi2). 
Proof.
 intros. rewrite ds_sym. rewrite <- ds_rev.
 rewrite ds_sym. unfold ds_set. 
 apply In_ds_mk_ds_set_eq.
Qed.



