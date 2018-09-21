(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Disagr.v
 Authors     : Washington Luis R. de Carvalho Segundo and
               Mauricio Ayala Rincon 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation

 Description : This file contains the definition of the disagreements set,   
               also called the differences set, ds(\pi, \pi'), and some
               results about this definition.
 
 Last Modified On: Mar 26, 2018.
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
 intros. case (atom_eqdec (pi $ a) (pi' $ a)); intro H.
 right~. left~. 
Qed.

Lemma not_In_ds : forall pi pi' a, 
                  (~ In_ds pi pi' a) <-> pi $ a = pi' $ a. 
Proof.
  split~; intros.
  case (atom_eqdec (pi $ a) (pi' $ a)); intro; trivial.
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
~ In_ds ([]) (|[s]|) a -> In_ds (s::pi) pi' a -> In_ds pi pi' a.
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
In_ds (pi1) (pi2 ++ |[(pi1 $ b, pi2 $ b)]|) a -> In_ds pi1 pi2 a .
Proof. 
 intros. intro. apply H. clear H. rewrite <- perm_comp_atom.  
 simpl in *|-*. case (atom_eqdec (pi1 $ b) (pi2 $ a)); intros; trivial.
 rewrite <- e in H0. apply perm_eq_atom in H0. rewrite H0 in e.
 rewrite H0; trivial. case (atom_eqdec (pi2 $ b) (pi2 $ a)); trivial; intros.
 apply perm_eq_atom. apply perm_eq_atom in e. rewrite e; trivial.
Qed.

Lemma ds_perm_right : forall a b pi1 pi2, 
a <> b -> pi1 $ b <> pi2 $ a -> 
In_ds pi1 pi2 a -> In_ds (pi1) (pi2 ++ |[(pi1 $ b, pi2 $ b)]|) a .
Proof. 
 intros. unfold In_ds in *|-*. rewrite <- perm_comp_atom. simpl. 
 case (atom_eqdec (pi1 $ b) (pi2 $ a)); intros; try contradiction.
 case (atom_eqdec (pi2 $ b) (pi2 $ a)); intros; trivial.
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



(** The disagrement (differences) set as a recursive function *)

Fixpoint atom_in_set (a : Atom) (S : set Atom) : bool :=
  match S with 
    | [] => false
    | a0 :: S0 => if atom_eqdec a a0
                  then true
                  else atom_in_set a S0
  end.


Fixpoint atoms_perm (pi : Perm) : set Atom :=
  match pi with
    | [] => []
    | (a, b) :: pi0 => set_add atom_eqdec a (set_add atom_eqdec b (atoms_perm pi0))
  end .                                  


Fixpoint dom_perm_aux (pi : Perm) (S : set Atom) : set Atom :=
  match S with
     | [] => []
     | a :: S0 => if atom_eqdec a (pi $ a)
                  then dom_perm_aux pi S0
                  else set_add atom_eqdec a (dom_perm_aux pi S0)
  end.

Definition dom_perm (pi : Perm) : set Atom :=
  dom_perm_aux pi (atoms_perm pi).


Definition disgr (pi pi': Perm) : set Atom :=
  dom_perm (pi++(!pi')).


(** Equivalence between ds and disgr *)

Lemma ds_to_atoms_perm : forall a pi, In_ds ([]) pi a -> set_In a (atoms_perm pi).
Proof.
  intros. unfold In_ds in H.
  induction pi; simpl in *|-*. apply H; trivial.
  destruct a0. gen H.
  case (atom_eqdec a0 a); intros H H0.
  apply set_add_intro2. symmetry. trivial.
  gen H0. case (atom_eqdec a1 a); intros H0 H1.
  apply set_add_intro1.
  apply set_add_intro2. symmetry; trivial.
  apply IHpi in H1.
  apply set_add_intro1.
  apply set_add_intro1; trivial.
Qed.  

Lemma ds_to_dom_perm_aux : forall a pi A, In_ds ([]) pi a ->
                                          set_In a A ->
                                          set_In a (dom_perm_aux pi A).
Proof.
  intros. unfold In_ds in H. simpl in H.
  gen pi a. induction A; intros.
  simpl in H0. contradiction.
  simpl in *|-*. case (atom_eqdec a (pi $ a)); intro H1.
  destruct H0. rewrite H0 in H1; contradiction.
  apply IHA; trivial.
  destruct H0. apply set_add_intro2.
  symmetry. trivial.
  apply set_add_intro1.
  apply IHA; trivial.
Qed.

Lemma dom_perm_aux_to_In_ds : forall a pi A, set_In a (dom_perm_aux pi A) ->
                                             In_ds ([]) pi a.
Proof.
  intros. unfold In_ds.
  simpl. gen a pi.
  induction A; intros; simpl in *|-*.
  contradiction.
  gen H. case (atom_eqdec a (pi $ a)); intros.
  apply IHA; trivial.
  apply set_add_elim in H. destruct H.
  rewrite H; trivial. apply IHA; trivial.
Qed.  
  
Lemma ds_eq_disgr : forall a pi pi', In_ds pi pi' a <-> set_In a (disgr pi pi'). 
Proof.
  intros.
  rewrite ds_sym. rewrite <- ds_rev.
  unfold disgr. unfold dom_perm.
  split~; intros.
  apply ds_to_dom_perm_aux; trivial.
  apply ds_to_atoms_perm; trivial.
  apply dom_perm_aux_to_In_ds in H; trivial.
Qed.  


Lemma In_dom_perm : forall a pi, set_In a (dom_perm pi) -> exists b, pi $ a = b /\ set_In b (dom_perm pi).
Proof.
  intros. replace (dom_perm pi) with (disgr pi ([])) in *|-*.
  apply ds_eq_disgr in H. exists (pi $ a).
  split~. apply ds_eq_disgr.
  unfold In_ds in *|-*. simpl in *|-*.
  apply perm_diff_atom; trivial.
  unfold disgr. simpl. rewrite app_nil_r; trivial.
Qed.

Lemma dom_perm_inv : forall a pi, set_In a (dom_perm pi) <-> set_In a (dom_perm (!pi)). 
Proof.
  intros.
  replace (dom_perm pi) with (disgr pi ([])).
  replace (dom_perm (!pi)) with (disgr (!pi) ([])).  
  rewrite <- 2 ds_eq_disgr. split~; intro.
  apply ds_sym. replace (!pi) with (([])++(!pi)).
  apply ds_rev; trivial. simpl; trivial.
  apply ds_sym in H. replace (!pi) with (([])++(!pi)) in H.
  rewrite ds_rev in H; trivial. simpl; trivial.
  unfold disgr. simpl. rewrite app_nil_r; trivial.
  unfold disgr. simpl. rewrite app_nil_r; trivial.
Qed.
  
  
Lemma In_dom_perm' :  forall a pi, set_In a (dom_perm pi) -> exists b, (!pi) $ a = b /\ set_In b (dom_perm pi).
Proof.
  intros. setoid_rewrite dom_perm_inv.
  rewrite dom_perm_inv in H.
  apply In_dom_perm; trivial.
Qed.  



Fixpoint fresh_context (S : set Atom) (X : Var) :=
  match S with
    | [] => []
    | a :: S0 => (a, X) :: fresh_context S0 X
  end.

Definition sub_context (C0 C1 : Context) :=
  forall c, set_In c C0 -> set_In c C1.


Fixpoint sub_context_rec (C C' : Context) : bool :=
  match C with
  | [] => true
  | c :: C0 => if in_context_dec c C'
               then sub_context_rec C0 C'
               else false                 
  end.


Lemma sub_context_rec_correctness : forall C C',

       sub_context C C' <->
     
       sub_context_rec C C' = true .

Proof.
  intros. unfold sub_context.
  gen C'. induction C; intros.
  split~; intros. simpl in H0. contradiction.
  simpl. split~; intro H.
  case (in_context_dec a C'); intro H0.
  apply IHC; intros. apply H. right~.
  assert (Q : In a C'). apply H. left~. contradiction.
  intros. gen H.
  case (in_context_dec a C'); intros H2 H1.
  destruct H0. rewrite H in H2. trivial.
  apply IHC; trivial.
  inverts H1.
Qed.


Lemma fresh_context_mem : forall a X Y St,
      set_In (a, Y) (fresh_context St X) <->
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