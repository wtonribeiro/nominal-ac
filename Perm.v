(*
 ============================================================================
 Project     : Nominal A, AC and C Equivalence
 File        : Perm.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation

 Description : This file contains the definition of action of 
               permutations and some results about.
 
 Last Modified On: Jul 25, 2018.
 ============================================================================
*)

Require Export Terms.

(** Swapping of atoms *)

Definition swapa (s : Atom * Atom) (c : Atom) :=
  let     (a, b)     :=  s in
  if      (atom_eqdec a c) then b
  else if (atom_eqdec b c) then a
  else c.

(** Permutation action  *)

Fixpoint p_act_aux (p : Perm) (c : Atom) {struct p} : Atom :=
match p with 
  | nil       => c
  | (a,b)::p0 => p_act_aux p0 (swapa (a,b) c)
end.
Notation "p $ a" := (p_act_aux p a) (at level 67).

Fixpoint perm_act (pi : Perm) (t : term) : term :=
 match t with
  | <<>>  => <<>>
  | %a    => %(pi $ a)
  | [a]^s => [pi $ a]^(perm_act pi s)
  | <|u, v|> => <|perm_act pi u, perm_act pi v|> 
  | Fc E n s => Fc E n (perm_act pi s)
  | pi'|.X    => (pi'++pi)|.X  
 end.

Notation "p @ t" := (perm_act p t) (at level 67).  
Notation "! p"   := (rev p) (at level 67).
            

(** Lemmas *)

(**  Swap action *) 

Lemma swap_app_atom : forall s a p, (s :: p) $ a = p $ (|[s]| $ a).
Proof. intros. destruct s. simpl. trivial. Qed.

Lemma swap_comm : forall (a b c : Atom), |[(a, b)]| $ c = |[(b, a)]| $ c.
Proof.
 intros. simpl.
 case (atom_eqdec a c); intros; case (atom_eqdec b c); intros; trivial.  
 rewrite e. rewrite e0. trivial. 
Qed. 

Lemma swap_eq_swapa : forall s a, |[s]| $ a = swapa s a .
Proof. intros. destruct s. simpl. trivial. Qed.

Lemma swap_left : forall a b, |[(a,b)]| $ a = b.
Proof. 
 intros. simpl. case (atom_eqdec a a); intros; trivial.
 apply False_ind. apply n; trivial.
Qed.

Hint Rewrite swap_left : perm.

Lemma swap_left' : forall a b c, a = c -> |[(a,b)]| $ c = b.
Proof. intros. rewrite H. rewrite swap_left; trivial. Qed.

Lemma swap_right : forall a b, |[(a,b)]| $ b = a.
Proof. 
 intros. simpl. case (atom_eqdec a b); intros. rewrite e; trivial.  
 case (atom_eqdec b b); intros; trivial. apply False_ind. apply n0; trivial. 
Qed.

Hint Rewrite swap_right : perm.

Lemma swap_right' : forall a b c, b = c -> |[(a,b)]| $ c = a.
Proof. intros. rewrite H. rewrite swap_right; trivial. Qed.

Lemma swap_neither : forall a b c, a <> c -> b <> c -> |[(a,b)]| $ c = c.
Proof. 
 intros. simpl. 
 case (atom_eqdec a c); case (atom_eqdec b c); intros; 
 try contradiction; trivial. 
Qed.

Lemma swap_same : forall a b, |[(a,a)]| $ b = b.
Proof. intros. simpl. case (atom_eqdec a b); case (atom_eqdec a b); intros; trivial. Qed.

Hint Rewrite  swap_same : perm.

Lemma swap_invol : forall s c, |[s]| $ (|[s]| $ c) = c. 
Proof. 
 intros. destruct s. 
 case (atom_eqdec a c); intros. 
 rewrite e. rewrite swap_left. rewrite swap_right; trivial.
 case (atom_eqdec a0 c); intros. 
 rewrite e. rewrite swap_right. rewrite swap_left; trivial.
 rewrite 2 swap_neither with (c := c); trivial.
Qed.

Hint Rewrite swap_invol : perm.


(** Permutations *) 

(** Basic identities *)

Lemma perm_id_atom : forall a, [] $ a = a.
Proof. simpl. trivial. Qed. 

Lemma perm_id : forall t, [] @ t = t.
Proof.
  intros. induction t; simpl; trivial.
  rewrite IHt; trivial.
  rewrite IHt1. rewrite IHt2; trivial.
  rewrite IHt; trivial.
  rewrite app_nil_r. trivial.
Qed.       

Hint Rewrite perm_id_atom : perm.
Hint Rewrite perm_id : perm.


(** Permutations over atoms *)

Lemma swap_app : forall s t p, (s::p) @ t = p @ (|[s]| @ t).
Proof.
 intros. induction t; simpl; 
 try destruct s; simpl; trivial.
 rewrite IHt; trivial. rewrite IHt1. rewrite IHt2; trivial.
 rewrite IHt; trivial. rewrite <- app_assoc; simpl; trivial.
Qed. 


Lemma swap_empty : forall pi X t, pi @ t = Su ([]) X -> pi = [].
Proof.
 intros pi X t. 
 destruct t; simpl; intro H; inversion H.
 destruct pi. rewrite H1; trivial. apply False_ind.
 symmetry in H1. generalize H1. apply app_cons_not_nil.
Qed.


Lemma perm_comp_atom : forall p0 p1 a, p1 $ (p0 $ a) = (p0++p1) $ a.
Proof.
 intros p0 p1. induction p0; intros.
 simpl. trivial.
 rewrite swap_app_atom. rewrite IHp0.
 rewrite <- app_comm_cons. 
 rewrite swap_app_atom with (p := p0++p1).
 trivial.
Qed.


Lemma perm_inv_atom : forall p a, (!p) $ (p $ a) = a.
Proof.
 intro p. induction p; intros.
 simpl. trivial. 
 simpl rev. rewrite <- perm_comp_atom. 
 rewrite swap_app_atom with (s := a) (a := a0).
 rewrite IHp. rewrite swap_app_atom.  
 rewrite swap_invol. simpl; trivial.
Qed.

Hint Rewrite perm_inv_atom : perm.

Lemma perm_inv_side_atom : forall p a b, (p $ a) = b <-> a = (!p $ b).
Proof.
 intros. destruct p.
 split~; simpl; trivial.
 split~; intros. 
 rewrite <- H. rewrite perm_inv_atom. trivial.
 rewrite H. gen_eq g : (!p::p0). intro H'.
 assert (Q : p::p0 = !g). rewrite H'. rewrite rev_involutive. trivial.
 rewrite Q. rewrite perm_inv_atom. trivial.
Qed.

Lemma perm_inv_inv_atom : forall p a, (!(!p)) $ a = p $ a.
Proof. intros. rewrite rev_involutive. trivial. Qed.

Hint Rewrite perm_inv_inv_atom : perm.

Lemma perm_diff_atom : forall p a a', a <> a' <-> p $ a <> p $ a'.
Proof.
 split~; intros; intro H'; apply H.
 apply perm_inv_side_atom in H'.
 rewrite perm_inv_atom in H'. trivial.
 rewrite H'. trivial.
Qed.

Lemma perm_eq_atom : forall p a a', a = a' <-> p $ a = p $ a'.
Proof.
 split~; intros. rewrite H. trivial.
 case (atom_eqdec a a'); intros; trivial.
 apply perm_diff_atom with (p := p) in n.
 contradiction.
Qed.

Lemma pi_comm_atom : forall a b pi c,
 pi $ (|[(a,b)]| $ c) = |[(pi $ a, pi $ b)]| $ (pi $ c).  
Proof.
 intros. simpl.
 case (atom_eqdec a c); case (atom_eqdec (pi $ a) (pi $ c)); 
 intros; trivial. apply perm_diff_atom in n. contradiction.
 apply perm_eq_atom in e. contradiction.
 case (atom_eqdec b c); case (atom_eqdec (pi $ b) (pi $ c)); 
 intros; trivial. apply perm_diff_atom in n1. contradiction.
 apply perm_eq_atom in e. contradiction.
Qed. 


(** Permutations over terms *)

Lemma perm_comp : forall p0 p1 t, p1 @ (p0 @ t) = (p0++p1) @ t.
Proof.
 intros. generalize t; clear t. induction p0; intros.
 rewrite perm_id. simpl. trivial.
 simpl. rewrite swap_app. 
 rewrite swap_app with (p := p0++p1).
 rewrite IHp0; trivial. 
Qed.

Lemma perm_inv_inv : forall p t, (!(!p)) @ t = p @ t.
Proof. intros. rewrite rev_involutive. trivial. Qed.

Hint Rewrite perm_inv_inv : perm.


(** Permutations does not act over variables *)

Lemma perm_term_vars : forall pi t, term_vars (pi @ t) = term_vars t.
Proof.
  intros. induction t; simpl; trivial.
  rewrite IHt1. rewrite IHt2. trivial.
Defined.

Hint Rewrite perm_term_vars : perm.

(** Permutations does not change the term size *)

Lemma perm_term_size : forall pi t, term_size (pi @ t) = term_size t. 
Proof. 
  intros. induction t; simpl; trivial.
  rewrite IHt; trivial.
  rewrite IHt1. rewrite IHt2; trivial.
  rewrite IHt; trivial.
Defined.
  
Hint Rewrite perm_term_size : perm.


(** Invariance *)

Lemma perm_term_invariance : forall pi s t, s = t <-> pi @ s = pi @ t .
Proof.
  intros. split~; intro H. rewrite H; trivial.
  gen t. induction s; intros t H; destruct t;
   autorewrite with perm in *|-*; trivial; try inverts H.
  apply perm_eq_atom in H1. rewrite H1; trivial.
  apply perm_eq_atom in H1. rewrite H1.
  apply IHs in H2. rewrite H2; trivial.
  apply IHs1 in H1. apply  IHs2 in H2.
  rewrite H1. rewrite H2. trivial.
  apply IHs in H3. rewrite H3. trivial.
  apply app_inv_tail in H1.
  rewrite H1. trivial.
Qed.


(** About pairs and proper terms *) 


Lemma perm_is_Pr : forall pi t, is_Pr t -> is_Pr (pi @ t).
Proof.
  intros. induction t; autorewrite with perm; simpl in *|-*; trivial.
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
