(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Alpha_Equiv.v
 Authors     : Washington Luis R. de Carvalho Segundo and
               Mauricio Ayala Rincon 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation

 Description : This file contains the definition of alpha-equivalence 
               and its soundness proof.
 
 Last Modified On: Set 17, 2018.
 ============================================================================
*)

Require Export Fresh.

Inductive alpha_equiv : Context -> term -> term -> Prop :=

 | alpha_equiv_Ut   : forall C, alpha_equiv C (<<>>) (<<>>) 

 | alpha_equiv_At   : forall C a, alpha_equiv C (%a) (%a)

 | alpha_equiv_Pr   : forall C t1 t2 t1' t2', (alpha_equiv C t1 t1') -> (alpha_equiv C t2 t2') -> 
                                          alpha_equiv C (<|t1,t2|>) (<|t1',t2'|>)  

 | alpha_equiv_Fc   :  forall m n t t' C, (alpha_equiv C t t') -> 
                              alpha_equiv C (Fc m n t) (Fc m n t')

 | alpha_equiv_Ab_1 : forall C a t t', (alpha_equiv C t t') -> 
                               alpha_equiv C ([a]^t) ([a]^t')

 | alpha_equiv_Ab_2 : forall C a a' t t', 
                a <> a' -> (alpha_equiv C t (|[(a,a')]| @ t')) -> C |- a # t' -> 
                                    alpha_equiv C ([a]^t) ([a']^t')

 | alpha_equiv_Su   : forall (C: Context) p p' (X: Var), 
               (forall a, (In_ds p p' a) -> set_In ((a,X)) C) ->
                            alpha_equiv C (p|.X) (p'|.X) 
.

Hint Constructors alpha_equiv.

Notation "C |- t ~alpha t'" := (alpha_equiv C t t') (at level 67).


(** alpha_equiv intro and elim lemmas *)

Lemma alpha_equiv_At_elim : forall C a a', C |- (%a) ~alpha (%a') -> a = a'.
Proof. intros. inversion H. trivial. Qed.

Lemma alpha_equiv_At_intro : forall C a a', a = a' -> C |- (%a) ~alpha (%a').
Proof. intros. rewrite H. apply alpha_equiv_At. Qed.

Lemma alpha_equiv_Pr_elim : forall C t1 t2 t1' t2', 
C |- (<|t1,t2|>) ~alpha (<|t1',t2'|>) -> ((C |- t1 ~alpha t1') /\ (C |- t2 ~alpha t2')).  
Proof. intros. inversion H. split~; trivial. Qed.

Lemma alpha_equiv_Fc_elim : forall C m0 m1 n0 n1 t t', 
C |- Fc m0 n0 t ~alpha Fc m1 n1 t' -> (m0 = m1 /\ n0 = n1 /\ C |- t ~alpha t').  
Proof. 
 intros. inversion H; split~; try split~; trivial. 
Qed.

Lemma alpha_equiv_Ab_elim : forall C t t' a a', 
C |- [a]^t ~alpha ([a']^t') -> 
((a = a' /\ C |- t ~alpha t') \/ 
(a <> a' /\ ((C |- t ~alpha (|[(a,a')]| @ t')) /\ C |- a # t'))). 
Proof.
 intros. inversion H.
 left~. right~. 
Qed.

Lemma alpha_equiv_Ab_intro : forall C t t' a a', 
((a = a' /\ C |- t ~alpha t') \/ 
 (a <> a' /\ ((C |- t ~alpha (|[(a,a')]| @ t'))) /\ C |- a # t')) ->
C |- [a]^t ~alpha ([a']^t') .
Proof.
 intros. destruct H. 
 destruct H. rewrite H. apply alpha_equiv_Ab_1; trivial.
 destruct H. destruct H0. apply alpha_equiv_Ab_2; trivial.
Qed.

Lemma alpha_equiv_Su_elim : forall C p p' X,
C |- Su p X ~alpha Su p' X -> (forall a, (In_ds p p' a) -> set_In ((a,X)) C).
Proof. intros. inversion H. apply H3; trivial. Qed.

Hint Resolve alpha_equiv_At_elim.
Hint Resolve alpha_equiv_At_intro.
Hint Resolve alpha_equiv_Pr_elim.
Hint Resolve alpha_equiv_Fc_elim.
Hint Resolve alpha_equiv_Ab_elim.
Hint Resolve alpha_equiv_Ab_intro.
Hint Resolve alpha_equiv_Su_elim.

Require Import Omega.

Lemma alpha_equiv_term_size : forall C s t,
      C |- s ~alpha t -> term_size s = term_size t.                               
Proof.
  intros. induction H; simpl; try omega.
  rewrite perm_term_size in IHalpha_equiv. omega.
Qed.

Lemma alpha_equiv_sub_context : forall C C' s t,
      sub_context C C' -> C |- s ~alpha t -> C' |- s ~alpha t.
Proof.
  intros. induction H0.
  apply alpha_equiv_Ut. apply alpha_equiv_At.
  apply alpha_equiv_Pr.
   apply IHalpha_equiv1; trivial.
   apply IHalpha_equiv2; trivial.
  apply alpha_equiv_Fc.
   apply IHalpha_equiv; trivial.
  apply alpha_equiv_Ab_1.  
   apply IHalpha_equiv; trivial.
  apply alpha_equiv_Ab_2; trivial.
   apply IHalpha_equiv; trivial.
  apply fresh_lemma_3 with (C:=C); trivial.
  apply alpha_equiv_Su; intros.
   unfold sub_context in H. 
   apply H. apply H0; trivial.
Qed.
   
Lemma ds_empty_fresh_1 : forall C pi pi' a t,
                         (forall b, ~ In_ds pi pi' b) -> 
                         (C |- (pi $ a) # t <-> C |- (pi' $ a) # t) .
Proof.
  intros.
  assert (Q : pi $ a = pi' $ a).
   apply not_In_ds. apply H.
  rewrite Q. split~; intro; trivial.
Qed.

Lemma ds_empty_fresh_2 : forall C pi pi' a t,
      (forall b, ~ In_ds pi pi' b) ->
      C |-  a # (pi @ t) -> C |- a # (pi' @ t) .
Proof.
  intros. apply fresh_lemma_1 in H0.
  apply fresh_lemma_1.
  apply ds_empty_fresh_1 with (pi := !pi); trivial.
  intros. intro H1. apply H1. apply not_In_ds_inv.
  intros. apply H.
Qed.

Lemma ds_empty_equiv_1 : forall C pi pi' s t, (forall b, ~ In_ds pi pi' b) -> 
                         C |- (pi @ s) ~alpha t ->
                         C |- (pi'@ s) ~alpha t .
Proof.
  intros. gen t.
  induction s; intros;
   simpl in *|-*; inverts H0; auto.
  replace (pi' $ a) with (pi $ a). auto.
  apply not_In_ds; trivial.
  replace (pi' $ a) with (pi $ a). 
  apply alpha_equiv_Ab_1. apply IHs; trivial.
  apply not_In_ds; trivial.
  replace (pi' $ a) with (pi $ a).   
  apply alpha_equiv_Ab_2; trivial.
  apply IHs; trivial. apply not_In_ds; trivial.
  apply alpha_equiv_Su; intros.
  apply H5. intro H1. apply H0. clear H0. 
  rewrite <- perm_comp_atom in *|-*.
  rewrite <- H1. symmetry. apply not_In_ds; trivial.  
Qed.

Lemma ds_empty_equiv_2 : forall C pi pi' s t, (forall b, ~ In_ds pi pi' b) -> 
                         C |- s ~alpha (pi @ t) ->
                         C |- s ~alpha (pi' @ t) .
Proof.
  intros. gen pi pi' s.
  induction t; intros;
   simpl in *|-*; inverts H0; auto.
  replace (pi' $ a) with (pi $ a). auto.
  apply not_In_ds; trivial.
  replace (pi' $ a) with (pi $ a). 
  apply alpha_equiv_Ab_1. apply IHt with (pi := pi); trivial.
  apply not_In_ds; trivial.
  replace (pi' $ a) with (pi $ a).
  apply alpha_equiv_Ab_2; trivial.
  rewrite perm_comp in *|-*.
  apply IHt with (pi := pi ++ (|[(a0, pi $ a)]|)); trivial; intros.
  rewrite ds_cancel; trivial.
  apply ds_empty_fresh_2 with (pi := pi); trivial.
  apply not_In_ds; trivial.
  apply alpha_equiv_Pr;
    [apply IHt1 with (pi:=pi) | apply IHt2 with (pi:=pi)]; trivial.
  apply alpha_equiv_Fc; apply IHt with (pi:=pi); trivial.
  apply alpha_equiv_Su; intros.
  apply H4. intro H1. apply H0. clear H0. 
  rewrite <- perm_comp_atom in *|-*.
  rewrite H1. apply not_In_ds; trivial.  
Qed.

    
Lemma perm_inv_side : forall C pi s t,
      C |- pi @ s ~alpha t <-> C |- s ~alpha (!pi @ t).   
Proof.
  intros. gen pi t.
  induction s; intros pi t; destruct t; simpl in *|-*; split~;
    intro H; inverts H; autorewrite with perm; auto.

  gen_eq g : (!pi); intro H. replace pi with (!g).
  rewrite perm_inv_atom. trivial.
  rewrite H. rewrite rev_involutive. trivial.

  apply alpha_equiv_Ab_1. apply IHs; trivial.

  apply alpha_equiv_Ab_2.
  intro H. apply H5. 
  apply perm_inv_side_atom in H. trivial.
  apply IHs in H6. rewrite perm_comp in *|-*.
  gen H6. apply ds_empty_equiv_2; intro.
  intro H. apply H. clear H.
  rewrite <- 2 perm_comp_atom. 
  rewrite pi_comm_atom.  
  rewrite perm_inv_atom; trivial.
  apply fresh_lemma_1.
  rewrite rev_involutive; trivial.

  gen_eq g : (!pi); intro H.
  replace pi with (!g).
  rewrite perm_inv_atom; trivial.
  apply alpha_equiv_Ab_1; trivial.
  rewrite H in *|-*.
  rewrite rev_involutive; trivial.
  apply IHs; trivial.
  rewrite H. rewrite rev_involutive; trivial.
  
  apply alpha_equiv_Ab_2.
  intro H. apply H5. 
  apply perm_inv_side_atom in H; trivial.
  apply IHs. rewrite perm_comp in *|-*.
  gen H6. apply ds_empty_equiv_2; intro.
  intro H. apply H. clear H.
  rewrite <- 2 perm_comp_atom. 
  rewrite pi_comm_atom.  
  rewrite perm_inv_atom; trivial.
  apply fresh_lemma_1 in H7.
  rewrite rev_involutive in H7; trivial.

  apply alpha_equiv_Pr; [apply IHs1 | apply IHs2]; trivial.
  apply alpha_equiv_Pr; [apply IHs1 | apply IHs2]; trivial.

  apply alpha_equiv_Fc; apply IHs; trivial.
  apply alpha_equiv_Fc; apply IHs; trivial.
  
  apply alpha_equiv_Su; intros.
  apply H2. unfold In_ds in *|-*.
  intro H0. apply H. clear H2 H.
  rewrite <- perm_comp_atom in *|-*.
  apply perm_inv_side_atom in H0; trivial.
  apply alpha_equiv_Su; intros.
  apply H2. unfold In_ds in *|-*.
  intro H0. apply H. clear H2 H.
  rewrite <- perm_comp_atom in *|-*.
  apply perm_inv_side_atom in H0; trivial.

Qed. 


  
(** Freshness preservation of alpha_equiv *)

Lemma alpha_equiv_fresh : forall C a t1 t2, C |- t1 ~alpha t2 ->
                                                 C |- a # t1 -> C |- a # t2.
Proof.
 intros. induction H; trivial.
 apply fresh_Pr_elim in H0. destruct H0.
 apply fresh_Pr; [apply IHalpha_equiv1 | apply IHalpha_equiv2]; trivial.
 apply fresh_Fc_elim in H0. apply fresh_Fc; apply IHalpha_equiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. rewrite H0. apply fresh_Ab_1.
 destruct H0. apply fresh_Ab_2; trivial. apply IHalpha_equiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. apply fresh_Ab_2.
 intro. apply H. rewrite <- H0. trivial. rewrite <- H0 in H2. trivial.
 destruct H0. case (atom_eqdec a a'); intros.
 rewrite e. apply fresh_Ab_1. apply fresh_Ab_2; trivial.
 assert (Q : C |- a # ((|[(a0, a')]|) @ t')).  apply IHalpha_equiv; trivial.
 apply fresh_lemma_1 in Q. simpl rev in Q. rewrite swap_neither in Q; trivial.
 intro. apply H0. rewrite H4; trivial. intro. apply n. rewrite H4; trivial.
 apply fresh_Su. apply fresh_Su_elim in H0.
 case (atom_eqdec ((!p) $ a) ((!p') $ a)); intros. rewrite <- e; trivial.
 apply H; intros. intro. apply n. gen_eq g : (!p'); intro. 
 replace p' with (!g) in H1. rewrite perm_inv_atom in H1. 
 replace ((!p) $ a) with ((!p) $ (p $ (g $ a))). rewrite perm_inv_atom. trivial.
 rewrite H1. trivial. rewrite H2. rewrite rev_involutive. trivial.
Qed.

(** Equivariance of alpha_equiv *)

Lemma alpha_equiv_equivariance : forall C t1 t2 pi,  
 C |- t1 ~alpha t2 <-> C |- (pi @ t1) ~alpha (pi @ t2).
Proof.
  intros. split~; intros.
  
  apply perm_inv_side.
  rewrite perm_comp.
  apply ds_empty_equiv_2 with (pi := []);
    autorewrite with perm; trivial; intro.
  rewrite ds_sym. rewrite ds_rev_pi_pi.
  intro H0. unfold In_ds in H0. simpl in H0.
  apply H0. trivial.

  apply perm_inv_side in H.
  rewrite perm_comp in H.
  apply ds_empty_equiv_2 with (pi' := []) in H;
    autorewrite with perm; trivial.
  autorewrite with perm in H; trivial.
  intros. rewrite ds_rev_pi_pi.
  intro H0. unfold In_ds in H0. simpl in H0.
  apply H0. trivial.
 
Qed.

(** Invariance of terms under alpha_equiv and the action of permutations *)

Lemma alpha_equiv_pi : forall C t pi pi', 
                 (forall a, (In_ds pi pi' a) -> (C |- a # t)) <->
                  C |- pi @ t ~alpha (pi' @ t) .
Proof. 
 intros C t pi. 
 induction t; split~; autorewrite with perm; intros; auto.
 (* At *)
 apply alpha_equiv_At_intro. apply equiv_pi_atom; intros.
 assert (Q' : C |- a' # %a). apply H; trivial. 
 apply fresh_At_elim in Q'; trivial. 
 apply fresh_At. apply alpha_equiv_At_elim in H. 
 unfold In_ds in H0. intro. rewrite H1 in H0. contradiction.
 (* Ab *)
  (* -> *)
 apply alpha_equiv_Ab_intro. 
 case (atom_eqdec (pi $ a) (pi' $ a)); intros. left~; split~; trivial.
 apply IHt; intros. assert (Q : C |- a0 # Ab a t). apply H; trivial.
 apply fresh_Ab_elim in Q. destruct Q.  unfold In_ds in H0. 
 rewrite H1 in H0. contradiction. destruct H1; trivial. 
 right~. split~; trivial. split~. 
 rewrite perm_comp. apply IHt; intros. unfold In_ds in H0.
 case (atom_eqdec a0 a); intros. apply False_ind. apply H0.
 rewrite e. rewrite <- perm_comp_atom. rewrite swap_right; trivial.
 apply ds_perm_left in H0. assert (Q : C |- a0 # Ab a t). apply H; trivial.
 apply fresh_Ab_elim in Q. destruct Q. contradiction.  
 destruct H1; trivial. 
 assert (Q : C |- ((!pi') $ (pi $ a)) # Ab a t). apply H.
   unfold In_ds. intro. apply n.
   gen_eq g : (!pi'); intro. replace pi' with (!g) in H0.
   rewrite perm_inv_atom in H0. apply perm_eq_atom with (p := pi) in H0. 
   apply perm_inv_side_atom in H0. rewrite H1 in H0. rewrite rev_involutive in H0.
   trivial. rewrite H1. rewrite rev_involutive. trivial.
 apply fresh_Ab_elim in Q. 
 destruct Q. apply perm_inv_side_atom in H0. 
 rewrite rev_involutive in H0. contradiction.
 destruct H0. apply fresh_lemma_1 in H1. trivial.
  (* <- *)
 apply alpha_equiv_Ab_elim in H. destruct H.
 destruct H. case (atom_eqdec a0 a); intros. rewrite e in H0. unfold In_ds in H0. contradiction. 
 apply fresh_Ab_2; trivial. apply (IHt pi'); trivial.
 destruct H. destruct H1.
 case (atom_eqdec a0 a); intros. rewrite e. apply fresh_Ab_1. 
 apply fresh_Ab_2; trivial.
 case (atom_eqdec (pi $ a) (pi' $ a0)); intro. 
 rewrite e in H2. apply fresh_lemma_1 in H2. rewrite perm_inv_atom in H2. trivial.
 rewrite perm_comp in H1. 
 apply IHt with (pi' := pi' ++ (|[(pi $ a, pi' $ a)]|)); trivial. 
 apply ds_perm_right; trivial. 
 (* Pr *)
 apply alpha_equiv_Pr; [apply IHt1 | apply IHt2]; intros; 
 assert (Q : C |- a # <|t1,t2|>); try apply H; trivial; 
 apply fresh_Pr_elim in Q; destruct Q; trivial.
 apply alpha_equiv_Pr_elim in H. destruct H. 
 apply fresh_Pr; [apply (IHt1 pi') | apply (IHt2 pi')]; trivial.
 (* Fc *) 
 apply alpha_equiv_Fc. apply IHt; intros. 
 assert (Q : C |- a # Fc n n0 t); try apply H; trivial.
 apply fresh_Fc_elim in Q; trivial.
 apply alpha_equiv_Fc_elim in H. destruct H. destruct H1.
 apply fresh_Fc; apply (IHt pi'); trivial.
 (* Su *)
 apply alpha_equiv_Su; intros.
 assert (Q : C |- (p $ a) # Su p v). 
  apply H. intro. apply H0. 
  rewrite <- 2 perm_comp_atom. trivial.
 apply fresh_Su_elim in Q. rewrite perm_inv_atom in Q. trivial.
 apply alpha_equiv_Su_elim with (a := (!p) $ a) in H. apply fresh_Su; trivial.
 unfold In_ds in *|-*. rewrite <- 2 perm_comp_atom.
 gen_eq g : (!p); intro. replace p with (!g). rewrite perm_inv_atom; trivial.
 rewrite H1. rewrite rev_involutive. trivial.
Qed.



(** Reflexivity of alpha_equiv *)

Lemma alpha_equiv_refl : forall C t, C |- t ~alpha t.
Proof.
 intros. induction t.
 apply alpha_equiv_Ut. apply alpha_equiv_At. apply alpha_equiv_Ab_1; trivial.
 apply alpha_equiv_Pr; trivial. apply alpha_equiv_Fc; trivial. 
 apply alpha_equiv_Su. intros. apply False_ind. apply H; trivial.
Qed.


(** Symmetry of alpha_equiv *)

Lemma alpha_equiv_sym : forall C t1 t2, C |- t1 ~alpha t2 -> C |- t2 ~alpha t1 .
Proof.
 intros. induction H; auto; trivial. 
 apply alpha_equiv_Ab_2.
 intro H2. apply H. clear H. symmetry; trivial.
 apply perm_inv_side in IHalpha_equiv.  
 simpl in IHalpha_equiv. gen IHalpha_equiv.
 apply ds_empty_equiv_2.
 intros. apply not_In_ds. apply swap_comm.
 apply alpha_equiv_fresh with (a:=a') in IHalpha_equiv; trivial.
 apply fresh_lemma_1. simpl rev. 
 rewrite swap_right. trivial.
 apply alpha_equiv_Su; intros. apply H. apply ds_sym; trivial.
Qed.
 

(** Transitivity of alpha_equiv *)
 
Lemma alpha_equiv_trans : forall C t1 t2 t3,
 C |- t1 ~alpha t2 -> C |- t2 ~alpha t3 -> C |- t1 ~alpha t3.
Proof.
 intros C t1 t2 t3. gen_eq l : (term_size t1); intro H.
 gen t1 t2 t3 H. induction l using peano_induction; intros.
 inverts H1; inverts H2; auto. simpl in H0.
 (* Pr *)
 apply alpha_equiv_Pr. 
 apply H with (m:=term_size t0) (t2:=t1'); try omega; trivial.
 apply H with (m:=term_size t4) (t2:=t2'); try omega; trivial.
 (* Fc *)
 apply alpha_equiv_Fc. simpl in H0.
 apply H with (m:=term_size t) (t2:=t'); try omega; trivial.
 (* Ab *)
  (* a = b = c *)
  apply alpha_equiv_Ab_1. simpl in H0.
  apply H with (m:=term_size t) (t2:=t'); try omega; trivial.
  (* a = b <> c *)
  apply alpha_equiv_Ab_2; trivial. simpl in H0.
  apply H with (m:=term_size t) (t2:=t'); try omega; trivial.
  (* a <> b = c *)
  apply alpha_equiv_Ab_2; trivial. simpl in H0.
  apply H with (m:=term_size t) (t2:=(|[(a, a')]|) @ t'); try omega; trivial.
  apply alpha_equiv_equivariance; trivial.
  apply alpha_equiv_fresh with (a:=a) in H9; trivial.
  (* a <> b <> c *) 
  simpl in H0. case (atom_eqdec a a'0); intro H1.
   (* a = c *)
   rewrite <- H1 in *|-*. clear H1 H7.
   apply alpha_equiv_Ab_1. 
   apply H with (m:=term_size t) (t2:=(|[(a, a')]|) @ t'); try omega; trivial.  
   apply perm_inv_side. simpl.   
   apply ds_empty_equiv_2 with (pi := |[(a', a)]|); trivial.
   intro c. apply not_In_ds. apply swap_comm.
   (* a <> c *)
   assert (Q : C |- a # t'0).
    apply alpha_equiv_fresh with (a:=a) in H9; trivial.
    apply fresh_lemma_1 in H9. simpl rev in H9.
    rewrite swap_neither in H9; trivial.
    intro H2. apply H3. symmetry. trivial.
    intro H2. apply H1. symmetry. trivial.      
   apply alpha_equiv_Ab_2; trivial.
   apply H with (m:=term_size t) (t2:=(|[(a, a')]|) @ t'); try omega; trivial.  
   apply perm_inv_side. simpl. rewrite perm_comp.
   apply H with (m:=term_size t') (t2:=(|[(a', a'0)]|) @ t'0); trivial.
   apply alpha_equiv_term_size in H4. rewrite perm_term_size in H4. omega.
   apply alpha_equiv_pi. intros b H2.
   unfold In_ds in H2. rewrite <- perm_comp_atom in H2.
   rewrite pi_comm_atom in H2.
   rewrite swap_left in H2. rewrite swap_neither with (c:=a'0) in H2; trivial.
   apply perm_diff_atom in H2.
   case (atom_eqdec a b); intro H10. rewrite <- H10; trivial.
   case (atom_eqdec a' b); intro H12. rewrite <- H12; trivial.   
   rewrite swap_neither in H2; trivial. false.
 (* Su *)
 inversion H0. apply alpha_equiv_Su; intros.
 apply ds_trans with (pi2:=p') in H2. destruct H2.
 apply H3; trivial. apply H7; trivial.
Qed.


(** Corollaries *)

Corollary alpha_equiv_pi_comm : forall C a b t pi, 
C |- pi @ (|[(a,b)]| @ t) ~alpha (|[(pi $ a, pi $ b)]| @ (pi @ t)) . 
Proof.
  intros. rewrite 2 perm_comp.
  apply alpha_equiv_pi; intros c H.
  false. gen H. apply not_In_ds.
  rewrite <- 2 perm_comp_atom.
  apply pi_comm_atom.  
Qed.
 
Corollary alpha_equiv_perm_inv : forall C pi t, C |- (pi ++ !pi) @ t ~alpha t.
Proof.
  intros. rewrite <- perm_comp.
  rewrite perm_inv_side.
  rewrite rev_involutive.
  apply alpha_equiv_refl.
Qed.  

Corollary alpha_equiv_swap_neither : forall C a a' t, 
C |- a # t -> C |- a' # t -> C |- (|[(a, a')]|) @ t ~alpha t.
Proof.
 intros. replace t with ([] @ t).
 rewrite perm_comp. simpl. apply alpha_equiv_pi; intros.
 unfold In_ds in H1. 
 case (atom_eqdec a a0); intro H2. rewrite <- H2; trivial.
 case (atom_eqdec a' a0); intro H3. rewrite <- H3; trivial.
 rewrite swap_neither in H1; trivial. simpl in H1. false.
 autorewrite with perm; trivial.
Qed.
