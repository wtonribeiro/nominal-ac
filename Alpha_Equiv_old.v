(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Alpha_Equiv.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 3, 2017.
 ============================================================================
*)

Require Export  w_Equiv.

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


(** Intermediate transitivity for alpha_equiv with w_equiv *)

Lemma alpha_equiv_w_equiv_trans : forall C t1 t2 t3, 
  C |- t1 ~alpha t2 -> t2 ~we t3 -> C |- t1 ~alpha t3.
Proof.
 intros. generalize t3 H0; clear t3 H0. 
 induction H; intros; trivial.
 inversion H0; auto. inversion H0; auto. 
 inversion H1. apply alpha_equiv_Pr; [apply IHalpha_equiv1 | apply IHalpha_equiv2]; trivial.
 inversion H0. apply alpha_equiv_Fc. apply IHalpha_equiv; trivial.
 inversion H0. apply alpha_equiv_Ab_1. apply IHalpha_equiv; trivial.
 inversion H2. apply alpha_equiv_Ab_2; trivial. apply IHalpha_equiv.
 apply w_equiv_equivariance; trivial.
 apply w_equiv_fresh with (t1 := t'); trivial.
 inversion H0. apply alpha_equiv_Su; intros.
 apply H. intro. apply H5. setoid_rewrite not_In_ds in H4. 
 rewrite <- H4. trivial.
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
 C |- t1 ~alpha t2 -> C |- (pi @ t1) ~alpha (pi @ t2).
Proof.
 intros. induction H; intros;
 simpl; auto.
 apply alpha_equiv_Ab_2. apply perm_diff_atom; trivial.
 apply alpha_equiv_w_equiv_trans with (t2 :=  (pi @ ((|[(a, a')]|) @ t'))).
 apply IHalpha_equiv. apply w_equiv_pi_comm. apply fresh_lemma_2; trivial.
 apply alpha_equiv_Su. intros. apply H. intro. apply H0.
 rewrite <- 2 perm_comp_atom. rewrite H1; trivial. 
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


(** A Corollary: the order of the atoms inside a swapping doesn't matter in alpha_equiv *)

Corollary alpha_equiv_swap_comm : forall C a b t, C |- |[(a, b)]| @ t ~alpha |[(b, a)]| @ t.
Proof.
 intros. apply alpha_equiv_pi. intros. unfold In_ds in H.
 apply False_ind. apply H. apply swap_comm.
Qed.

(** Second intermediate transitivity lemma *)

Lemma pi_alpha_equiv : forall C t1 t2 pi, 
     C |- t1 ~alpha t2 -> C |- t2 ~alpha (pi @ t2) ->
     C |- t1 ~alpha (pi @ t2).
Proof.
 intros. gen pi H0.  induction H; intro pi; 
 simpl; intros; auto.
(* Pr *)
 apply alpha_equiv_Pr_elim in H1. destruct H1.
 apply alpha_equiv_Pr;
 [apply IHalpha_equiv1 | apply IHalpha_equiv2]; trivial.
(* Fc *)
 apply alpha_equiv_Fc_elim in H0.
 destruct H0. destruct H1. 
 apply alpha_equiv_Fc. apply IHalpha_equiv; trivial.
(* Ab *)
 apply alpha_equiv_Ab_elim in H0. destruct H0.
 
 (* a = a' *)
 
  (* a = pi $ a *)
  destruct H0. rewrite <- H0. 
  apply alpha_equiv_Ab_1;
  apply IHalpha_equiv; trivial.
  destruct H0. destruct H1.
  
  (* a <> pi $ a *)
  apply alpha_equiv_Ab_2; trivial.
  rewrite perm_comp. apply IHalpha_equiv.
  rewrite perm_comp in H1. trivial.
  
(* a <> a' *)
  apply alpha_equiv_Ab_elim in H2. destruct H2.
  
 (* a' = pi $ a' *)
  destruct H2. case (atom_eqdec a (pi $ a')); intros.
  
    (* a = pi $ a' *)
     rewrite <- e in H2. symmetry in H2. contradiction.
  
    (* a <> pi $ a' *)
    apply alpha_equiv_Ab_2; trivial. rewrite <- H2.
    apply  alpha_equiv_w_equiv_trans with
    (t2 := (((a, a')::pi) ++ |[(a, a')]|) @ (|[(a, a')]| @ t')).
    apply IHalpha_equiv. rewrite <- perm_comp.
    apply alpha_equiv_equivariance.
    rewrite swap_app with (p := pi).
    apply alpha_equiv_w_equiv_trans with (t2 := pi @ t'); trivial.
    rewrite 2 perm_comp.
    apply w_equiv_sym. simpl.
    apply w_equiv_swap_cancel.
    rewrite 2 perm_comp. simpl.
    apply w_equiv_swap_cancel.
    apply alpha_equiv_fresh with (t1 := t'); trivial.
    
 (* a' <> pi $ a' *) 
 destruct H2. destruct H3. case (atom_eqdec a (pi $ a')); intro.
    
   (* a = pi $ a' *)
   rewrite e. apply alpha_equiv_Ab_1. rewrite <- e in H3.
   apply alpha_equiv_w_equiv_trans with
   (t2 :=  (((a,a')::pi) @ ((|[(a, a')]|) @ t'))).
   apply IHalpha_equiv.
   rewrite perm_comp in *|-*; simpl.
   apply alpha_equiv_w_equiv_trans with
   (t2 := pi @ t').
   apply alpha_equiv_w_equiv_trans with
   (t2 := ((|[(a, a')]|) @ (pi ++ (|[(a', a)]|) @ t'))).
   apply alpha_equiv_equivariance; trivial.
   apply w_equiv_trans with
   (t2 := ((|[(a', a)]|) @ (pi ++ (|[(a', a)]|) @ t'))).
   apply w_equiv_swap_comm.
   rewrite perm_comp.
   apply w_equiv_swap_cancel2. 
   apply w_equiv_sym.
   apply w_equiv_swap_cancel. 
   rewrite perm_comp. simpl.
   apply w_equiv_swap_cancel. 
   
(** The dificult case: 
    a <> a', a' <> pi $ a', a <> pi $ a' *)

  (* a <> pi $ a' *)
   rewrite perm_comp in H3.
   
  assert (fresh_a : C |- a # (pi @ t')).
    assert (Q : C |- a # (pi ++ (|[(a', pi $ a')]|) @ t')).
    apply alpha_equiv_fresh with (t1 := t'); trivial.
    rewrite <- perm_comp in Q. apply fresh_lemma_1 in Q.
    simpl rev in Q. rewrite swap_neither in Q; 
    try intro H5; try symmetry in H5; try contradiction; trivial.
    
  apply alpha_equiv_Ab_2; trivial.
  apply alpha_equiv_w_equiv_trans with 
  (t2 :=
  ((|[(a, pi $ a')]|) @ (pi @ ((|[(a, a')]|) @ ((|[(a, a')]|) @ t'))))).  
  rewrite 2 perm_comp. apply IHalpha_equiv. 
  rewrite perm_comp.

  apply alpha_equiv_pi; intros.
  unfold In_ds in H5. repeat rewrite <- perm_comp_atom in H5.
  case (atom_eqdec a a0); intro H6.
  (* a = a0 *)
   rewrite H6 in *|-; trivial.
  (* a <> a0 *) 
   case (atom_eqdec a' a0); intro H7.
    (* a' = a0 *)
    rewrite H7 in *|-. rewrite swap_right in H5.
    rewrite swap_left in H5. rewrite swap_right in H5. false. 
    (* a' <> a0 *)
    rewrite 2 swap_neither with (c := a0) in H5; trivial.
    case (atom_eqdec a (pi $ a0)); intro H8.
      (* a = (pi $ a0) *)
      rewrite <- H8 in *|-. rewrite H8 in fresh_a.
      apply fresh_lemma_2 in fresh_a; trivial.
      (* a <> (pi $ a0) *)
      rewrite swap_neither in H5;
      try apply perm_diff_atom; trivial.
      case (atom_eqdec a' (pi $ a0)); intro H9.
        (* a' = (pi $ a0) *)
        rewrite H9 in H4.
        apply fresh_lemma_2 in H4; trivial.
        (* a' <> (pi $ a0) *)
        apply alpha_equiv_pi with
        (pi := []) (pi' := (pi ++ (|[(a', pi $ a')]|))).
        rewrite perm_id; trivial.
        unfold In_ds. rewrite perm_id_atom.
        rewrite <- perm_comp_atom.
        rewrite swap_neither;
        try apply perm_diff_atom; trivial.

  apply w_equiv_equivariance.
  apply w_equiv_equivariance.
  apply w_equiv_sym.
  apply w_equiv_swap_inv_side.
  apply w_equiv_refl.

(* Su *)
 apply alpha_equiv_Su. intros. case (In_ds_dec p' (p' ++ pi) a); intros.
 apply alpha_equiv_Su_elim with (a := a) in H0; trivial. 
 apply not_In_ds in H2. apply H. intro. apply H1. rewrite H3; trivial.
Qed.


(** Reflexivity of alpha_equiv *)

Lemma alpha_equiv_refl : forall C t, C |- t ~alpha t.
Proof.
 intros. induction t.
 apply alpha_equiv_Ut. apply alpha_equiv_At. apply alpha_equiv_Ab_1; trivial.
 apply alpha_equiv_Pr; trivial. apply alpha_equiv_Fc; trivial. 
 apply alpha_equiv_Su. intros. apply False_ind. apply H; trivial.
Qed.

(** Transitivity of alpha_equiv *)
 
Lemma alpha_equiv_trans : forall C t1 t2 t3,
 C |- t1 ~alpha t2 -> C |- t2 ~alpha t3 -> C |- t1 ~alpha t3.
Proof.
 intros. gen t3 H0. induction H; intros; trivial.
(* Pr *)
 inversion H1. apply alpha_equiv_Pr; [apply IHalpha_equiv1 | apply IHalpha_equiv2]; trivial.
(* Fc *) 
 inversion H0. apply alpha_equiv_Fc.  apply IHalpha_equiv; trivial. 
(* Ab *)
 inverts H0. apply alpha_equiv_Ab_1; apply IHalpha_equiv; trivial. 
 apply alpha_equiv_Ab_2; trivial. apply IHalpha_equiv; trivial.
 inverts H2. apply alpha_equiv_Ab_2; trivial. apply IHalpha_equiv.
 apply alpha_equiv_equivariance; trivial. 
 apply alpha_equiv_fresh with (t1 := t'); trivial.
 case (atom_eqdec a a'0); intros. rewrite e. apply alpha_equiv_Ab_1.
 apply IHalpha_equiv. apply alpha_equiv_w_equiv_trans with 
  (t2 := (|[(a, a')]|) @ ((|[(a, a')]|) @ t'0)). 
 apply alpha_equiv_equivariance. apply alpha_equiv_w_equiv_trans with
  (t2 := (|[(a', a)]|) @ t'0). rewrite e; trivial. 
 apply w_equiv_swap_comm. apply w_equiv_sym.
 apply w_equiv_swap_inv_side. apply w_equiv_refl.
 assert (Q0 : C |- a # ((|[(a', a'0)]|) @ t'0)). 
  apply alpha_equiv_fresh with (t1 := t'); trivial.
 apply fresh_lemma_1 in Q0. simpl rev in Q0. 
 rewrite swap_neither in Q0; try intro H8; try symmetry in H8; try contradiction.
 apply alpha_equiv_Ab_2; trivial.
 apply IHalpha_equiv. apply alpha_equiv_equivariance with (pi := |[(a, a')]|) in H7.
 assert 
  (Q : C |- ((a',a'0)::|[(a,a')]|) @ t'0 ~alpha (((a',a'0)::(a,a')::|[(a',a'0)]|) @ t'0)).
  apply alpha_equiv_pi; intros. unfold In_ds in H2.
  rewrite swap_app_atom in H2. 
  rewrite swap_app_atom with (p := (a,a')::(|[(a',a'0)]|)) in H2.
  rewrite swap_app_atom with (p := |[(a',a'0)]|) in H2.
  case (atom_eqdec a' a0); intros. rewrite <- e; trivial.
  case (atom_eqdec a'0 a0); intros. rewrite e in H2.
  rewrite 2 swap_right in H2. rewrite swap_neither in H2.
  apply False_ind. apply H2; trivial. 
  intro. symmetry in H3. contradiction.
  intro. rewrite <- e in H3. symmetry in H3. contradiction.
  rewrite swap_neither with (a := a') (b := a'0) in H2; trivial.  
  case (atom_eqdec a a0); intros. rewrite <- e; trivial.
  rewrite 2 swap_neither in H2; trivial. apply False_ind. apply H2; trivial.
 rewrite swap_app in Q. 
 rewrite swap_app with (p := (a,a')::(|[(a',a'0)]|)) in Q.
 rewrite swap_app with (p := |[(a',a'0)]|) in Q. 
 gen_eq t1 : ((|[(a, a')]|) @ t'); intro. 
 gen_eq t2 : ((|[(a, a')]|) @ ((|[(a', a'0)]|) @ t'0)); intro.
 assert (Q' : C |- t1 ~alpha ((|[(a', a'0)]|) @ t2)). apply pi_alpha_equiv; trivial.
 rewrite H3 in Q'. apply alpha_equiv_w_equiv_trans with 
 (t2 := (|[(a', a'0)]|) @ ((|[(a, a')]|) @ ((|[(a', a'0)]|) @ t'0))); trivial.
 apply w_equiv_trans with 
 (t2 := ((|[((|[(a', a'0)]|) $ a, (|[(a', a'0)]|) $ a')]|) @ ((|[(a', a'0)]|) @ 
        ((|[(a', a'0)]|) @ t'0)))). apply w_equiv_pi_comm.
 rewrite swap_neither with (c := a); 
 try intro H10; try symmetry in H10; try contradiction. rewrite swap_left. 
 apply w_equiv_equivariance. apply w_equiv_sym. 
 apply w_equiv_swap_inv_side. apply w_equiv_refl. 
(* Su *)
 inversion H0. apply alpha_equiv_Su; intros.
 case (In_ds_dec p p' a); intros. apply H; trivial.
 apply H5. apply not_In_ds in H7. unfold In_ds in *|-*. 
 rewrite <- H7; trivial.
Qed.

(** Symmetry of alpha_equiv *)

Lemma alpha_equiv_sym : forall C t1 t2, C |- t1 ~alpha t2 -> C |- t2 ~alpha t1 .
Proof.
 intros. induction H; auto; trivial. 
 assert (Q0 : C |- t' ~alpha ((|[(a', a)]|) @ t)).
  apply alpha_equiv_trans with (t2 := (|[(a, a')]|) @ t).
  apply alpha_equiv_trans with (t2 := (|[(a, a')]|) @ ((|[(a, a')]|) @ t')).
  apply alpha_equiv_w_equiv_trans with (t2 := t'). apply alpha_equiv_refl.
  apply w_equiv_swap_inv_side. apply w_equiv_refl.
  apply alpha_equiv_equivariance; trivial. apply alpha_equiv_swap_comm.
 assert (Q1 : C |- a # ((|[(a', a)]|) @ t)).
  apply alpha_equiv_fresh with (t1 := t'); trivial.
 apply fresh_lemma_1 in Q1. simpl rev in Q1. rewrite swap_right in Q1.
 apply alpha_equiv_Ab_2; trivial. intro. symmetry in H2. contradiction.
 apply alpha_equiv_Su. intros. apply H. apply ds_sym. trivial.
Qed.


(** Corollaries *)

Corollary alpha_equiv_pi_comm : forall C a b t pi, 
C |- pi @ (|[(a,b)]| @ t) ~alpha (|[(pi $ a, pi $ b)]| @ (pi @ t)) . 
Proof.
  intros. rewrite 2 perm_comp. apply alpha_equiv_pi; intros.
  false. apply H. rewrite <- 2 perm_comp_atom.
  rewrite pi_comm_atom. trivial.
Qed.

Corollary alpha_equiv_perm_inv : forall C pi t,
C |- (pi ++ !pi) @ t ~alpha t.
Proof.
  intros. replace t with ([]@t).
  rewrite perm_comp. apply alpha_equiv_pi; intros.
  false. apply H. simpl. rewrite <- perm_comp_atom.
  rewrite perm_inv_atom. trivial.
  autorewrite with perm; trivial.
Qed.  

Corollary alpha_equiv_pi_inv_side_left : forall C pi t1 t2, 
 C |- (!pi) @ t1 ~alpha t2 -> C |- t1 ~alpha (pi @ t2).
Proof.
 intros. apply alpha_equiv_trans with (t2 := pi @ ((!pi) @ t1)).
 apply alpha_equiv_sym. rewrite perm_comp. gen_eq g : (!pi); intros. 
 replace pi with (!g). apply alpha_equiv_perm_inv. 
 rewrite H0. apply rev_involutive. apply alpha_equiv_equivariance; trivial.
Qed.

Corollary alpha_equiv_pi_inv_side_right : forall C pi t1 t2, 
C |- t1 ~alpha (pi @ t2) -> C |- (!pi) @ t1 ~alpha t2.
Proof.
 intros. apply alpha_equiv_sym in H. gen_eq g : (!pi); intros.
 replace pi with (!g) in H. apply alpha_equiv_pi_inv_side_left in H.
 apply alpha_equiv_sym; trivial. rewrite H0. apply rev_involutive.
Qed. 

Corollary alpha_equiv_pi_inv_side: forall C pi t1 t2, 
 C |- (!pi) @ t1 ~alpha t2 <-> C |- t1 ~alpha (pi @ t2). 
Proof.
 split~; intros; 
   [apply alpha_equiv_pi_inv_side_left |
    apply  alpha_equiv_pi_inv_side_right]; 
 trivial.
Qed.
 
Corollary alpha_equiv_swap_inv_side : forall C a b t1 t2,
 C |- (|[(a,b)]|) @ t1 ~alpha t2 <-> C |- t1 ~alpha ((|[(a,b)]|) @ t2).
Proof.
  intros. split~; intro.
  apply alpha_equiv_pi_inv_side. simpl rev; trivial.
  apply alpha_equiv_sym.
  apply alpha_equiv_pi_inv_side.
  apply alpha_equiv_sym. simpl rev; trivial.
Qed.

Corollary alpha_equiv_swap_commutes : forall C a b t1 t2,
 C |- t1 ~alpha ((|[(a,b)]|) @ t2) -> C |- t1 ~alpha ((|[(b,a)]|) @ t2).
Proof.
  intros. apply alpha_equiv_trans with (t2:= (|[(a, b)]|) @ t2); trivial.
  apply alpha_equiv_pi; intros. false. apply H0.
  apply swap_comm.
Qed. 
  
Corollary alpha_equiv_equivariance_right : forall C pi t1 t2,
C |- pi @ t1 ~alpha (pi @ t2) -> C |- t1 ~alpha t2.
Proof.
 intros. apply alpha_equiv_trans with (t2 := (!pi) @ (pi @ t1)). 
 apply alpha_equiv_sym. rewrite perm_comp. apply alpha_equiv_perm_inv.
 apply alpha_equiv_trans with (t2 := (!pi) @ (pi @ t2)).  
 apply alpha_equiv_equivariance; trivial.
 rewrite perm_comp. apply alpha_equiv_perm_inv.
Qed.

Corollary alpha_equiv_swap_neither : forall C a a' t, 
C |- a # t -> C |- a' # t -> C |- (|[(a, a')]|) @ t ~alpha t.
Proof.
 intros. replace t with ([] @ t).
 rewrite perm_comp. simpl.
 apply alpha_equiv_pi; intros. gen H1. unfold In_ds. 
 case (atom_eqdec a a0); intro H2. rewrite <- H2; intro; trivial.
 case (atom_eqdec a' a0); intro H3. rewrite <- H3; intro; trivial.
 rewrite swap_neither; auto. intro H4. false. apply H4. 
 simpl; trivial. autorewrite with perm. trivial.
Qed.

Corollary alpha_equiv_inv_swap : forall C a b c t,
          a <> b -> b <> c -> a <> c ->
          C |- a # t -> C |- b # t ->
          C |- (|[(a, b)]|) @ ((|[(b, c)]|) @ t) ~alpha ((|[(a, c)]|) @ t).
Proof.
  intros.
  rewrite perm_comp. apply alpha_equiv_pi; intros.
  unfold In_ds in H4. rewrite <- perm_comp_atom in H4.
  case (atom_eqdec a a0); intro H5. rewrite <- H5; trivial.
  case (atom_eqdec c a0); intro H6.
  rewrite <- H6 in *|-. false.
  apply H4. rewrite 3 swap_right; trivial.
  case (atom_eqdec b a0); intro H7. rewrite <- H7; trivial.
  false. apply H4. rewrite 3 swap_neither with (c:=a0); trivial.
Qed.  