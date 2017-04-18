(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : C_Equiv.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: March 13, 2017.
 ============================================================================
*)

Require Export Equiv Fresh.

(** specific c_equiv elim lemmas *)

Lemma c_equiv_At_elim : forall C a a', C |- (%a) ~c (%a') -> a = a'.
Proof. intros. inverts H; trivial. Qed.

Lemma c_equiv_Pr_elim : forall C t1 t2 t1' t2', 
C |- (<|t1,t2|>) ~c (<|t1',t2'|>) -> ((C |- t1 ~c t1') /\ (C |- t2 ~c t2')).  
Proof. intros. inverts H; try split~. Qed.

Lemma c_equiv_Fc_elim : forall C E E' n n' t t',
((~set_In E (0::1::[2])) \/ (E = 2 /\ (forall s s', t <> <|s,s'|>))) ->                           
C |- Fc E n t ~c Fc E' n' t' -> (E = E' /\ n = n' /\ C |- t ~c t').  
Proof. 
 intros. inverts H0. repeat split~.
 simpl in H6. omega.  simpl in H6. omega.
 false. destruct H. apply H. simpl. right~.
 destruct H. apply (H0 s0 s1); trivial.
 false. destruct H. apply H. simpl. right~.
 destruct H. apply (H0 s0 s1); trivial. 
Qed.

Lemma c_equiv_Fc_c_elim : forall C n n' s1 s2 t1 t2,
 C |- Fc 2 n (<|s1,s2|>) ~c Fc 2 n' (<|t1,t2|>) ->
      (n = n' /\ ((C |- s1 ~c t1 /\ C |- s2 ~c t2) \/
                  (C |- s1 ~c t2 /\ C |- s2 ~c t1))).  
Proof.
  intros. inverts H.
  false. destruct H3. simpl in H. omega.
  destruct H. apply (H0 s1 s2); trivial.
  split~. split~.
Qed.
  
Lemma c_equiv_Ab_elim : forall C t t' a a', 
C |- [a]^t ~c ([a']^t') -> 
((a = a' /\ C |- t ~c t') \/ 
(a <> a' /\ ((C |- t ~c ([(a,a')] @ t')) /\ C |- a # t'))). 
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


(** First intermediate transitivity for c_equiv with alpha_equiv *)

Lemma c_alpha_equiv_trans : forall C t1 t2 t3, 
  C |- t1 ~c t2 -> C |- t2 ~alpha t3 -> C |- t1 ~c t3.
Proof.
 intros. generalize t3 H0; clear t3 H0. 
 induction H; intros t3 H'; inverts H'; auto.
 
 apply equiv_Ab_2; trivial. apply IHequiv.
 apply alpha_equiv_equivariance; trivial.
 apply alpha_equiv_fresh with (t1 := t'); trivial.
 case (a ==at a'0); intro H9. rewrite <- H9.
 apply equiv_Ab_1. apply IHequiv.
 apply alpha_equiv_swap_inv_side.
 apply alpha_equiv_swap_commutes.
 rewrite H9; trivial.
 assert (Q : C |- a # t'0).
  apply alpha_equiv_fresh with (t1 := ([(a',a'0)]) @ t').
  apply alpha_equiv_swap_inv_side; trivial.
  replace ([(a', a'0)]) with (![(a', a'0)]).
  apply fresh_lemma_2. rewrite swap_neither; trivial.
  intro. symmetry in H2. contradiction.
  intro. symmetry in H2. contradiction.
  simpl; trivial.
 apply equiv_Ab_2; trivial. apply IHequiv.
 apply alpha_equiv_swap_inv_side.
 apply alpha_equiv_trans with (t2 := ([(a', a'0)]) @ t'0); trivial.
 apply alpha_equiv_trans with (t2 := ([([(a,a')] $ a, [(a,a')] $ a'0)]) @ (([(a,a')]) @ t'0)). 
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

(** Freshness preservation of c_equiv *)

Lemma c_equiv_fresh : forall C a t1 t2, C |- t1 ~c t2 ->
                                        C |- a # t1 -> C |- a # t2.
Proof.
 intros. induction H; trivial.
 apply fresh_Pr_elim in H0. destruct H0.
 apply fresh_Pr; [apply IHequiv1 | apply IHequiv2]; trivial.
 apply fresh_Fc_elim in H0. apply fresh_Fc; apply IHequiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. rewrite H0. apply fresh_Ab_1.
 destruct H0. apply fresh_Ab_2; trivial. apply IHequiv; trivial.
 apply fresh_Ab_elim in H0. destruct H0. apply fresh_Ab_2.
 intro. apply H. rewrite <- H0. trivial. rewrite <- H0 in H2. trivial.
 destruct H0. case (a ==at a'); intros.
 rewrite e. apply fresh_Ab_1. apply fresh_Ab_2; trivial.
 assert (Q : C |- a # (([(a0, a')]) @ t')).  apply IHequiv; trivial.
 apply fresh_lemma_1 in Q. simpl rev in Q. rewrite swap_neither in Q; trivial.
 intro. apply H0. rewrite H4; trivial. intro. apply n. rewrite H4; trivial.
 apply fresh_Su. apply fresh_Su_elim in H0.
 case (((!p) $ a) ==at ((!p') $ a)); intros. rewrite <- e; trivial.
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


(** Equivariance of c_equiv *)

Lemma c_equiv_equivariance : forall C t1 t2 pi,  
 C |- t1 ~c t2 -> C |- (pi @ t1) ~c (pi @ t2).
Proof.
 intros. induction H; intros;
 autorewrite with perm; auto.
 apply equiv_Fc; trivial.
 destruct H. left~. destruct H. right~; intros.
 split~; intros. intro.
 destruct t; autorewrite with perm in H2; inverts H2.
 apply (H1 t1 t2); trivial.
 apply equiv_Ab_2. apply perm_diff_atom; trivial.
 apply c_alpha_equiv_trans with (t2 := (pi @ (([(a, a')]) @ t'))).
 apply IHequiv. apply alpha_equiv_pi_comm. apply fresh_lemma_3; trivial.
 apply equiv_Su. intros. apply H.
 apply ds_cancel in H0; trivial.
 simpl in H. omega. simpl in H. omega.
Qed.


(** Second intermediate transitivity for c_equiv with alpha_equiv *)

Lemma c_alpha_equiv_trans' : forall C t1 t2 t3, 
  C |- t1 ~alpha t2 -> C |- t2 ~c t3 ->  C |- t1 ~c t3.
Proof.
 intros. gen t3. induction H; intros t3 H'; inverts H'; auto.
 apply equiv_Fc. destruct H5. left~.
 destruct H0. right~. split~; intros.
 intro H7. rewrite H7 in H. inverts H.
 apply (H1 t1' t2'); trivial.
 apply IHalpha_equiv; trivial.

 simpl in H4. omega. simpl in H4. omega.

 inverts H. assert (Q : C |- <| t2, t3 |> ~c  <| t0, t1 |>).
 apply IHalpha_equiv. apply equiv_Pr; trivial.
 inverts Q. apply equiv_C1; trivial.

 inverts H. assert (Q : C |- <| t2, t3 |> ~c  <| t1, t0 |>).
 apply IHalpha_equiv. apply equiv_Pr; trivial.
 inverts Q. apply equiv_C2; trivial.

 assert (Q : C |- a # t'0).
  apply c_equiv_fresh with (a:=a) in H6; trivial.
 apply equiv_Ab_2; trivial. 
 apply IHalpha_equiv. apply c_equiv_equivariance; trivial.

 case (a ==at a'0); intro H9. rewrite <- H9 in *|-*.
 apply equiv_Ab_1. apply IHalpha_equiv.
 apply c_alpha_equiv_trans with (t2:= ([(a, a')]) @ (([(a', a)]) @ t'0)).
 apply c_equiv_equivariance; trivial.
 apply alpha_equiv_swap_inv_side.
 apply alpha_equiv_swap_commutes.
 apply alpha_equiv_refl.
 
 assert (Q : C |- a # t'0).
  apply c_equiv_fresh with (a:=a) in H6; trivial.
  apply fresh_lemma_1 in H6. simpl rev in H6.
  rewrite swap_neither in H6; trivial.
  intro H10. symmetry in H10. contradiction.
  intro H10. symmetry in H10. contradiction. 
 apply equiv_Ab_2; trivial. apply IHalpha_equiv.
 apply c_alpha_equiv_trans with (t2:= ([(a, a')]) @ (([(a', a'0)]) @ t'0)).
 apply c_equiv_equivariance; trivial.
 apply alpha_equiv_inv_swap; trivial.
 
 apply equiv_Su; intros.
 apply ds_trans with (pi2:=p') in H0.
 destruct H0; [apply H | apply H4]; trivial.

 Qed.
 
(** Equivalence of ~c *)

(** The proof of the equivalence of ~c is also given as corolary 
    of the equivalence of the relation ~aacc in the end of the file Equiv.v.
    That predicade is a nominal  relation between two terms, under a freshness context,
    which allows occurrences of associative (only), associative-commutative 
    and commutative (only) function symbols *)

Lemma c_equiv_refl : forall C t, C |- t ~c t.
Proof.
  induction t; auto.
  apply c_equiv_Fc; trivial.
  apply equiv_Su; intros.
  false. 
Qed.

Lemma c_equiv_sym : forall C t1 t2, C |- t1 ~c t2 -> C |- t2 ~c t1.
Proof.
  intros. induction H; auto.
  
  apply equiv_Fc; trivial.
  destruct H. left~. destruct H.
  right~. split~; intros. intro H2. rewrite H2 in H0.
  inverts H0. apply (H1 t1 t2); trivial.

  apply equiv_Ab_2; trivial.
  intro H2. symmetry in H2. contradiction.
  apply c_alpha_equiv_trans' with (t2:= ([(a', a)]) @ (([(a, a')]) @ t')).
  apply alpha_equiv_swap_inv_side.
  apply alpha_equiv_swap_commutes.
  apply alpha_equiv_refl.
  apply c_equiv_equivariance; trivial.
  apply c_equiv_fresh with (a:=a') in IHequiv; trivial.
  replace ([(a, a')]) with (![(a, a')]). apply fresh_lemma_2.
  rewrite swap_right; trivial. simpl; trivial.

  apply equiv_Su; intros. apply H.
  intro H1. unfold In_ds in H0.
  symmetry in H1. contradiction.

  simpl in H. omega.

Qed.

Lemma c_equiv_trans : forall C t1 t2 t3,
                      C |- t1 ~c t2 -> C |- t2 ~c t3 -> C |- t1 ~c t3.
Proof.
  intros C t1 t2 t3. gen_eq l : (term_size t1).
  gen t1 t2 t3. induction l using peano_induction; intros.
  destruct H1; inverts H2; auto; simpl in *|-; try omega.

  apply equiv_Pr; 
    [apply H with (m:=term_size t1) (t2:=t1') |
     apply H with (m:=term_size t2) (t2:=t2')]; try omega; trivial.

  apply equiv_Fc. destruct H1. left~.
  destruct H1. right~.
  apply H with (m:=term_size t) (t2:=t'); try omega; trivial.

  clear H8. destruct H1. omega. destruct H1. clear H1.
  inverts H3. false. 
  destruct H1. omega. destruct H1.
  inverts H3. false. 

  apply equiv_Ab_1.
  apply H with (m:=term_size t) (t2:=t'); try omega; trivial. 

  apply equiv_Ab_2; trivial.
  apply H with (m:=term_size t) (t2:=t'); try omega; trivial.

  apply equiv_Ab_2; trivial.
  apply H with (m:=term_size t) (t2:=([(a, a')]) @ t'); try omega; trivial.
  apply c_equiv_equivariance; trivial.
  apply c_equiv_fresh with (a:=a) in H9; trivial.

  case (a ==at a'0); intro H12. rewrite <- H12 in *|-*.
  apply equiv_Ab_1.
  apply H with (m:=term_size t) (t2:=([(a, a')]) @ t'); try omega; trivial.
  apply c_alpha_equiv_trans with (t2:= ([(a, a')]) @ (([(a', a)]) @ t'0)).
  apply c_equiv_equivariance; trivial.  
  apply alpha_equiv_swap_inv_side.
  apply alpha_equiv_swap_commutes.
  apply alpha_equiv_refl.
  assert (Q : C |- a # t'0).
   apply c_equiv_fresh with (a:=a) in H9; trivial.
   apply fresh_lemma_1 in H9. simpl rev in H9.
   rewrite swap_neither in H9; trivial.
   intro H13. symmetry in H13. contradiction.
   intro H13. symmetry in H13. contradiction.   
  apply equiv_Ab_2; trivial.
  apply H with (m:=term_size t) (t2:=([(a, a')]) @ t'); try omega; trivial.
  apply c_alpha_equiv_trans with (t2:= ([(a, a')]) @ (([(a', a'0)]) @ t'0)).  
  apply c_equiv_equivariance; trivial.
  apply alpha_equiv_inv_swap; trivial.

  apply equiv_Su; intros.
  apply ds_trans with (pi2:=p') in H2; intros.
  destruct H2; [apply H1 | apply H7]; trivial.

  false. destruct H8. apply H2; omega.
  destruct H2. apply (H3 t0 t1); trivial.

  clear H1 H7. apply equiv_C1; 
    [left~ |
     apply H with (m:=term_size s0) (t2:=t0) |
     apply H with (m:=term_size s1) (t2:=t1)]; try omega; trivial.

  clear H1 H7. apply equiv_C2; 
    [left~ |
     apply H with (m:=term_size s0) (t2:=t0) |
     apply H with (m:=term_size s1) (t2:=t1)]; try omega; trivial.

  false. destruct H8. apply H2; omega.
  destruct H2. apply (H3 t0 t1); trivial.

  clear H1 H7. apply equiv_C2; 
    [left~ |
     apply H with (m:=term_size s0) (t2:=t1) |
     apply H with (m:=term_size s1) (t2:=t0)]; try omega; trivial.

  clear H1 H7. apply equiv_C1; 
    [left~ |
     apply H with (m:=term_size s0) (t2:=t1) |
     apply H with (m:=term_size s1) (t2:=t0)]; try omega; trivial.

Qed.

(** Corolaries *)

Corollary c_equiv_pi_inv_side : forall C pi t1 t2,
 C |- pi @ t1 ~c t2 <-> C |- t1 ~c ((!pi) @ t2).
Proof.
  intros. split~; intro.
  apply c_alpha_equiv_trans' with (t2:=(!pi) @ (pi @ t1)). 
  apply alpha_equiv_sym. apply alpha_equiv_pi_inv_side.
  apply alpha_equiv_refl. apply c_equiv_equivariance; trivial.
  apply c_alpha_equiv_trans with (t2:=pi @ ((!pi) @ t2)). 
  apply c_equiv_equivariance; trivial.
  apply alpha_equiv_sym. apply alpha_equiv_pi_inv_side. 
  apply alpha_equiv_refl.
Qed.


(** Invariance of terms under c_equiv and the action of permutations *)

Lemma c_equiv_pi : forall C t pi, 
                   (forall a, (In_ds pi ([]) a) -> (C |- a # t)) -> C |- pi @ t ~c t.
Proof.
  intros. gen pi.
  induction t; intros;
  autorewrite with perm; auto.

  (* At *)
  case (pi $ a ==at a); intro H0. rewrite H0; auto.  
  assert (Q:  C |- a # (% a)).
   apply H. unfold In_ds. simpl; auto.
  inverts Q. false. 

  (* Ab *)
  case (pi $ a ==at a); intro H0.
  (* pi $ a = a *)
   rewrite H0. apply equiv_Ab_1.
   apply IHt; intros.
   assert (Q :  C |- a0 # ([a]^ t)). apply H; trivial.
   inverts Q; trivial.
   unfold In_ds in H1. simpl in H1. contradiction.
  (* pi $ a <> a *)
   apply equiv_Ab_2; trivial.
   apply c_equiv_sym.
   apply c_equiv_pi_inv_side. simpl.
   rewrite perm_comp.
   apply c_equiv_sym.
   apply IHt; intros.
   unfold In_ds in H1.
   rewrite <- perm_comp_atom in H1.
   replace (([]) $ a0) with a0 in H1; auto.
   case (a ==at (pi $ a0)); intro H2. symmetry in H2.
   rewrite H2 in H1. rewrite swap_right in H1.
   assert (Q : a <> a0).
    apply perm_diff_atom with (p := pi).
    intro H3. rewrite <- H3 in H2. contradiction.    
   assert (Q' : C |- a0 # ([a]^ t)).
    apply H. unfold In_ds. simpl.
    intro H3. rewrite H2 in H3. contradiction.
   inverts Q'. false.  trivial.
   case ((pi $ a) ==at (pi $ a0)); intro H3. symmetry in H3.
   rewrite H3 in H1. rewrite swap_left in H1.
   apply perm_eq_atom in H3. symmetry in H3. contradiction.
   rewrite swap_neither in H1; trivial.
   assert (Q' : C |- a0 # ([a]^ t)).
    apply H. unfold In_ds. simpl. trivial.
   inverts Q'; trivial. false. trivial.
   assert (Q' : C |- (pi $ a) # ([a]^ t)).
    apply H. unfold In_ds. simpl. intro H1.
    apply perm_inv_side_atom in H1.
    rewrite perm_inv_atom in H1. contradiction.
   inverts Q'; trivial. contradiction.

  (* Pr *)
   apply equiv_Pr; [apply IHt1 | apply IHt2]; intros;
   assert (Q: C |- a # (<| t1, t2 |>)); try apply H; trivial;
   inverts Q; trivial.

  (* Fc *)
   apply c_equiv_Fc. apply IHt; intros.
   assert (Q: C |- a # Fc n n0 t). apply H; trivial.
   inverts Q; trivial.

  (* Su *)
   apply equiv_Su; intros.
   assert (Q : C |- (p $ a) # (p|.v)).
    apply H. apply ds_cancel2.
    replace (p ++ ([])) with p; trivial.
    rewrite app_nil_r; trivial.
   inverts Q. replace ((! p) $ (p $ a)) with a in H4; trivial.
   rewrite perm_inv_atom. trivial.
Qed.


Lemma c_equiv_pi' : forall C t pi pi', 
                   (forall a, (In_ds pi pi' a) -> (C |- a # t)) -> C |- pi @ t ~c (pi' @ t).
Proof.
  intros.
  apply c_equiv_pi_inv_side.
  apply c_equiv_sym.
  rewrite perm_comp.
  apply c_equiv_pi; intros.
  apply H. apply ds_sym in H0. 
  apply -> ds_rev in H0; trivial.
Qed.

(***)


Lemma c_equiv_term_size : forall C s t, C |- s ~c t -> term_size s = term_size t.
Proof.
  intros. induction H; simpl; try omega.
  rewrite perm_term_size in IHequiv. omega.
  simpl in H. omega. simpl in H. omega.
Qed.
  
Lemma c_equiv_psubterm : forall C s t, C |- s ~c t -> ~ set_In s (psubterms t).
Proof.
  intros. intro H'.
  apply c_equiv_term_size in H.
  apply psubterms_term_size_lt in H'.
  omega.
Qed.

Lemma c_equiv_perm_psubterm : forall C pi s t, C |- s ~c t -> ~ set_In (pi @ s) (psubterms t).
Proof.
  intros. intro H'.
  apply c_equiv_term_size in H.
  apply psubterms_term_size_lt in H'.
  rewrite perm_term_size in H'.
  omega.
Qed.

(*
Lemma c_equiv_Fc_inv : forall C E n pi pi' t,
                         C |- Fc E n (pi @ t) ~c Fc E n (pi' @ t) ->
                         C |- pi @ t ~c (pi' @ t).
Proof.
  intros. case (Pr_eqdec t); intro H0.
  case H0; clear H0; intros u H0.
  case H0; clear H0; intros v H0.
  rewrite H0 in *|-*. clear H0.
  autorewrite with perm in *|-*.
*)