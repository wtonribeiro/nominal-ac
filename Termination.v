(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Termination.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: April 8, 2017.
 ============================================================================
*)

Require Export C_Unif.                            


Definition Triplet_lex_order (T T': nat * nat * nat) :=
  let N1  := fst (fst T) in
  let N1' := fst (fst T') in
  let N2  := snd (fst T) in
  let N2' := snd (fst T') in
  let N3  := snd T in
  let N3' := snd T' in
   (N1 > N1') \/
  ((N1 >= N1') /\ (N2 > N2')) \/
 (((N1 >= N1') /\ (N2 >= N2')) /\ (N3 > N3')) .
                                          

Definition Problem_lex_measure (P : Problem) :=
  (length (Problem_vars (equ_proj P)), equ_Problem_size P, non_fixpoint_equ P).

Definition Problem_lex_order (P P' : Problem) := 
Triplet_lex_order (Problem_lex_measure P) (Problem_lex_measure P') . 
  
Notation "P >>* P'" := (Problem_lex_order P P') (at level 67).

 
  
(** Termiantion of fresh_sys and equ_sys *)

                                        
Lemma fresh_sys_termination : forall T T', fresh_sys T T' ->
                               (fresh_Problem_size (snd T)) > (fresh_Problem_size (snd T')) .
Proof.
  intros. destruct T. destruct T'. destruct p. destruct p1.
  simpl. inverts H.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=<<>>); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=%b); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > fresh_Problem_size p0 + (term_size s1)  - S (term_size s1)).
   assert (Q': fresh_Problem_size p0 > 0).
    apply fresh_Problem_size_gt_0 with (a:=a) (s:=Fc E n s1); trivial. omega.
  assert (Q': fresh_Problem_size (p0 |+ (a #? s1)) <= fresh_Problem_size p0 + term_size s1). 
  apply fresh_Problem_size_add. simpl in Q'. omega. apply set_add_intro1; trivial.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=[a]^s1); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > 0).
  apply fresh_Problem_size_gt_0 with (a:=a)(s:=[b]^s1); trivial.
  assert (Q': fresh_Problem_size p0 > fresh_Problem_size p0 + (term_size s1)  - S (term_size s1)). omega.
  assert (Q'': fresh_Problem_size (p0 |+ (a #? s1)) <= fresh_Problem_size p0 + term_size s1). 
  apply fresh_Problem_size_add. simpl in Q''. omega. apply set_add_intro1; trivial.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=pi|.X); trivial. omega.

  rewrite fresh_Problem_size_remove; trivial. simpl.
  assert (Q: fresh_Problem_size p0 > 0).
  apply fresh_Problem_size_gt_0 with (a:=a) (s:=<|s1,t|>); trivial.
  assert (Q': fresh_Problem_size p0 >
              fresh_Problem_size p0 + (term_size s1) + (term_size t) - S (term_size s1 + term_size t)).
  omega.
  assert (Q'': fresh_Problem_size (p0 |+ (a #? s1) |+ (a #? t)) <=
               fresh_Problem_size p0 + (term_size s1) + (term_size t)). 
  assert (Q'': fresh_Problem_size ((p0 |+ (a #? s1)) |+ (a #? t)) <=
               fresh_Problem_size (p0 |+ (a #? s1)) + (term_size t)).
  apply fresh_Problem_size_add.
  assert (Q''': fresh_Problem_size (p0 |+ (a #? s1)) <=
               fresh_Problem_size p0 + (term_size s1)).
  apply fresh_Problem_size_add. omega.
  simpl in Q''. omega. apply set_add_intro1. apply set_add_intro1; trivial.
Qed.


Lemma equ_sys_termination : forall T T', equ_sys T T' -> (snd T) >>* (snd T').
Proof.
  intros. destruct H; simpl snd;
  unfold Problem_lex_order;
  unfold Problem_lex_measure;
  unfold Triplet_lex_order; simpl fst; simpl snd.
  
  right~. left~. split~. 
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0. 
  apply Problem_vars_remove in H0; trivial.
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P >= equ_Problem_size ([s~?s])).
   apply equ_Problem_size_neq_nil; trivial.
  assert (Q' : equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=s) (t:=s); trivial. 
  assert (Q'' : term_size s > 0).
   apply term_size_gt_0.
  simpl in Q. omega.
   
  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0. 
  rewrite 2 equ_proj_add_eq in H0. 
  apply equ_proj_set_In_eq in H.
  apply Problem_vars_remove in H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.

  rewrite equ_Problem_size_remove.
  assert (Q : equ_Problem_size (P |+ (s0 ~? t0)) + equ_Problem_size ([s1 ~? t1]) >=
              equ_Problem_size ((P |+ (s0 ~? t0)) |+ (s1 ~? t1))).
   apply equ_Problem_size_add.
  assert (Q' : equ_Problem_size P + equ_Problem_size ([s0 ~? t0]) >=
               equ_Problem_size (P |+ (s0 ~? t0))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=<|s0,s1|>) (t:=<|t0,t1|>); trivial. 
  assert (Q''' : term_size s0 > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1. apply set_add_intro1; trivial.

  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H1. 
  rewrite equ_proj_add_eq in H1. 
  apply equ_proj_set_In_eq in H.
  apply Problem_vars_remove in H1; trivial.
  apply Problem_vars_add in H1. simpl in H1.
  apply set_union_elim in H1. destruct H1; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.  
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P + equ_Problem_size ([t ~? t']) >=
              equ_Problem_size (P |+ (t ~? t'))).
   apply equ_Problem_size_add.
  assert (Q': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=Fc E n t) (t:=Fc E n t'); trivial. 
  assert (Q'' : term_size t > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1; trivial.
   
  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0.
  rewrite equ_proj_add_eq in H0.
  rewrite equ_proj_add_eq in H0. 
  apply Problem_vars_remove in H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply set_union_elim in H0.
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply set_union_elim in H0.  
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.
  
  rewrite equ_Problem_size_remove. 
  assert (Q : equ_Problem_size (P |+ (s0 ~? t0)) + equ_Problem_size ([s1 ~? t1]) >=
              equ_Problem_size ((P |+ (s0 ~? t0)) |+ (s1 ~? t1))).
   apply equ_Problem_size_add.
  assert (Q' : equ_Problem_size P + equ_Problem_size ([s0 ~? t0]) >=
               equ_Problem_size (P |+ (s0 ~? t0))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=Fc 2 n (<| s0, s1 |>)) (t:=Fc 2 n (<| t0, t1 |>)); trivial. 
  assert (Q''' : term_size s0 > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1. apply set_add_intro1; trivial.

  right~. left~. split~.
  
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0.
  rewrite equ_proj_add_eq in H0.
  rewrite equ_proj_add_eq in H0. 
  apply Problem_vars_remove in H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0.
  apply Problem_vars_add in H0; simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply set_union_elim in H0.
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial.
  apply set_union_elim in H0.  
  apply equ_proj_set_In_eq in H.  
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  simpl. destruct H0.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  
  rewrite equ_Problem_size_remove. 
  assert (Q : equ_Problem_size (P |+ (s0 ~? t1)) + equ_Problem_size ([s1 ~? t0]) >=
              equ_Problem_size ((P |+ (s0 ~? t1)) |+ (s1 ~? t0))).
   apply equ_Problem_size_add.
  assert (Q' : equ_Problem_size P + equ_Problem_size ([s0 ~? t1]) >=
               equ_Problem_size (P |+ (s0 ~? t1))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=Fc 2 n (<| s0, s1 |>)) (t:=Fc 2 n (<| t0, t1 |>)); trivial. 
  assert (Q''' : term_size s0 > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1. apply set_add_intro1; trivial.

  
  right~. left~. split~.

  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H0. 
  rewrite equ_proj_add_eq in H0. 
  apply equ_proj_set_In_eq in H.
  apply Problem_vars_remove in H0; trivial.
  apply Problem_vars_add in H0. simpl in H0.
  apply set_union_elim in H0. destruct H0; trivial.
  apply Problem_vars_set_In with (X:=b) in H; trivial.
  
  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size P + equ_Problem_size ([t ~? t']) >=
              equ_Problem_size (P |+ (t ~? t'))).
   apply equ_Problem_size_add.
  assert (Q': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=[a]^t) (t:=[a]^t'); trivial. 
  assert (Q'' : term_size t > 0).
   apply term_size_gt_0.
  simpl in *|-*. omega.
  apply set_add_intro1; trivial.

  
  right~. left~. split~.

  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H1. 
  rewrite equ_proj_add_fresh in H1.
  rewrite equ_proj_add_eq in H1.
  apply equ_proj_set_In_eq in H0.
  apply Problem_vars_remove in H1; trivial.
  apply Problem_vars_add in H1. simpl in H1.
  apply set_union_elim in H1. destruct H1; trivial.
  apply Problem_vars_set_In with (X:=b0) in H0; trivial.  
  simpl. apply set_union_elim in H1. destruct H1.
  apply set_union_intro1; trivial.
  apply set_union_intro2.
  rewrite perm_term_vars in H1; trivial.

  rewrite equ_Problem_size_remove; trivial.
  assert (Q : equ_Problem_size (P |+ (t ~? (([(a, b)]) @ t'))) + equ_Problem_size ([a #? t']) >=
              equ_Problem_size ((P |+ (t ~? (([(a, b)]) @ t'))) |+ (a #? t'))).
   apply equ_Problem_size_add.  
  assert (Q' : equ_Problem_size P + equ_Problem_size ([t ~? (([(a, b)]) @ t')]) >=
              equ_Problem_size (P |+ (t ~? (([(a, b)]) @ t')))).
   apply equ_Problem_size_add.
  assert (Q'': equ_Problem_size P > 0).
   apply equ_Problem_size_gt_0 with (s:=[a]^t) (t:=[b]^t'); trivial. 
  assert (Q''' : term_size t > 0).
   apply term_size_gt_0.
  simpl in *|-*. rewrite perm_term_size in Q'. omega.
  apply set_add_intro1; apply set_add_intro1; trivial.

  left~.

  apply nat_lt_inv.
  apply subset_list'.
  apply Var_eqdec. apply NoDup_Problem_vars.
  intros.
  rewrite equ_proj_union in H2. 
  apply Problem_vars_union in H2.
  apply set_union_elim in H2. destruct H2.

  Focus 2. rewrite equ_proj_subs_fresh in H2.
  simpl in H2. contradiction.

  rewrite equ_proj_subs in H2.
  case (b ==v X); intro H3. rewrite H3 in H2.
  apply In_im_subst_term_Problem in H2.
  rewrite perm_term_vars in H2. contradiction.
  apply In_im_subst_term_Problem' in H2; trivial.
  apply set_union_elim in H2. destruct H2.
  rewrite 2 equ_proj_rem_eq in H2.
  apply Problem_vars_remove in H2.
  apply Problem_vars_remove in H2. trivial.
  rewrite perm_term_vars in H2.
  destruct H0; apply equ_proj_set_In_eq in H0;
  apply Problem_vars_set_In with (X:=b) in H0; simpl; trivial.
  apply set_union_intro2; trivial.
  apply set_add_intro1; trivial.
  
  exists X; split~.
  destruct H0; apply equ_proj_set_In_eq in H0;
  apply Problem_vars_set_In with (X:=X) in H0; simpl; trivial.
  apply set_union_intro1; simpl; left~.
  apply set_add_intro2; trivial.
  intro H2. rewrite equ_proj_union in H2. 
  apply Problem_vars_union in H2.
  apply set_union_elim in H2. destruct H2.

  Focus 2. rewrite equ_proj_subs_fresh in H2.
  simpl in H2; trivial.
  rewrite equ_proj_subs in H2.
  apply In_im_subst_term_Problem in H2.
  rewrite perm_term_vars in H2. contradiction.
  
  right~. right~. split~. split~.
 
  apply nat_leq_inv. apply subset_list; intros.
  apply Var_eqdec. apply NoDup_Problem_vars.
  rewrite equ_proj_rem_eq in H2. 
  rewrite equ_proj_add_eq in H2.
  apply equ_proj_set_In_eq in H1.
  apply Problem_vars_remove in H2; trivial.
  apply Problem_vars_add in H2. simpl in H2.
  apply set_union_elim in H2. destruct H2; trivial.
  apply Problem_vars_set_In with (X:=b) in H1; trivial.

  rewrite equ_Problem_size_remove. simpl. 

  assert (Q : equ_Problem_size P + equ_Problem_size ([((pi ++ (! pi')|.X) ~? (([])|.X))])  >=
               equ_Problem_size (P |+ ((pi ++ (! pi')|.X) ~? (([])|.X)))).
  apply equ_Problem_size_add.
  simpl in Q. omega. apply set_add_intro1; trivial.

  rewrite non_fixpoint_equ_remove.
  rewrite non_fixpoint_equ_add.
  assert (Q : non_fixpoint_equ P > 0).
   apply non_fixpoint_equ_gt_0 with (u:=((pi|.X) ~? (pi'|.X))); trivial.
   intro H2. destruct H2. destruct H2. destruct H2. inverts H3. apply H0; trivial.
  omega. intro H2. apply H0.
  assert (Q' : !pi' = []).
   gen_eq g : (!pi'); intro H'. clear H'.
   destruct g; trivial. symmetry in H2.
   apply app_cons_not_nil in H2. contradiction.
  replace pi' with (!(!pi')). rewrite Q'. simpl; trivial.
  rewrite rev_involutive; trivial.
  apply set_add_intro1; trivial.
  intro. destruct H2. destruct H2. destruct H2. inverts H3. apply H0; trivial.
Qed.