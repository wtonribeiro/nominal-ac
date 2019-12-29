(** 
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Equiv.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala R\'incon 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: Sep 17, 2018.

 Description : This is a guideline how to deal with A, C and AC equivalence
               starting from the notion of alpha-equivalence for purely.  
               The idea is we have already defined a notion of alpha-
               equivalence for nominal terms without A, C or AC function symbols. Now,
               the signature is extended allowing these objects.  
 ============================================================================
*)

Require Export Tuples Alpha_Equiv Morphisms.


(** Inductive definition of equiv which encompasses, an parametric way,
              the definitions of alpha, a, ac and c equivalences *)

Inductive equiv (S : set nat): Context -> term -> term -> Prop :=

 | equiv_Ut   : forall C, equiv S C (<<>>) (<<>>) 

 | equiv_At   : forall C a, equiv S C (%a) (%a)

 | equiv_Pr   : forall C t1 t2 t1' t2', (equiv S C t1 t1') -> (equiv S C t2 t2') -> 
                                          equiv S C (<|t1,t2|>) (<|t1',t2'|>)  

 | equiv_Fc   :  forall E n t t' C, (~ set_In E S \/
                                    (E = 2 /\ ((~ is_Pr t) \/ (~ is_Pr t')))) -> 
                                    (equiv S C t t') -> 
                              equiv S C (Fc E n t) (Fc E n t')

(** Checks only for alpha-equivalence *)  
                                    
 | equiv_Ab_1 : forall C a t t', (equiv S C t t') -> 
                               equiv S C ([a]^t) ([a]^t')
                                     
 | equiv_Ab_2 : forall C a a' t t', 
                a <> a' -> (equiv S C t (|[(a,a')]| @ t')) -> C |- a # t' -> 
                                    equiv S C ([a]^t) ([a']^t')

 | equiv_Su   : forall (C: Context) p p' (X: Var), 
               (forall a, (In_ds p p' a) -> set_In ((a,X)) C) ->
               equiv S C (p|.X) (p'|.X)


(** Checks only for A-alpha-equivalence *)  

 | equiv_A : set_In 0 S -> 
             forall n t t' C, 
             (equiv S C (TPith 1 (Fc 0 n t) 0 n) (TPith 1 (Fc 0 n t') 0 n))  ->
             (equiv S C (TPithdel 1 (Fc 0 n t) 0 n) (TPithdel 1 (Fc 0 n t') 0 n)) ->
             (equiv S C (Fc 0 n t) (Fc 0 n t'))

(** Checks only for AC-alpha-equivalence *)

 | equiv_AC   : set_In 1 S -> 
                forall n t t' i C,
                (equiv S C (TPith 1 (Fc 1 n t) 1 n)  (TPith i (Fc 1 n t') 1 n))  ->
                (equiv S C (TPithdel 1 (Fc 1 n t) 1 n) (TPithdel i (Fc 1 n t') 1 n)) ->
                (equiv S C (Fc 1 n t) (Fc 1 n t'))  

(** Checks only for C-alpha-equivalence *)

 | equiv_C1 : set_In 2 S ->
              forall n s0 s1 t0 t1 C,
              (equiv S C s0 t0) -> (equiv S C s1 t1) -> 
              (equiv S C (Fc 2 n (<|s0, s1|>)) (Fc 2 n (<|t0, t1|>)))
                
 | equiv_C2 : set_In 2 S ->
              forall n s0 s1 t0 t1 C,
              (equiv S C s0 t1) -> (equiv S C s1 t0) -> 
              (equiv S C (Fc 2 n (<|s0, s1|>)) (Fc 2 n (<|t0, t1|>)))    
.

Hint Constructors equiv.


(** Notations for the different equivalences *)


Notation "C |- t ~e t'" := (equiv ([]) C t t') (at level 67).
Notation "C |- t ~a t'" := (equiv (|[0]|) C t t') (at level 67). 
Notation "C |- t ~ac t'" := (equiv (|[1]|) C t t') (at level 67).
Notation "C |- t ~c t'" := (equiv (|[2]|) C t t') (at level 67).
Notation "C |- t ~acc t'" := (equiv (1::|[2]|) C t t') (at level 67).
Notation "C |- t ~aacc t'" := (equiv (0 :: 1 :: (|[2]|)) C t t') (at level 67). 

(** alpha\_equiv is equivalent equiv ([]) *)

Lemma alpha_equiv_eq_equiv : forall C t t',
 C |- t ~alpha t' <-> C |- t ~e t'.
Proof.
 intros. split~; intro H; induction H; auto;
 simpl in H; try contradiction.
Qed.

Hint Resolve alpha_equiv_eq_equiv.


(** Some basic properties about alpha\_equiv *)

Require Import Omega.

Lemma alpha_equiv_TPlength : forall C t1 t2 E n, 
 C |- t1 ~alpha t2 -> TPlength t1 E n = TPlength t2 E n. 
Proof.
  intros. induction H; trivial. simpl; auto.
  case (nat_pair_eqdec (E,n) (m,n0)); intro H0. inverts H0.
  autorewrite with tuples; trivial.
  rewrite 2 TPlength_Fc_diff; auto.
Qed.

Lemma alpha_equiv_TPith : forall C t t' i E n, 
  C |- t ~alpha t' -> C |- TPith i t E n ~alpha TPith i t' E n.
Proof. 
 intros. gen i. induction H; intro i.
 apply alpha_equiv_refl. apply alpha_equiv_refl.
 apply alpha_equiv_TPlength with (E:=E) (n:=n) in H.
 case (le_dec i (TPlength t1 E n)); intro H1. 
 rewrite 2 TPith_Pr_le; try omega; auto.
 rewrite 2 TPith_Pr_gt; try omega. rewrite H; auto.
 generalize H; intro H'. apply alpha_equiv_TPlength with (E:=E) (n:=n) in H.
 case (nat_pair_eqdec (E,n) (m,n0)); intro H0. inverts H0. autorewrite with tuples; trivial.
 rewrite 2 TPith_Fc_diff; auto.  
 simpl; auto. simpl; auto. simpl; auto. 
Qed. 

Lemma alpha_equiv_TPithdel : forall C t t' i E n, 
  C |- t ~alpha t' -> C |- TPithdel i t E n ~alpha TPithdel i t' E n.
Proof. 
 intros. gen i. induction H; intro i.
 apply alpha_equiv_refl. apply alpha_equiv_refl.
 generalize H; intro H'. generalize H0; intro H0'.
 apply alpha_equiv_TPlength with (E:=E) (n:=n) in H.
 apply alpha_equiv_TPlength with (E:=E) (n:=n) in H0.
 case (le_dec i (TPlength t1 E n)); intro H1. 
 case (eq_nat_dec (TPlength t1 E n) 1); intro H2. 
 rewrite 2 TPithdel_t1_Pr; try omega; trivial. 
 rewrite 2 TPithdel_Pr_le; try omega; auto.
 case (eq_nat_dec (TPlength t2 E n) 1); intro H2. 
 rewrite 2 TPithdel_t2_Pr; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try omega. rewrite H; auto.
 generalize H; intro H'. apply alpha_equiv_TPlength with (E:=E) (n:=n) in H.
 case (nat_pair_eqdec (E,n) (m,n0)); intro H0. inverts H0.
 case (nat_eqdec (TPlength t m n0) 1); intro H0.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; try omega; auto.
 rewrite 2 TPithdel_Fc_eq; try omega. apply alpha_equiv_Fc; auto.
 rewrite 2 TPithdel_Fc_diff; auto.  
 simpl; auto. simpl; auto. simpl; auto. 
Qed.


(** Manipulating the function symbols superscripts *)

(**  The following results are going towards the proof that 
if (equiv S0 C) is a equivalence and S1 is a subset of S0
then (equiv S1 C) is also a equivalence. *)

Definition proper_equiv_Fc (S1 : set nat) :=
forall C t t' m n, equiv S1 C t t' -> equiv S1 C (Fc m n t) (Fc m n t').

Lemma subset_equiv : forall S1 S2 C t t', proper_equiv_Fc S2 ->
      subset nat S1 S2 -> equiv S1 C t t' -> equiv S2 C t t'.
Proof.
  intros. induction H1; auto.
  apply equiv_AC with (i:=i); trivial.
  apply H0; trivial.  
Qed.

Lemma subset_equiv_inv : forall S1 S2 C t t',
      subset nat S1 S2 ->                      
     (forall k, set_In k (set_super t) -> set_In k S1 \/ ~ set_In k S2) ->                     
      equiv S2 C t t' ->  equiv S1 C t t'. 
Proof.
  intros. induction H1; auto; simpl set_super in H0|-.
  
  apply equiv_Pr;
  [apply IHequiv1; intros; apply H0; apply set_union_intro1
  |apply IHequiv2; intros; apply H0; apply set_union_intro2]; trivial.

  apply equiv_Fc; simpl set_In in *|-*; try omega.
  destruct H1. left~. right~.
 
  apply IHequiv; intros. apply (H0 k). apply set_add_intro1; trivial.

  case (set_In_dec eq_nat_dec 0 S1); intro H2.
  apply equiv_A; simpl set_In; try omega; trivial;
  [apply IHequiv1; intros; apply H0 | apply IHequiv2; intros; apply H0].
  autorewrite with tuples in H3. apply set_super_TPith in H3.
  apply set_add_intro1; trivial. case (eq_nat_dec (TPlength t 0 n) 1); intro H4.
  rewrite TPithdel_TPlength_1 in H3; autorewrite with tuples; trivial.
  simpl in H3. contradiction. rewrite TPithdel_Fc_eq in H3; trivial.
  simpl in H3. apply set_add_elim in H3. destruct H3.
  apply set_add_intro2; trivial. apply set_add_intro1.
  apply set_super_TPithdel in H3; trivial.
  assert (Q: set_In 0 S1 \/ ~ set_In 0 S2).
   apply H0. apply set_add_intro2; trivial.
   destruct Q; contradiction.
   
  case (set_In_dec eq_nat_dec 1 S1); intro H2.
  apply equiv_AC with (i:=i); simpl set_In; try omega; trivial;
  [apply IHequiv1; intros; apply H0 | apply IHequiv2; intros; apply H0].
  autorewrite with tuples in H3. apply set_super_TPith in H3.
  apply set_add_intro1; trivial. case (eq_nat_dec (TPlength t 1 n) 1); intro H4.
  rewrite TPithdel_TPlength_1 in H3; autorewrite with tuples; trivial.
  simpl in H3. contradiction. rewrite TPithdel_Fc_eq in H3; trivial.
  simpl in H3. apply set_add_elim in H3. destruct H3.
  apply set_add_intro2; trivial. apply set_add_intro1.
  apply set_super_TPithdel in H3; trivial.
  assert (Q: set_In 1 S1 \/ ~ set_In 1 S2).
  apply H0. apply set_add_intro2; trivial.
  destruct Q; contradiction.

  case (set_In_dec eq_nat_dec 2 S1); intro H2. 
  apply equiv_C1; trivial.
  apply IHequiv1; intros. apply H0.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply IHequiv2; intros. apply H0.
  apply set_add_intro1. apply set_union_intro2; trivial.
  assert (Q: set_In 2 S1 \/ ~ set_In 2 S2).
  apply H0. apply set_add_intro2; trivial.
  destruct Q; contradiction.
  
  case (set_In_dec eq_nat_dec 2 S1); intro H2. 
  apply equiv_C2; trivial.
  apply IHequiv1; intros. apply H0.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply IHequiv2; intros. apply H0.
  apply set_add_intro1. apply set_union_intro2; trivial.
  assert (Q: set_In 2 S1 \/ ~ set_In 2 S2).
  apply H0. apply set_add_intro2; trivial.
  destruct Q; contradiction.
  
Qed.

Lemma rpl_equiv : forall C t t' S1 S2 E,
      S1 |I S2 = [] -> 
     (forall k, set_In k (S1 |U (set_super t) |U (set_super t')) -> E >= k) -> 
     (equiv S1 C t t' <-> equiv S1 C (rpl_super S2 E t) (rpl_super S2 E t')) .
Proof.
  intros. gen_eq l : (term_size t). intro Hl.
  gen t t' Hl H0. induction l using peano_induction; intros.
  destruct t; destruct t'; simpl; split~; auto;
  try case (set_In_dec nat_eqdec n S2);
  try case (set_In_dec nat_eqdec n1 S2);
  try intros H2 H3 Q; try intros H2 Q; try intro Q; inverts Q;
  simpl set_In in *|-; simpl term_size in Hl; try omega; try contradiction.

  apply equiv_Ab_1. apply -> H0; trivial. omega.
  apply equiv_Ab_2; trivial. rewrite <- rpl_super_perm.
  apply -> H0; trivial; intros. apply H1.
  apply set_union_elim in H2. destruct H2. apply set_union_intro1; trivial.
  apply set_union_intro2. rewrite perm_set_super in H2; trivial.
  omega. apply fresh_rpl_super; trivial.
  apply equiv_Ab_1. apply <- H0; trivial. omega.
  apply equiv_Ab_2; trivial. apply <- H0; intros; trivial.
  rewrite rpl_super_perm; trivial. apply H1.
  apply set_union_elim in H2. destruct H2. apply set_union_intro1; trivial.
  apply set_union_intro2. rewrite perm_set_super in H2; trivial.
  omega. apply fresh_rpl_super in H9; trivial.
  
  apply equiv_Pr; apply -> H0; trivial; try intros.
  apply H1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial. omega.
  apply H1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1; trivial. 
  apply set_union_intro2. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial. omega.
  apply equiv_Pr; apply <- H0; trivial; try intros.
  apply H1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_union_intro1; trivial. omega.
  apply H1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1. apply set_union_elim in H2. destruct H2.
  apply set_union_intro1; trivial. 
  apply set_union_intro2. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_union_intro2; trivial. omega.

  apply equiv_Fc; trivial. left~.
  intro H9. assert (Q:E >= n1 + E + 1).
  apply H1. apply set_union_intro1; trivial.
  apply set_union_intro1; trivial. omega. 
  apply -> H0; intros; trivial. apply H1.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1; trivial. omega.
  
  assert (Q: set_In 0 (S1 |I S2)). apply set_inter_intro; trivial.
  rewrite H in Q. simpl in Q. contradiction.
  assert (Q: set_In 1 (S1 |I S2)). apply set_inter_intro; trivial.
  rewrite H in Q. simpl in Q. contradiction.

  apply equiv_Fc; trivial. left~.
  intro H10.  assert (Q:E >= 2 + E + 1).
  apply H1. apply set_union_intro1; trivial.
  apply set_union_intro1; trivial. omega. 
  simpl. apply equiv_Pr.
  apply -> H0; intros; trivial. apply H1.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1; trivial.
  apply set_union_intro1; trivial.
  apply set_union_intro2. 
  apply set_add_intro1. apply set_union_intro1; trivial.
  rewrite Hl. omega.
  apply -> H0; intros; trivial. apply H1.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1; trivial.
  apply set_union_intro2; trivial.
  apply set_union_intro2. 
  apply set_add_intro1. apply set_union_intro2; trivial.
  rewrite Hl. omega.

  assert (Q : set_In 2 (S1 |I S2)).
    apply set_inter_intro; trivial.  
  rewrite H in Q. simpl in Q. contradiction.

  apply equiv_Fc; trivial.
  destruct H7.  left~. 
  right~. destruct H4. split~. intros.
  destruct H5; [left~ | right~];
    intro H6; apply H5; apply rpl_super_is_Pr in H6; trivial.
  apply -> H0; intros; trivial. apply H1.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1; trivial. omega.

  Focus 5.
  (* 5:{ *) assert (Q:n=n1). omega. rewrite <- Q in *|-*.
  clear H3 H7 H9 Q. assert (Q: ~ set_In n S1). intro.
  assert (Q: set_In n (S1 |I S2)). apply set_inter_intro; trivial.
  rewrite H in Q. simpl in Q. contradiction.
  apply equiv_Fc; trivial. left~.
  apply <- H0; intros; trivial. apply H1.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_elim in H3. destruct H3.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1; trivial. omega. (* } *)

  Focus 5.
  (* 5:{*) assert (Q:n=n1). omega. rewrite <- Q in *|-*.
  clear H12 H13 H3 H8 Q. assert (n = 0). omega.
  assert (E = 0). omega. rewrite H3 in *|-*. rewrite H5 in *|-*.
  assert (0 >= 1). apply H1. apply set_union_intro1. apply set_union_intro1; trivial. omega. (*}*)
  
  Focus 7.
  (* 7:{ *) assert (Q:E >= n + E + 1). apply H1. apply set_union_intro2. apply set_add_intro2; trivial. omega. (* } *)

  Focus 7.
  (* 7:{ *) assert (n = 0). omega. assert (E = 0). omega. rewrite H5 in *|-*. rewrite H6 in *|-*.
      assert (0 >= 1). apply H1. apply set_union_intro1. apply set_union_intro1; trivial. omega. (* } *)

  Focus 9.
  (* 9:{ *) assert (Q:E >= n1 + E + 1). apply H1. apply set_union_intro1. apply set_union_intro2. apply set_add_intro2; trivial. omega. (* } *)
 
  Focus 9.
  (* 9:{ *) assert (n1 = 0). omega. assert (E = 0). omega. rewrite H4 in *|-*. rewrite H5 in *|-*. 
  assert (0 >= 1). apply H1. apply set_union_intro1. apply set_union_intro1; trivial. omega. (* } *)

  Focus 11.
  (* 11:{ *)  apply equiv_Fc. destruct H7.
  left~. destruct H4. right~. split~.
  destruct H5; [left~ | right~];
    intro H6; apply H5; apply rpl_super_is_Pr; trivial.  
  apply <- H0; intros; trivial. apply H1.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1; trivial. omega. (* } *)


  clear H3. assert (Q:E >=0). apply H1.
  apply set_union_intro2. apply set_add_intro2; simpl; omega.
  apply equiv_A; trivial. autorewrite with tuples in *|-*.
  rewrite 2 TPith_rpl_super; trivial. apply -> H0; intros; trivial. apply H1.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_elim in H3. destruct H3.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_super_TPith in H3; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_super_TPith in H3; trivial.
  assert (Q': term_size (TPith 1 t 0 n2) <= term_size t). apply term_size_TPith. omega.
  assert (Q': TPlength t 0 n2 >= 1 /\ TPlength t' 0 n2 >= 1). auto. destruct Q'.
  case (eq_nat_dec (TPlength t 0 n2) 1); case (eq_nat_dec (TPlength t' 0 n2) 1); intros H5 H6.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_rpl_super; simpl set_In; try omega; auto.
  rewrite TPithdel_TPlength_1 in H13; autorewrite with tuples; trivial.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples; try omega; trivial. inverts H13.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples; try omega; trivial.
  rewrite TPithdel_TPlength_1 with (t:=Fc 0 n2 t') in H13; autorewrite with tuples; trivial.
  inverts H13. rewrite 2 TPithdel_Fc_eq; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial; try omega.
  rewrite 2 TPithdel_rpl_super; trivial; try omega.
  assert (Q':  equiv S1 C (rpl_super S2 E (Fc 0 n2 (TPithdel 1 t 0 n2))) 
                          (rpl_super S2 E (Fc 0 n2 (TPithdel 1 t' 0 n2)))).
   apply -> H0; intros; trivial. rewrite 2 TPithdel_Fc_eq in H13;
   autorewrite with tuples; try omega; trivial. clear H0.
   apply H1. apply set_union_elim in H7. destruct H7.
   apply set_union_intro1. apply set_union_elim in H0. destruct H0.
   apply set_union_intro1; trivial. simpl in H0.
   apply set_add_elim in H0. apply set_union_intro2.
   destruct H0. apply set_add_intro2; trivial.
   apply set_add_intro1. apply set_super_TPithdel in H0; trivial.
   apply set_union_intro2.  simpl in H0. apply set_add_elim in H0.
   destruct H0. apply set_add_intro2; trivial.
   apply set_add_intro1. apply set_super_TPithdel in H0; trivial.
   simpl. assert (Q':term_size (TPithdel 1 t 0 n2) <  term_size t).
   apply term_size_TPithdel; trivial. omega.
  simpl in Q'. gen Q'. case (set_In_dec nat_eqdec 0 S2);
  intros; try contradiction; try omega; trivial.

  clear H3. assert (Q:E >=1). apply H1.
  apply set_union_intro2. apply set_add_intro2; simpl; omega.
  apply equiv_AC with (i:=i); repeat split~;
  autorewrite with tuples; trivial.
  rewrite 2 TPith_rpl_super; trivial. autorewrite with tuples in *|-.
  apply -> H0; intros; trivial. clear H0. apply H1.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1. apply set_super_TPith in H0; trivial. 
  apply set_union_intro2. apply set_add_intro1. apply set_super_TPith in H0; trivial.   
  assert (Q': term_size (TPith 1 t 1 n2) <= term_size t). apply term_size_TPith. omega.
  assert (Q': TPlength t 1 n2 >= 1 /\ TPlength t' 1 n2 >= 1). auto. destruct Q'.
  case (eq_nat_dec (TPlength t 1 n2) 1); case (eq_nat_dec (TPlength t' 1 n2) 1); intros H10 H11.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_rpl_super; try omega; auto.
  rewrite TPithdel_TPlength_1 in H13; autorewrite with tuples; trivial.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples; try omega; trivial. inverts H13.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples; try omega; trivial.
  rewrite TPithdel_TPlength_1 with (t:=Fc 1 n2 t') in H13; autorewrite with tuples; trivial.
  inverts H13. rewrite 2 TPithdel_Fc_eq; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial; try omega.
  rewrite 2 TPithdel_rpl_super; trivial; try omega.
  assert (Q':  equiv S1 C (rpl_super S2 E (Fc 1 n2 (TPithdel 1 t 1 n2))) 
                          (rpl_super S2 E (Fc 1 n2 (TPithdel i t' 1 n2)))).
   apply -> H0; intros; trivial; clear H0. rewrite 2 TPithdel_Fc_eq in H13;
   autorewrite with tuples; try omega; trivial.
   apply H1. clear H1. apply set_union_elim in H5. destruct H5.
   apply set_union_intro1. apply set_union_elim in H0. destruct H0.
   apply set_union_intro1; trivial. apply set_union_intro2.
   simpl in H0. apply set_add_elim in H0. destruct H0.
   apply set_add_intro2; trivial. apply set_add_intro1.
   apply set_super_TPithdel in H0; trivial.
   simpl in H0. apply set_union_intro2.
   apply set_add_elim in H0. destruct H0.
   apply set_add_intro2; trivial. apply set_add_intro1.
   apply set_super_TPithdel in H0; trivial.
   simpl. assert (Q':term_size (TPithdel 1 t 1 n2) < term_size t).
   apply term_size_TPithdel; trivial. omega.
   simpl in Q'. gen Q'. case (set_In_dec nat_eqdec 1 S2);
                          intros; try contradiction; try omega; trivial.

  Focus 9. 
  (* 9:{ *) clear H3. assert (Q:E >=0). apply H1.
  apply set_union_intro2. apply set_add_intro2; simpl; omega.
  apply equiv_A; trivial. autorewrite with tuples in *|-*.
  rewrite 2 TPith_rpl_super in H12; trivial.
  apply <- H0; intros; trivial. apply H1.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_elim in H3. destruct H3.
  apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_super_TPith in H3; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_super_TPith in H3; trivial.
  assert (Q': term_size (TPith 1 t 0 n2) <= term_size t).
  apply term_size_TPith. omega.
  assert (Q': TPlength t 0 n2 >= 1 /\ TPlength t' 0 n2 >= 1). auto. destruct Q'.
  case (eq_nat_dec (TPlength t 0 n2) 1); case (eq_nat_dec (TPlength t' 0 n2) 1); intros H5 H6.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_rpl_super; simpl set_In; try omega; auto.
  rewrite TPithdel_TPlength_1 in H13; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples; try omega;
  try rewrite TPlength_rpl_super; trivial. inverts H13.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples;
  try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite TPithdel_TPlength_1 with (t:=Fc 0 n2 (rpl_super S2 E t')) in H13;
  autorewrite with tuples; try rewrite TPlength_rpl_super; trivial.
  inverts H13. rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial; try omega.
  rewrite 2 TPithdel_rpl_super in H13; trivial; try omega.
  apply <- H0; intros; trivial; clear H0. simpl.
  case (set_In_dec nat_eqdec 0 S2);
  intros; try contradiction; try omega; trivial.
  apply H1. apply set_union_elim in H7. destruct H7.
  apply set_union_intro1. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1; trivial. simpl in H0.
  apply set_add_elim in H0. apply set_union_intro2.
  destruct H0. apply set_add_intro2; trivial.
  apply set_add_intro1. apply set_super_TPithdel in H0; trivial.
  apply set_union_intro2.  simpl in H0. apply set_add_elim in H0.
  destruct H0. apply set_add_intro2; trivial.
  apply set_add_intro1. apply set_super_TPithdel in H0; trivial.
  simpl. assert (Q':term_size (TPithdel 1 t 0 n2) < term_size t).
  apply term_size_TPithdel; trivial. omega. (* } *)

  Focus 9.
  (* 9:{ *) clear H3. assert (Q:E >=1). apply H1.
  apply set_union_intro2. apply set_add_intro2; simpl; omega.
  apply equiv_AC with (i:=i); repeat split~;
  autorewrite with tuples in *|-*; trivial.
  rewrite 2 TPith_rpl_super in H12; trivial.
  apply <- H0; intros; trivial. clear H0. apply H1.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1; trivial. apply set_union_intro2.
  apply set_add_intro1. apply set_super_TPith in H0; trivial. 
  apply set_union_intro2. apply set_add_intro1. apply set_super_TPith in H0; trivial.   
  assert (Q': term_size (TPith 1 t 1 n2) <= term_size t).
  apply term_size_TPith. omega.
  assert (Q': TPlength t 1 n2 >= 1 /\ TPlength t' 1 n2 >= 1). auto. destruct Q'.
  case (eq_nat_dec (TPlength t 1 n2) 1); case (eq_nat_dec (TPlength t' 1 n2) 1); intros H10 H11.
  rewrite 2 TPithdel_TPlength_1; autorewrite with tuples;
  try rewrite TPlength_rpl_super; try omega; auto.
  rewrite TPithdel_TPlength_1 in H13; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples;
  try rewrite TPlength_rpl_super; try omega; trivial. inverts H13.
  rewrite TPithdel_Fc_eq in H13; autorewrite with tuples;
  try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite TPithdel_TPlength_1 with (t:=Fc 1 n2 (rpl_super S2 E t')) in H13;
  try rewrite TPlength_rpl_super; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial.
  inverts H13. rewrite 2 TPithdel_Fc_eq; autorewrite with tuples;
  try rewrite TPlength_rpl_super; trivial; try omega.
  rewrite 2 TPithdel_Fc_eq in *|-*; autorewrite with tuples;
  try rewrite TPlength_rpl_super; try omega; trivial.
  rewrite 2 TPithdel_rpl_super in H13; trivial; try omega.
  apply <- H0; intros; trivial; clear H0. simpl.
  case (set_In_dec nat_eqdec 1 S2); intros; try contradiction; try omega; trivial. 
  apply H1. clear H1. apply set_union_elim in H5. destruct H5.
  apply set_union_intro1. apply set_union_elim in H0. destruct H0.
  apply set_union_intro1; trivial. apply set_union_intro2.
  simpl in H0. apply set_add_elim in H0. destruct H0.
  apply set_add_intro2; trivial. apply set_add_intro1.
  apply set_super_TPithdel in H0; trivial.
  simpl in H0. apply set_union_intro2.
  apply set_add_elim in H0. destruct H0.
  apply set_add_intro2; trivial. apply set_add_intro1.
  apply set_super_TPithdel in H0; trivial.
  simpl. assert (Q':term_size (TPithdel 1 t 1 n2) < term_size t).
  apply term_size_TPithdel; trivial. omega. (* } *)

  simpl rpl_super. apply equiv_C1; trivial.
  apply -> H0; intros; trivial; clear H0; try omega.  
  apply H1. apply set_union_elim in H4. destruct H4.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro1; trivial.
  apply -> H0; intros; trivial; clear H0; try omega.  
  apply H1. apply set_union_elim in H4. destruct H4.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro2; trivial.

  simpl rpl_super. apply equiv_C2; trivial.
  apply -> H0; intros; trivial; clear H0; try omega.  
  apply H1. apply set_union_elim in H4. destruct H4.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro2; trivial.
  apply -> H0; intros; trivial; clear H0; try omega.  
  apply H1. apply set_union_elim in H4. destruct H4.
  apply set_union_elim in H0. destruct H0.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro1; trivial.
  
  assert (Q:n=n1). omega. rewrite <- Q in *|-*.
  assert (E >= n). apply H1.
  apply set_union_intro2. apply set_add_intro2; trivial.
  assert (E = 1). omega. assert (E >= 2). apply H1.
  apply set_union_intro1. apply set_union_intro1; trivial. omega.

  assert (Q:n=n1). omega. rewrite <- Q in *|-*.
  assert (E >= n). apply H1.
  apply set_union_intro2. apply set_add_intro2; trivial.
  assert (E = 1). omega. assert (E >= 2). apply H1.
  apply set_union_intro1. apply set_union_intro1; trivial. omega.

  assert (E >= n). apply H1.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro2; trivial.
  assert (E = 1). omega. assert (E >= 2). apply H1.
  apply set_union_intro2. apply set_add_intro2; trivial. omega.

  assert (E >= n). apply H1.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro2; trivial.
  assert (E = 1). omega. assert (E >= 2). apply H1.
  apply set_union_intro2. apply set_add_intro2; trivial. omega.

  assert (E >= n1). apply H1.
  apply set_union_intro2. apply set_add_intro2; trivial.
  assert (E = 1). omega. assert (E >= 2). apply H1.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro2; trivial. omega.

  assert (E >= n1). apply H1.
  apply set_union_intro2. apply set_add_intro2; trivial.
  assert (E = 1). omega. assert (E >= 2). apply H1.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro2; trivial. omega.

  destruct t; simpl in H6; inverts H6.
  destruct t'; simpl in H11; inverts H11.
  simpl in Hl. simpl in H1. apply equiv_C1; trivial. 
  apply <- H0; intros; trivial; try omega.
  apply H1; intros. apply set_union_elim in H4.
  destruct H4. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro1; trivial.
  apply <- H0; intros; trivial; try omega.
  apply H1; intros. apply set_union_elim in H4.
  destruct H4. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro2; trivial.
  gen H5. case (set_In_dec nat_eqdec n S2); intros; inverts H5.
  gen H5. case (set_In_dec nat_eqdec n S2); intros; inverts H5.   

  destruct t; simpl in H6; inverts H6.
  destruct t'; simpl in H11; inverts H11.
  simpl in Hl. simpl in H1. apply equiv_C2; trivial. 
  apply <- H0; intros; trivial; try omega.
  apply H1; intros. apply set_union_elim in H4.
  destruct H4. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro1; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro2; trivial.
  apply <- H0; intros; trivial; try omega.
  apply H1; intros. apply set_union_elim in H4.
  destruct H4. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_intro1; trivial.
  apply set_union_intro1. apply set_union_intro2.
  apply set_add_intro1. apply set_union_intro2; trivial.
  apply set_union_intro2. apply set_add_intro1.
  apply set_union_intro1; trivial.
  gen H5. case (set_In_dec nat_eqdec n S2); intros; inverts H5.
  gen H5. case (set_In_dec nat_eqdec n S2); intros; inverts H5.   

Qed.


(** Subtheories of equiv({0,1,2}) are equivalences if 
 equiv({0,1,2}) is an equivalence *)

(**
The following lemma is proved by case analysis over Equivalence (equiv S2 C).
*)

Lemma subset_equivalence : forall C S1 S2,
                             subset nat S1 S2 -> proper_equiv_Fc S2 ->
                             Equivalence (equiv S2 C) -> Equivalence (equiv S1 C).
Proof.
  intros. destruct H1.
  split~; unfold Reflexive in *|-*;
         unfold Symmetric in *|-*;
         unfold Transitive in *|-*; intros.

 (** Reflexivity *) 
  case (leq_nat_set (S2 |U (set_super x))); intros E H1.
  apply rpl_equiv with (E:=E) (S2:=set_diff eq_nat_dec S2 S1); intros.
  apply nil_empty_set. intros k H2. apply set_inter_elim in H2. destruct H2.
  apply set_diff_elim2 in H3. contradiction. apply H1.
  apply set_union_elim in H2. destruct H2.
  apply set_union_elim in H2. destruct H2.
  apply set_union_intro1. apply H; trivial.
  apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.
  apply subset_equiv_inv with (S2:=S2); trivial; intros.
  case (set_In_dec eq_nat_dec k S1); intro H3. left~.
  right~. intro H4. gen H2. apply set_rpl_super; intros.
  assert (Q: k0 <= E).
   apply H1. apply set_diff_elim1 in H2.
   apply set_union_intro1; trivial.
  omega. apply set_diff_intro; trivial.

 (** Symmetry *) 
  case (leq_nat_set (S2 |U (set_super x) |U (set_super y))); intros E H2. 
  apply rpl_equiv with (E:=E) (S2:=set_diff eq_nat_dec S2 S1); intros.
  apply nil_empty_set. intros k H3. apply set_inter_elim in H3. destruct H3.
  apply set_diff_elim2 in H4. contradiction. apply H2.
  apply set_union_elim in H3. destruct H3.
  apply set_union_elim in H3. destruct H3.
  apply set_union_intro1. apply set_union_intro1. apply H; trivial.
  apply set_union_intro2; trivial.
  apply set_union_intro1. apply set_union_intro2; trivial.
  apply subset_equiv_inv with (S2:=S2); trivial; intros.
  case (set_In_dec eq_nat_dec k S1); intro H4. left~.
  right~. intro H5. gen H3. apply set_rpl_super; intros.
  assert (Q: k0 <= E).
   apply H2. apply set_diff_elim1 in H3.
   apply set_union_intro1. apply set_union_intro1; trivial.
  omega. apply set_diff_intro; trivial.
  apply rpl_equiv with (E:=E) (S2:=set_diff eq_nat_dec S2 S1) in H1; intros.
  apply subset_equiv with (S2:=S2) in H1; trivial.    
  apply Equivalence_Symmetric; trivial.
  apply nil_empty_set. intros k H4. apply set_inter_elim in H4. destruct H4.
  apply set_diff_elim2 in H5. contradiction. apply H2.
  apply set_union_elim in H4. destruct H4.
  apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply set_union_intro1. apply H; trivial.
  apply set_union_intro1. apply set_union_intro2; trivial.  
  apply set_union_intro2; trivial.

  (** Transitivity *)
  case (leq_nat_set (S2 |U (set_super x) |U (set_super y) |U (set_super z))); intros E H3. 
  apply rpl_equiv with (E:=E) (S2:=set_diff eq_nat_dec S2 S1); intros.
  apply nil_empty_set. intros k H4. apply set_inter_elim in H4. destruct H4.
  apply set_diff_elim2 in H5. contradiction. apply H3.
  apply set_union_elim in H4. destruct H4. apply set_union_intro1.
  apply set_union_intro1. apply set_union_elim in H4. destruct H4.
  apply set_union_intro1. apply H; trivial. apply set_union_intro2; trivial.
  apply set_union_intro2; trivial.
  apply subset_equiv_inv with (S2:=S2); trivial; intros.
  case (set_In_dec eq_nat_dec k S1); intro H5. left~.
  right~. intro H6. gen H4. apply set_rpl_super; intros.
  assert (Q: k0 <= E).
   apply H3. apply set_diff_elim1 in H4.
   apply set_union_intro1. apply set_union_intro1. apply set_union_intro1. trivial.
   omega. apply set_diff_intro; trivial.
  assert (Q: S1 |I set_diff eq_nat_dec S2 S1 = []).
   apply nil_empty_set. intros k H4.
   apply set_inter_elim in H4. destruct H4.
   apply set_diff_elim2 in H5. contradiction. 
  apply rpl_equiv with (E:=E) (S2:=set_diff eq_nat_dec S2 S1) in H1; intros; trivial.
  apply subset_equiv with (S2:=S2) in H1; trivial.    
  apply rpl_equiv with (E:=E) (S2:=set_diff eq_nat_dec S2 S1) in H2; intros; trivial.
  apply subset_equiv with (S2:=S2) in H2; trivial. 
  apply Equivalence_Transitive with
  (y:=(rpl_super (set_diff eq_nat_dec S2 S1) E y)); trivial.
  assert (Q': k <= E).
   apply H3. apply set_union_elim in H5. destruct H5.
   apply set_union_intro1. apply set_union_elim in H5. destruct H5.
   apply set_union_intro1. apply set_union_intro1. apply H; trivial.
   apply set_union_intro2; trivial. apply set_union_intro2; trivial. omega.
  assert (Q': k <= E).
   apply H3. apply set_union_elim in H5. destruct H5.
   apply set_union_intro1. apply set_union_elim in H5. destruct H5.
   apply set_union_intro1. apply set_union_intro1. apply H; trivial.
   apply set_union_intro1. apply set_union_intro2; trivial.
   apply set_union_intro1. apply set_union_intro2; trivial. omega.
Qed.

(** Some usefull properties about the (Fc 2 n) regularity in the relations aacc\_equiv 
    and c\_equiv *)

Lemma equiv_Fc_c : forall C t t' n, C |- t ~aacc t' -> C |- Fc 2 n t ~aacc Fc 2 n t'.
Proof.
  intros.
   case (is_Pr_dec t); intro H0.
   case (is_Pr_dec t'); intro H1.
   apply is_Pr_exists in H0. apply is_Pr_exists in H1.
   case H0; clear H0; intros u0 H0.
   case H0; clear H0; intros u1 H0.
   case H1; clear H1; intros v0 H1.
   case H1; clear H1; intros v1 H1.
   rewrite H0 in *|-*. rewrite H1 in *|-*. clear H0 H1.
  inverts H. apply equiv_C1; trivial.
  simpl. right~.
  apply equiv_Fc; trivial. right~.
  apply equiv_Fc; trivial. right~.  
Qed.

Lemma c_equiv_Fc : forall C t t' m n, C |- t ~c t' -> C |- Fc m n t ~c Fc m n t'.
Proof.
  intros. case (eq_nat_dec m 2); intro H0. rewrite H0. clear H0.
   case (is_Pr_dec t); intro H0.
   case (is_Pr_dec t'); intro H1.
   apply is_Pr_exists in H0. apply is_Pr_exists in H1.
   case H0; clear H0; intros u0 H0.
   case H0; clear H0; intros u1 H0.
   case H1; clear H1; intros v0 H1.
   case H1; clear H1; intros v1 H1.
   rewrite H0 in *|-*. rewrite H1 in *|-*. clear H0 H1.
  inverts H. apply equiv_C1; trivial.
  simpl. left~. apply equiv_Fc; trivial. right~.
  apply equiv_Fc; trivial. right~.
  apply equiv_Fc; trivial. left~.
  intro H1. apply H0. simpl in H1.
  destruct H1; try contradiction. symmetry; trivial.
Qed.
