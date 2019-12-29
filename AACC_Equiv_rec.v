(** 
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : AACC_Equiv_rec.v
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala R\'incon 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: Sep 16, 2018.

 Description : This file contains recursive versions of the inductive 
               definitions fresh and equiv from files Fresh.v and Equiv.v.
               The definition equiv_rec uses an extra Matthieu Sozeau Equations 
               package. The proofs of correctness of these recursive
               definitions are also included in the present file.
               From this file OCaml executable code was automatically generated
               for A, AC and C nominal equality checking.

 ============================================================================
*)


(** Import the library Equiv *)
Require Import Equiv.

(** Import the Equations Package *)
From Equations Require Import Equations. 


(** A recursive version for the fresh relation *)

Fixpoint fresh_rec (C : Context) (a : Atom) (t : term) :=

  match t with

  (** a # <<>> under any freshness context *)  

  | <<>> => true

  (** a # %a0, under any freshness context, only if a <> a0 *)

  | %a0 => if eq_atom_rec a a0
           then false
           else true

  (** a # [a0]^s if a = a0 or if a # s under the same freshness context *)                

  | [a0]^s => if eq_atom_rec a a0
              then true
              else fresh_rec C a s

  (** a # <|u, v|> if a # u and a # v under the same freshness context *)                          

  | <|u, v|> => fresh_rec C a u && fresh_rec C a v

  (** a # Fc m n s if a # s under the same freshness context *)

  | Fc m n s => fresh_rec C a s

  (** a # pi|.X if the pair (!pi $ a, X) is in the freshness context *)                           

  | pi|.X => if in_context_dec (!pi $ a, X) C
             then true
             else false

  end.


(** A interation function that tests the predicade P for every k,
    from i to i + j - 1. If P is true for a k in this range, the iter
    function stops with "true" as a result. Otherwise it keeps iterating 
    the test until the end of the range and the response will be P (i + j - 1). 
    This function is used in the AC cheking of definition equiv_rec *) 

Fixpoint iter (P : nat -> bool) (i j : nat) {struct j} : bool :=
         match j with
         | 0 => false
         | S j0 => if P i
                   then true
                   else iter P (S i) j0
         end .


(** equiv_rec is a recursive definition that is proved to be equivalent
    to the relation ~aacc of file Equiv.v *)

Equations equiv_rec (C: Context) (s t : term) : bool :=

          equiv_rec C s t by rec (term_size s) lt :=

          (** Ut ~ Ut in any freshness context *)
            
          equiv_rec C Ut Ut := true;

          (** At a ~ At b only if a = b *) 
                                 
          equiv_rec C (At a) (At b) := eq_atom_rec a b;

          (** The two cases w.r.t Ab a u ~ Ab b v:
              1) If a = b, u ~ v is verified
              2) If a <> b, it is verified if a # v and 
                            then if u ~ (a b)v *)                                
                                         
          equiv_rec C (Ab a u) (Ab b v) := if eq_atom_rec a b
                                           then equiv_rec C u v
                                           else
                                             if fresh_rec C a v
                                             then
                                               equiv_rec C u (((a,b)::nil)@v)
                                             else false;
                                                    
          (** For Pr u0 u1 ~ Pr v0 v1 one verifies first if 
              u0 ~ v0 and then if u1 ~ v1 *)
                                                    
          equiv_rec C (Pr u0 u1) (Pr v0 v1) := if equiv_rec C u0 v0
                                               then equiv_rec C u1 v1
                                               else false;
                                        
          (** For the case Fc 0 n u ~ Fc E n' v, it is verified
              that n = n' and 0 = E, then if TPith 1 u 0 n ~ TPith 1 v 0 n,
              one verifies that TPithdel 1 (Fc 0 n u) 0 n ~ TPithdel 1 (Fc 0 n v) 0 n *)   
                                                 
          equiv_rec C (Fc 0 n u) (Fc E n' v) :=

            if eq_nat_rec n n' && eq_nat_rec 0 E
                                                               
            then       
               
                 if equiv_rec C (TPith 1 u 0 n) (TPith 1 v 0 n) 
                 then equiv_rec C (TPithdel 1 (Fc 0 n u) 0 n)
                                  (TPithdel 1 (Fc 0 n v) 0 n)
                 else false
                                  
            else false;

          (** For the case Fc 1 n u ~ Fc E n' v, it is verified
              that n = n' and 1 = E. Then for i = 1, ..., (TPlength v 1 n) one
              uses the iter function to test that if 
              (TPith 1 u 1 n) ~ (TPith i v 1 n) then 
              (TPithdel 1 (Fc 1 n u) 1 n) ~ (TPithdel i (Fc 1 n v) 1 n). 
              If the response is "true" for some i, the iteration process stops. *)
              
          equiv_rec C (Fc 1 n u) (Fc E n' v) :=

            if eq_nat_rec n n' && eq_nat_rec 1 E       

            then


                let branch (i : nat) :=
                    if equiv_rec C (TPith 1 u 1 n) (TPith i v 1 n)
                    then equiv_rec C (TPithdel 1 (Fc 1 n u) 1 n)
                                     (TPithdel i (Fc 1 n v) 1 n)
                    else false
                                     
                in iter branch 1 (TPlength v 1 n)
                   


            else false;
              
          (** For Fc 2 n (Pr u0 u1) ~ (Fc E n' (Pr v0 v1) one
              verifies that n = n' and 2 = E and then the two cases of
              the C function symbols are verified:
              1) u0 ~ v0 and u1 ~ v1, or 
              2) u0 ~ v1 and u1 ~ v0 *)
              
          
          equiv_rec C (Fc 2 n (Pr u0 u1)) (Fc E n' (Pr v0 v1)) :=

            if eq_nat_rec n n' && eq_nat_rec 2 E

            then
              if
                 if equiv_rec C u0 v0
                 then equiv_rec C u1 v1
                 else false               
              then
                 true
              else    
                 if equiv_rec C u0 v1
                 then equiv_rec C u1 v0
                 else false
            else false;

              
          (** The remaining cases of Fc are verified thought Fc E n u ~ Fc E' n' v.
              iIf E = E' and n = n' then u ~ v is verified *)
              
          equiv_rec C (Fc E n u) (Fc E' n' v) := if eq_nat_rec E E' &&
                                                    eq_nat_rec n n'
                                                 then equiv_rec C u v
                                                 else false;

          (** The case Su pi X ~ Su pi' Y is verified by checking if X = Y
              and if (disgr pi pi')#X is subset of the freshness context C *) 
                                                   
          equiv_rec C (Su pi X) (Su pi' Y) :=
              if eq_var_rec X Y
              then sub_context_rec (fresh_context (disgr pi pi') X) C
              else false;

          (** All the other cases have "false" as answer *)
                     
          equiv_rec C _ _ := false.


(** The following obligations are regarding the well-foundedness 
    of the measure (term_size s) *)

Next Obligation.
apply -> le_Sn. fold plus.
apply le_plus.
Defined.

Next Obligation.
apply -> le_Sn. fold plus.
rewrite plus_com.
apply le_plus.
Defined.

Next Obligation.
apply -> le_Sn.
apply term_size_TPith.
Defined.

Next Obligation. 
rewrite eq_nat_refl. apply -> le_Sn.
gen_eq b : (eq_nat_rec (TPlength u 0 n) 1); intro H0.
symmetry in H0.
destruct b. 
apply term_size_1_le.
apply term_size_TPithdel.
apply eq_nat_diff in H0. trivial.
Defined.

Next Obligation.
apply -> le_Sn.
apply term_size_TPith.
Defined.

Next Obligation.
rewrite eq_nat_refl. apply -> le_Sn.
gen_eq b : (eq_nat_rec (TPlength u 1 n) 1); intro H0.
symmetry in H0.
destruct b. 
apply term_size_1_le.
apply term_size_TPithdel.
apply eq_nat_diff in H0. trivial.
Defined.

Next Obligation.
apply -> le_Sn.
apply le_S. fold plus.
apply le_plus.
Defined.

Next Obligation.
apply -> le_Sn.
apply le_S. fold plus.
rewrite plus_com.
apply le_plus.
Defined.

Next Obligation.
apply -> le_Sn.
apply le_S. fold plus.
apply le_plus.
Defined.

Next Obligation.
apply -> le_Sn.
apply le_S. fold plus.
rewrite plus_com.
apply le_plus.
Defined.  


(** The Coq command to extract recursively the certified 
    OCaml w.r.t equiv_rec. *)

Recursive Extraction equiv_rec.


(** *)


(** Correctness of fresh_rec *)

Lemma fresh_rec_eq : forall C a t,
      C |- a # t <-> fresh_rec C a t = true. 
Proof.
  intros. split~; intro H.
  induction H; simpl; trivial.
  rewrite IHfresh1. rewrite IHfresh2.
  simpl; trivial.
  destruct a; simpl. rewrite eq_nat_refl; trivial.
  destruct a; destruct a'. simpl.
  assert (Q : eq_nat_rec n n0 = false).
   apply eq_nat_diff. intro H1.
   apply H. rewrite H1. trivial.
  rewrite Q; trivial.
  destruct a; destruct a'. simpl.
  assert (Q : eq_nat_rec n n0 = false).
   apply eq_nat_diff. intro H1.
   apply H. rewrite H1. trivial.   
  rewrite Q; trivial.   
  case (in_context_dec ((! p) $ a, X) C); intro H0; trivial.
  contradiction.
  induction t; simpl in H.
  apply fresh_Ut.
  destruct a. destruct a0. simpl in H.
  gen_eq b : (eq_nat_rec n n0); intro H'.
  destruct b. inversion H. symmetry in H'.
  apply eq_nat_diff in H'. apply fresh_At.
  intro H0. apply H'. inverts H0; trivial.
  destruct a. destruct a0. simpl in H.
  gen_eq b : (eq_nat_rec n n0); intro H'.
  destruct b. symmetry in H'. apply eq_nat_refl' in H'.
  rewrite H'. apply fresh_Ab_1.
  symmetry in H'. apply eq_nat_diff in H'.  
  apply fresh_Ab_2.
  intro H0. apply H'. inverts H0; trivial.
  apply IHt; trivial.
  symmetry in H. apply andb_true_eq in H.
  destruct H. symmetry in H.  symmetry in H0.
  apply IHt1 in H. apply IHt2 in H0.
  apply fresh_Pr; trivial.
  apply fresh_Fc. apply IHt; trivial.
  gen H. case (in_context_dec ((! p) $ a, v) C); intros H0 H.
  apply fresh_Su; trivial.
  inverts H.
Qed.

(** Basic correction lemmas of equiv_rec *)

(** Correction of the unit case of equiv_rec *)

Lemma equiv_rec_Ut : forall C, equiv_rec C Ut Ut = true.
Proof.
  intros. simp equiv_rec.
Qed.

Hint Rewrite equiv_rec_Ut : equiv.


(** Correction of the atom case of equiv_rec *)

Lemma equiv_rec_At : forall C a b,
      equiv_rec C (At a) (At b) = eq_atom_rec a b.
Proof.
  intros. simp equiv_rec.
Qed.

Hint Rewrite equiv_rec_At : equiv.

(** Correction of the abstraction case of equiv_rec *)

Lemma equiv_rec_Ab_1 : forall C a s t,
      equiv_rec C (Ab a s) (Ab a t) = equiv_rec C s t. 
Proof.
  intros. simp equiv_rec.
  destruct a. simpl. rewrite eq_nat_refl.
  trivial.
Qed.

Hint Rewrite equiv_rec_Ab_1 : equiv.

Lemma equiv_rec_Ab_2 : forall C a b s t, a <> b ->
      equiv_rec C (Ab a s) (Ab b t) =
      fresh_rec C a t &&  equiv_rec C s (((a,b)::nil)@t). 
Proof.
  intros. simp equiv_rec.
  destruct a. destruct b.
  assert (Q : n <> n0).
   intro H0. apply H. rewrite H0; trivial. 
  simpl. apply eq_nat_diff in Q. rewrite Q.
  gen_eq b : (fresh_rec C (atom n) t); intro H0.
  destruct b; simpl; trivial.
Qed.

(** Correction of the pair case of equiv_rec *)

Lemma equiv_rec_Pr : forall C s0 s1 t0 t1,
      equiv_rec C (Pr s0 s1) (Pr t0 t1) =
      equiv_rec C s0 t0 && equiv_rec C s1 t1.
Proof.
  intros. simp equiv_rec.
Qed.

Hint Rewrite equiv_rec_Pr : equiv.

(** Correction of the application of a non A, C or AC 
    checking case of equiv_rec *)
  
Lemma equiv_rec_Fc : forall C s t E n,
      ~ In E [0;1;2] \/ (E = 2 /\ ((~ is_Pr s) \/ (~ is_Pr t))) ->
      equiv_rec C (Fc E n s) (Fc E n t) = equiv_rec C s t.
Proof.
  intros. destruct H. destruct E.
  false. apply H. left~.
  destruct E.
  false. apply H. right~. left~.
  destruct E. 
  false. apply H. right~. right~. left~.
  simp equiv_rec.
  rewrite 2 eq_nat_refl.
  simpl. trivial.
  destruct H. rewrite H.
  clear H. destruct H0.
  destruct s; simpl in H;
  simp equiv_rec; try rewrite 2 eq_nat_refl; trivial.
  false. apply H. trivial.
  destruct s; destruct t; simpl in H;
  simp equiv_rec; try rewrite 2 eq_nat_refl; trivial.
  false. apply H; trivial.
Qed.

Lemma equiv_rec_Fc_diff : forall C s t E n, ~ is_Fc' t ->
      equiv_rec C (Fc E n s) t = false.
Proof.
  intros. case (set_In_nat_dec E [0;1;2]); intro H0.
  simpl in H0.
  destruct H0. rewrite <- H0.
  destruct t; simpl in H; simp equiv_rec.
  apply False_ind. apply H. trivial.
  destruct H0. rewrite <- H0.
  destruct t; simpl in H; simp equiv_rec.
  apply False_ind. apply H. trivial.
  destruct H0. rewrite <- H0.
  destruct s; destruct t; simp equiv_rec;
  simpl in H; false; apply H; trivial. contradiction.
  destruct E. false. apply H0. left~.
  destruct E. false. apply H0. right~. left~.
  destruct E. false. apply H0. right~. right~. left~.
  destruct t; simp equiv_rec.
  simpl in H. false. apply H; trivial.
Qed.

Lemma equiv_rec_Fc_diff' : forall C s t E E' n n',
      (E, n) <> (E', n') ->
      equiv_rec C (Fc E n s) (Fc E' n' t) = false.
Proof.
  intros. 
  gen_eq b : (eq_nat_rec n n'); intro H0.
  symmetry in H0. destruct b.
  apply eq_nat_refl' in H0. rewrite <- H0 in *|-*. clear H0.
  gen_eq b : (eq_nat_rec E E'); intro H0.
  symmetry in H0. destruct b.
  apply eq_nat_refl' in H0. false. 
  destruct E; simp equiv_rec; try rewrite H0;
    try rewrite andb_false_r; trivial.
  destruct E; simp equiv_rec; try rewrite H0;
    try rewrite andb_false_r; trivial.
  destruct E; simp equiv_rec; try rewrite H0;
    try rewrite andb_false_r; trivial.
  destruct s; destruct t;
    simp equiv_rec; rewrite H0; try rewrite andb_false_r; trivial.
  destruct E; simp equiv_rec; try rewrite H0; trivial.
  destruct E; simp equiv_rec; try rewrite H0; trivial.
  destruct E; simp equiv_rec; try rewrite H0;
    try rewrite andb_false_r; trivial.
  destruct s; destruct t;
    simp equiv_rec; rewrite H0; try rewrite andb_false_r; trivial.
Qed.

(** Correction of the A checking case of equiv_rec *)

Lemma equiv_rec_A : forall C s t n,
      equiv_rec C (Fc 0 n s) (Fc 0 n t) =
      equiv_rec C (TPith 1 s 0 n) (TPith 1 t 0 n) &&
      equiv_rec C (TPithdel 1 (Fc 0 n s) 0 n) (TPithdel 1 (Fc 0 n t) 0 n).
Proof.
  intros. simp equiv_rec.
  rewrite eq_nat_refl; trivial.
Qed.


(** Correction of the iter function *)

Lemma iter_true : forall P i j, i <> 0 ->

    ((exists k, k >= i /\ k <= i + j - 1 /\ P k = true)
      <->
      iter P i j = true).

Proof.
  intros. gen i. induction j; intros; simpl. 
  split~; intro.
  case H0; clear H0; intros k H0.
  destruct H0. destruct H1.
  rewrite plus_0 in H1. unfold ge in H0.
  assert (Q : i <= i - 1).
  apply le_trans' with (l:=k); trivial.
  destruct i. false. simpl in Q.
  rewrite minus_0 in Q. apply Sn_le in Q. contradiction.   
  inverts H0.

  rewrite plus_com. simpl.
  rewrite plus_com. rewrite minus_0.

  gen_eq b : (P i); intro H0. destruct b. 
  split~; intro.

  exists i. repeat split~. apply le_plus.
  symmetry in H0. split~; intro H1.
  case H1; clear H1; intros k H1.
  destruct H1. destruct H2.

  gen_eq b : (eq_nat_rec i k); intro H4.
  symmetry in H4. destruct b.
  apply eq_nat_refl' in H4. rewrite H4 in H0.
  rewrite H0 in H3. inverts H3.
  apply eq_nat_diff in H4.
  unfold ge in H1.
  apply IHj. discriminate. exists k.
  simpl. rewrite minus_0. repeat split~.
  unfold ge. inverts H1. false.
  apply -> le_Sn; trivial.
  
  apply IHj in H1.
  case H1; clear H1; intros k H1.
  destruct H1. destruct H2.
  simpl in H2. rewrite minus_0 in H2.

  exists k.
  repeat split~. unfold ge in *|-*.
  apply le_S in H1. apply le_Sn; trivial.
  discriminate.
Qed.


(** Correction of the AC checking case of equiv_rec *)

Lemma equiv_rec_AC : forall C s t n,

      (exists i,
       equiv_rec C (TPith 1 s 1 n) (TPith i t 1 n) = true /\
       equiv_rec C (TPithdel 1 (Fc 1 n s) 1 n)
                   (TPithdel i (Fc 1 n t) 1 n) = true)

        <->

      equiv_rec C (Fc 1 n s) (Fc 1 n t) = true.  
Proof.      
  intros. simp equiv_rec.
  rewrite 2 eq_nat_refl.
  replace (true && true) with true; trivial.

  split~; intro H. case H; clear H; intros i H.
  destruct H.
  
  apply iter_true. discriminate.
  assert (Q : 1 <= TPlength t 1 n). apply TPlength_1_le.
  case (le_dec i 1); intro H1.
  exists 1. repeat split~. simpl. rewrite minus_0. trivial. 
  destruct i.
  rewrite TPith_0 in H. rewrite TPithdel_0 in H0.
  rewrite H. rewrite H0. simpl; trivial.  
  inverts H1. 
  rewrite H. rewrite H0. simpl; trivial.
  inverts H3. apply neg_le in H1.
  case (le_dec (TPlength t 1 n) i); intro H2.
  rewrite TPith_overflow with (i:=i) in H; trivial.
  rewrite TPithdel_overflow with (i:=i) in H0.
  exists (TPlength t 1 n). repeat split~; trivial. 
  simpl. rewrite minus_0; trivial.
  rewrite H. rewrite TPlength_Fc_eq in H0.
  rewrite H0. simpl; trivial.
  rewrite TPlength_Fc_eq. trivial.
  apply neg_le in H2.
  exists i. repeat split~.
  apply le_S in H1. apply le_Sn; trivial.
  simpl. rewrite minus_0; trivial.
  apply le_S in H2.  apply le_Sn; trivial.
  rewrite H. rewrite H0. simpl; trivial.

  apply iter_true in H.
  case H; clear H; intros k H.
  destruct H. destruct H0. exists k.
  symmetry in H1. apply andb_true_eq in H1.
  destruct H1. symmetry in H1. symmetry in H2.
  split~; trivial.
  discriminate.
Qed.  

(** Correction of the C checking case of equiv_rec *)

Lemma equiv_rec_C : forall C s0 s1 t0 t1 n,

       equiv_rec C (Fc 2 n (Pr s0 s1)) (Fc 2 n (Pr t0 t1)) = 

       equiv_rec C s0 t0 && equiv_rec C s1 t1 ||

       equiv_rec C s0 t1 && equiv_rec C s1 t0 .
Proof.
  intros. simp equiv_rec. rewrite 2 eq_nat_refl. simpl; trivial.
Qed.

Lemma equiv_rec_Su : forall C pi pi' X Y,
      equiv_rec C (Su pi X) (Su pi' Y) =
              eq_var_rec X Y &&
              sub_context_rec (fresh_context (disgr pi pi') X) C.
Proof.
  intros. simp equiv_rec.
Qed.

Hint Rewrite equiv_rec_Su : equiv.


(** Correctness of equiv_rec *)

Lemma equiv_rec_eq : forall C s t,
      C |- s ~aacc t <-> equiv_rec C s t = true.
Proof.
  intros. split~; intros.
  induction H; autorewrite with equiv; trivial.
  destruct a. simpl. rewrite eq_nat_refl. trivial.
  rewrite IHequiv1. rewrite IHequiv2. simpl. trivial.
  rewrite equiv_rec_Fc; trivial.
  rewrite equiv_rec_Ab_2; trivial.
  rewrite IHequiv. rewrite andb_true_r.

  apply fresh_rec_eq; trivial.

  destruct X. simpl. rewrite eq_nat_refl. simpl.

  apply sub_context_rec_correctness. intros c H0. destruct c.
  apply fresh_context_mem in H0. destruct H0.
  apply ds_eq_disgr in H1. rewrite <- H0.
  apply H; trivial.
  
  rewrite equiv_rec_A.
  rewrite 2 TPith_Fc_eq in IHequiv1.
  rewrite IHequiv1. rewrite IHequiv2. simpl; trivial.
  
  apply equiv_rec_AC.
  exists i. rewrite 2 TPith_Fc_eq in IHequiv1. split~.
  
  rewrite equiv_rec_C.
  rewrite IHequiv1. rewrite IHequiv2. simpl. trivial.

  rewrite equiv_rec_C.
  rewrite IHequiv1. rewrite IHequiv2. simpl.
  rewrite orb_true_r. trivial.

  gen_eq l : (term_size s); intro H0.
  gen H0 H. gen s t. induction l using peano_induction; intros.

  destruct s; destruct t;
    simp equiv_rec in H; inverts H1;
    simp equiv_rec in *|-; simpl in H0.

  apply equiv_Ut. 

  destruct a. destruct a0.
  simpl in H3. apply eq_nat_refl' in H3.
  rewrite H3. apply equiv_At.

  destruct a. destruct a0. simpl in H3.
  gen_eq b: (eq_nat_rec n n0); intro H2. destruct b.
  symmetry in H2. apply eq_nat_refl' in H2. rewrite H2.
  apply equiv_Ab_1. apply H with (m:=term_size s); trivial.
  rewrite H0. unfold lt. trivial.
  
  symmetry in H2. apply eq_nat_diff in H2.
  gen_eq b : (fresh_rec C (atom n) t); intro H4.
  destruct b. symmetry in H4.
  apply equiv_Ab_2. intro H5. inverts H5. false.
  apply H with (m:=term_size s); trivial.
  rewrite H0. unfold lt. trivial.
  apply fresh_rec_eq; trivial. inverts H3.

  assert (Q : equiv_rec C s1 t1 = true /\ equiv_rec C s2 t2 = true).
   gen_eq b : (equiv_rec C s1 t1); intro H4.
   destruct b. split~; trivial. inverts H3.
  destruct Q.
  apply H with (m:=term_size s1) in H1; try rewrite H0; trivial.
  apply H with (m:=term_size s2) in H2; try rewrite H0; trivial.
  apply equiv_Pr; trivial. 
  unfold lt. apply -> le_Sn. rewrite plus_com. apply le_plus.
  unfold lt. apply -> le_Sn. apply le_plus.

  rewrite equiv_rec_Fc_diff in H3; simpl.
  inversion H3. intro H2; trivial. 
  rewrite equiv_rec_Fc_diff in H3; simpl.
  inversion H3. intro H2; trivial. 
  rewrite equiv_rec_Fc_diff in H3; simpl.
  inversion H3. intro H2; trivial. 
  rewrite equiv_rec_Fc_diff in H3; simpl.
  inversion H3. intro H2; trivial.   

  case (nat_pair_eqdec (n, n0) (n1, n2)); intro H2.
  inverts H2.
  case (set_In_nat_dec n1 [0;1;2]); intro H2.
  simpl in H2. destruct H2; try rewrite <- H1 in *|-*. clear H1.

  rewrite equiv_rec_A in H3.
  symmetry in H3.  apply andb_true_eq in H3. destruct H3.
  symmetry in H1. symmetry in H2.
  apply equiv_A. left~.
  rewrite 2 TPith_Fc_eq.
  apply H with (m := term_size (TPith 1 s 0 n2)); trivial.
  assert (Q : term_size (TPith 1 s 0 n2) <= term_size s).
   apply term_size_TPith. rewrite H0. apply -> le_Sn; trivial.
  apply H with (m := term_size (TPithdel 1 (Fc 0 n2 s) 0 n2)); trivial.
  gen_eq b : (eq_nat_rec (TPlength s 0 n2) 1); intro H3.
  symmetry in H3. destruct b.
  rewrite eq_nat_refl' in H3.
  rewrite TPithdel_TPlength_1.
  assert (Q : 1 <= term_size s). apply term_size_1_le.
  rewrite H0. apply -> le_Sn; trivial.
  rewrite TPlength_Fc_eq; trivial.
  apply eq_nat_diff in H3.
  rewrite TPithdel_Fc_eq; trivial. simpl.
  assert (Q : term_size (TPithdel 1 s 0 n2) < term_size s).
   apply term_size_TPithdel; trivial.
  rewrite H0. apply -> le_Sn; trivial.

  destruct H1; try rewrite <- H1 in *|-*. clear H1.

  apply equiv_rec_AC in H3.
  case H3; clear H3; intros i H3. destruct H3.
  apply H with (m := term_size (TPith 1 s 1 n2)) in H1; trivial.
  apply H with (m := term_size (TPithdel 1 (Fc 1 n2 s) 1 n2)) in H2;
    trivial.
  
  apply equiv_AC with (i:=i); trivial. right~. left~.
  rewrite 2 TPith_Fc_eq; trivial.
  gen_eq b : (eq_nat_rec (TPlength s 1 n2) 1); intro H3.
  symmetry in H3. destruct b.
  rewrite eq_nat_refl' in H3.
  rewrite TPithdel_TPlength_1. simpl.  
  assert (Q : 1 <= term_size s). apply term_size_1_le.
  rewrite H0. apply -> le_Sn; trivial.
  rewrite TPlength_Fc_eq; trivial.
  apply eq_nat_diff in H3.  
  rewrite TPithdel_Fc_eq; trivial. simpl.
  assert (Q : term_size (TPithdel 1 s 1 n2) < term_size s).
   apply term_size_TPithdel; trivial.
  rewrite H0. apply -> le_Sn; trivial.
  assert (Q : term_size (TPith 1 s 1 n2) <= term_size s).
   apply term_size_TPith. rewrite H0. apply -> le_Sn; trivial.
  

  destruct H1; try contradiction; rewrite <- H1 in *|-*. clear H1.

  case (is_Pr_dec s); intro H4.
  case (is_Pr_dec t); intro H5.
  apply is_Pr_exists in H4.
  apply is_Pr_exists in H5. 
  case H4; clear H4; intros s0 H4.
  case H4; clear H4; intros s1 H4.
  case H5; clear H5; intros t0 H5.
  case H5; clear H5; intros t1 H5.
  rewrite H4 in *|-*. rewrite H5 in *|-*.
  clear H4 H5.
  rewrite equiv_rec_C in H3.
  apply orb_true_iff in H3.
  destruct H3; symmetry in H1;
    apply andb_true_eq in H1; destruct H1;
      symmetry in H1; symmetry in H2.
  simpl in H0. apply equiv_C1. right~. right~. left~.
  apply H with (m := term_size s0); trivial.
  rewrite H0. apply le_S. apply -> le_Sn. apply le_plus.
  apply H with (m := term_size s1); trivial.
  rewrite H0. apply le_S. apply -> le_Sn. rewrite plus_com. apply le_plus.  
  simpl in H0. apply equiv_C2. right~. right~. left~.
  apply H with (m := term_size s0); trivial.
  rewrite H0. apply le_S. apply -> le_Sn. apply le_plus.  
  apply H with (m := term_size s1); trivial.
  rewrite H0. apply le_S. apply -> le_Sn. rewrite plus_com. apply le_plus.
  rewrite equiv_rec_Fc in H3.    
  apply equiv_Fc. right~.
  apply H with (m := term_size s); trivial.
  rewrite H0. apply -> le_Sn; trivial.
  right~.
  rewrite equiv_rec_Fc in H3.    
  apply equiv_Fc. right~.
  apply H with (m := term_size s); trivial.
  rewrite H0. apply -> le_Sn; trivial.
  rewrite equiv_rec_Fc in H3.
  right~. right~.
  rewrite equiv_rec_Fc in H3. apply equiv_Fc. left~.
  apply H with (m:= term_size s); trivial.
  rewrite H0. apply -> le_Sn; trivial.  
  left~. rewrite equiv_rec_Fc_diff' in H3; trivial.
  inverts H3.
  
  rewrite equiv_rec_Fc_diff in H3; simpl.
  inversion H3. intro H2; trivial. 

  destruct v. destruct v0. simpl in H3.
  gen_eq b : (eq_nat_rec n n0); intro H2.
  symmetry in H2. destruct b.
  apply eq_nat_refl' in H2. rewrite H2 in *|-*.
  apply equiv_Su; intros.
  apply ds_eq_disgr in H1.
  gen_eq C0 : (fresh_context (disgr p p0) (var n0)); intro H4.
  apply sub_context_rec_correctness with (C:=C0) (C':=C); trivial.
  rewrite H4. apply fresh_context_mem. split~.

  inverts H3.

Qed.
