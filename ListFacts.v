(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : ListFacts.v
 Authors     : Washington Luís R. de Carvalho Segundo and
               Mauricio Ayala Rincón 
               Universidade de Brasília (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: Jun 23, 2018.
 ============================================================================
*)

Require Export List ListSet Omega LibTactics.

Notation "[]"    := nil  (at level 67). 
Notation "[ s ]" := (s::nil) (at level 67).


(** A useful induction principle *)

Lemma peano_induction :
 forall (P:nat->Prop),
   (forall n, (forall m, m < n -> P m) -> P n) ->
   (forall n, P n).
Proof.
  introv H. cuts* K: (forall n m, m < n -> P m).
  induction n; introv Le. inversion Le. apply H.
  intros. apply IHn. omega.
Qed.

Section ListFacts.

Variable A : Type.

Lemma In_nth : forall (l : list A) (a : A) d, In a l ->
      exists n, n < length l /\ nth n l d = a.
Proof.
   intros. gen a. induction l; intros.
   simpl in H; try contradiction.
   simpl in H. destruct H. exists 0.
   simpl. split~. try omega; trivial.   
   apply IHl in H. case H; clear H; intros n H.
   destruct H. exists (S n). simpl. split~; try omega; trivial.
Qed.

Lemma nth_0_exists_l' : forall (A : Set) (l : list A) (a : A) d,
   l <> [] -> exists l', l = (nth 0 l d)::l'.                 
Proof.
  intros. destruct l. false. 
  exists l. simpl; trivial.
Qed.


Hypothesis Aeq_dec : forall (a a': A), {a = a'} + {a <> a'}.


(** Additonal operators over lists: 
   remove_list, head_list and tail_list. *)

Fixpoint remove_list (L L': list A) : list A :=
  
  match L with

    | [] => L'
                
    | a::L0 => remove_list L0 (remove Aeq_dec a L') 

  end.


Fixpoint head_list (n : nat) (L : list A) : list A :=

  match n , L with
                                                              
  | 0 , _ => []

  | _ , [] => []             

  | S n0 , a :: L0 => a :: head_list n0 L0

  end.                      


Fixpoint tail_list (n : nat)  (L : list A) : list A :=

  match n , L with
                                                              
  | 0 , L => L

  | _ , [] => []             

  | S n0 , a :: L0 => tail_list n0 L0

  end.     


(** Additional lemmas about remove an element of a list *)

Lemma nil_eqdec : forall (l : list A), {l = []} + {l <> []}.
Proof.
  intros. destruct l. left~.
  right~. discriminate.
Qed.
  
Lemma remove_elim : forall (a b : A) (l : list A),    
                           In b (remove Aeq_dec a l) -> b <> a /\ In b l.
Proof.
  intros. induction l; simpl in *|-*; try contradiction.
  gen H. case (Aeq_dec a a0); intros.
  rewrite <- e in *|-*. clear e.
  apply IHl in H. destruct H. split~.
  simpl in H. destruct H. rewrite H in *|-*. clear H.
  split~. apply IHl in H. destruct H.
  split~.
Qed.

Lemma remove_eq : forall (a : A) (l : list A),  
                         ~ In a l -> remove Aeq_dec a l = l.
Proof.  
 intros. induction l; simpl; trivial.
 case (Aeq_dec a a0); intro H1.
 false. apply H. left~.
 assert (Q : ~ In a l). intro. apply H. right~. 
 apply IHl in Q. rewrite Q; trivial.
Qed.
  
Lemma remove_In_length : forall (a : A) (l : list A),
                          NoDup l -> In a l -> length (remove Aeq_dec a l) = length l - 1.
Proof.  
 intros. induction l; simpl; trivial.
 case (Aeq_dec a a0); intro H1.
 rewrite remove_eq; try omega.
 apply NoDup_cons_iff. rewrite H1. trivial.
 simpl. simpl in H0. destruct H0.
 symmetry in H0. contradiction.
 assert (Q : length (remove Aeq_dec a l) = length l - 1).
  apply IHl; trivial. apply NoDup_cons_iff with (a:=a0); trivial.
  assert (Q' : length l > 0).
  destruct l. simpl in H1. contradiction.
  simpl; try omega. omega.
Qed.  

Lemma remove_eq_set_remove : forall (l : list A) (a : A),
 NoDup l -> remove Aeq_dec a l = set_remove Aeq_dec a l.                               
Proof.
  intros. induction l; simpl.
  unfold empty_set. trivial.
  case (Aeq_dec a a0); intro H0.
  assert (Q : ~ In a l).
   apply NoDup_cons_iff.
   rewrite H0. apply H.
   rewrite remove_eq; trivial.
  rewrite IHl; trivial.
  apply NoDup_cons_iff with (a:=a0); trivial.
Qed.

Lemma NoDup_remove_3 : forall a l, NoDup l -> NoDup (remove Aeq_dec a l).
Proof.
  intros. induction l; simpl; trivial.
  case (Aeq_dec a a0); intro H0.
  apply IHl. apply NoDup_cons_iff with (a:=a0); trivial.
  apply NoDup_cons. intro H1.
  apply remove_elim in H1. destruct H1.
  apply NoDup_cons_iff in H. destruct H. contradiction.
  apply IHl. apply NoDup_cons_iff with (a:=a0); trivial.
Qed.
  
(** Comparing size of lists that do not have redundancies *)

Lemma subset_list : forall (l l' : list A),
      NoDup l  ->                     
     (forall b, In b l -> In b l') ->             
     length l <= length l' .
Proof.
  intros. 
  gen_eq n0 : (length l).
  gen_eq n1 : (length l').
  gen l l' n0.
  induction n1 using peano_induction; intros.

  destruct l'; destruct l; simpl in H2; simpl in H3;
  rewrite H2; rewrite H3;  try omega.
  false. apply (H1 a). left~.

  assert (Q : n0 - 1 <= n1 - 1).

  case (Aeq_dec a a0); intro H4. rewrite <- H4 in *|-. clear H4.
  apply H with (l:=l) (l':=l'); intros; try omega.
  apply NoDup_cons_iff with (a:=a); trivial. 
  case (Aeq_dec b a); intro H5.
  assert (Q: ~ In b l).
   apply NoDup_cons_iff. rewrite H5; trivial.   
  contradiction.
  case (H1 b). simpl. right~.
  intro. symmetry in H6. contradiction.
  intro. trivial.

  case (in_dec Aeq_dec a l); intro Q. 
  
  apply H with (l := remove Aeq_dec a (a0 :: l)) (l' := l');
  intros; try omega. apply NoDup_remove_3; trivial.
  apply remove_elim in H5. destruct H5.
  apply H1 in H6. simpl in H6.
  destruct H6; trivial. symmetry in H6.
  contradiction.

  rewrite remove_In_length;
  simpl length; try omega; trivial.
  right~.

  apply H with (l:=l) (l':=l'); intros; try omega.
  apply NoDup_cons_iff with (a:=a0); trivial.
  case (Aeq_dec b a); intro H6. rewrite H6 in H5. contradiction.
  assert (Q' :  In b (a :: l')). apply H1. right~.
  simpl in Q'. destruct Q'; trivial.
  symmetry in H7. contradiction.
  
 omega. 
  
Qed.


Lemma subset_list' : forall (l l' : list A),
     NoDup l ->                     
     (forall b, In b l -> In b l') ->
     (exists a', In a' l' /\ ~ In a' l) ->
     length l < length l' .
Proof.
  intros. case H1; clear H1; intros a' H1. destruct H1.
  assert (Q : length (a'::l) <= length l').
  apply subset_list. apply NoDup_cons; trivial.
  intros. simpl in H3. destruct H3. rewrite <- H3; trivial.
  apply H0; trivial. simpl in Q. omega.
Qed.


Lemma subset_list_eq : forall (l l' : list A),
      NoDup l -> NoDup l' ->                     
     (forall b, In b l <-> In b l') ->             
     length l = length l' .
Proof.
  intros. 
  assert (Q : length l <= length l').
   apply subset_list; trivial; intros.
   apply H1; trivial.
  assert (Q' : length l' <= length l).
   apply subset_list; trivial; intros.
   apply H1; trivial.

  omega.
   
Qed.


Lemma subset_list_eq' : forall (l l' : list A),
    NoDup l -> NoDup l' ->
    length l = length l' ->                  
    (forall b, In b l -> In b l') ->
    (forall b, In b l' -> In b l) .
Proof.
  intros.
  case (set_In_dec Aeq_dec b l); intro H4; trivial.  
  apply subset_list' in H2; trivial.
  omega. exists b. split~.   
Qed.


Lemma remove_list_nil: forall (L : list A),
      remove_list L ([]) = [] .
Proof.
  intros. induction L; simpl; trivial.
Qed.  

Lemma remove_list_overflow : forall (L L' : list A),
      (forall a, In a L' -> In a L) ->
      remove_list L L' = []. 
Proof.
  intros. gen_eq l : (length L); intro H1.
  gen L L'. induction l using peano_induction; intros.
  destruct L; simpl in *|-*; trivial.
  destruct L'; trivial.
  false. apply (H0 a). left~.
  apply H with (m := length L); try omega; intros.
  apply remove_elim in H2. destruct H2.
  apply H0 in H3. destruct H3; trivial.
  symmetry in H3. contradiction.
Qed.

(** Additional lemmas for naturals numbers *)

Lemma nat_leq_inv : forall m n, n <= m -> m >= n.
Proof. intros; omega. Qed.

Lemma nat_lt_inv : forall m n, n < m -> m > n.
Proof. intros; omega. Qed.


(** Additional lemmas for sets represented by lists *)

  Lemma set_add_iff : forall (a b : A) (l : list A),
                      In a (set_add Aeq_dec b l) <-> a = b \/ In a l.
  Proof.
  split~. apply set_add_elim. apply set_add_intro.
  Qed.

  Lemma set_union_iff : forall (a : A) (l l': list A),
                        In a (set_union Aeq_dec l l') <-> In a l \/ In a l'.
  Proof.
    split~. apply set_union_elim. apply set_union_intro.
  Qed.

  Lemma set_remove_add : forall (a b : A) (l : list A),
        In a (set_remove Aeq_dec b (set_add Aeq_dec b l)) -> In a l.                                            
  Proof.
    intros. induction l; simpl in H. gen H.
    case (Aeq_dec b b); intros; trivial. false.
    gen H. case (Aeq_dec b a0); intros.
    simpl in H. gen H.
    case (Aeq_dec b a0); intros;
     try contradiction. right~.    
    simpl in H. gen H.
    case (Aeq_dec b a0); intros;
     try contradiction.
    simpl in H. destruct H. left~. right~.
  Qed.


  Lemma set_remove_add' : forall (a b : A) (l : list A),
      a <> b ->
      set_remove Aeq_dec a (set_add Aeq_dec b l) =
      set_add Aeq_dec b (set_remove Aeq_dec a l).
  Proof.
    intros. induction l; simpl.
    case (Aeq_dec a b); intro H0. contradiction. fequals.
    case (Aeq_dec b a0); case (Aeq_dec a a0); intros H0 H1.
    rewrite <- H1 in H0. contradiction.
    simpl. case (Aeq_dec b a0); case (Aeq_dec a a0); intros H2 H3;
    try contradiction; trivial. 
    simpl. case (Aeq_dec a a0); intro H2; try contradiction; trivial.
    simpl. case (Aeq_dec b a0); case (Aeq_dec a a0); intros H2 H3;
             try contradiction. rewrite IHl. trivial.
  Qed.   
    
 Lemma set_In_nil : forall (l : list A), l = [] <-> (forall a, ~ set_In a l).  
 Proof.
   intros. split~; intros.
   rewrite H. intro H'. simpl in H'. trivial.
   induction l; trivial.
   false. apply (H a). simpl.
   left~.
 Qed.   
   
 Lemma set_inter_nil : forall (l l' : list A),
       set_inter Aeq_dec l l' = [] <-> (forall a, ~ set_In a (set_inter Aeq_dec l l')).
 Proof.  
   intros. split~; intros.
   rewrite H. simpl. intro; trivial.
   induction l; simpl in *|-*; trivial.
   gen H. case (set_mem Aeq_dec a l'); intros.
   assert (Q : ~ set_In a (a :: set_inter Aeq_dec l l')). apply H.
   false. apply Q. left~.
   apply IHl; intros. apply H.
 Qed.

 Lemma set_add_not_In : forall (l : list A) (a : A),
                        ~ set_In a l -> set_add Aeq_dec a l  = l++[a].
 Proof.
   intros. induction l; simpl; trivial.
   case (Aeq_dec a a0); intro H0.
   false. apply H. left~.
   fequals. apply IHl. intro H1.
   apply H. right~.
 Qed.

 Lemma set_add_In : forall (l : list A) (a : A),
                    set_In a l -> set_add Aeq_dec a l  = l.
 Proof.
   intros. induction l; simpl in H|-*; try contradiction.
   destruct H. rewrite H.
   case (Aeq_dec a a); intro H0; trivial. false.
   case (Aeq_dec a a0); intro H0; trivial.
   rewrite IHl; trivial.
 Qed.

 Lemma set_remove_eq : forall (l : list A) (a : A),
                         ~ set_In a l -> set_remove Aeq_dec a l  = l.
 Proof.
   intros. induction l; simpl; trivial.
   case (Aeq_dec a a0); intro H1.
   false. apply H. left~.
   rewrite IHl; trivial.
   intro H2. apply H. right~.
 Qed.  

 Lemma set_remove_comm : forall (l : list A) (a b : A),
       set_remove Aeq_dec a (set_remove Aeq_dec b l)  =                    
       set_remove Aeq_dec b (set_remove Aeq_dec a l) .
 Proof.
   intros. induction l; simpl; trivial.
   case (Aeq_dec b a0); case (Aeq_dec a a0); simpl; intros H H0.
   rewrite H. rewrite H0. trivial.
   case (Aeq_dec b a0); intro H1; try contradiction; trivial.
   case (Aeq_dec a a0); intro H1; try contradiction; trivial.
   case (Aeq_dec a a0); case (Aeq_dec b a0); intros H1 H2;
   try contradiction; trivial.
   rewrite IHl. trivial.
 Qed.



 (** Lemmas about head_list and tail_list *)


Lemma head_list_not_nil : forall (L : list A) (n : nat),

     n <> 0 -> length L > 0 ->

     head_list n L <> [] .
Proof.
  intros. 
  destruct L; simpl in *|-*. omega.
  destruct n; simpl. false.
  discriminate.
Qed.  


Lemma head_list_length : forall (L : list A) (n : nat),
      n <= length L ->
      length (head_list n L) = n.
Proof.
  intros. gen_eq l : (length L); intro H0.
  gen H0 H. gen n L. induction l using peano_induction; intros.
  destruct L; simpl in *|-*.
  assert (Q : n = 0). omega. rewrite Q. simpl; trivial.
  destruct n. simpl. trivial.
  simpl. rewrite H with (m := length L); omega.
Qed.  

Lemma tail_list_length : forall (L : list A) (n : nat),
      n <= length L ->
      length (tail_list n L) = length L - n.
Proof.
  intros. gen_eq l : (length L); intro H0.
  gen H0 H. gen n L. induction l using peano_induction; intros.
  destruct L; simpl in *|-*.
  assert (Q : n = 0). omega. rewrite Q. simpl; omega.
  destruct n. simpl. omega.
  simpl. rewrite H with (m := length L); omega.
Qed.  


Lemma head_tail_append : forall (L L0 L1 : list A) (n : nat),
      L0 = head_list n L ->
      L1 = tail_list n L ->
      L = L0 ++ L1 .
Proof.
  intros. gen_eq l : (length L); intro H1.
  gen H1 H H0. gen L L0 L1 n.
  induction l using peano_induction; intros.
  destruct L. destruct n; simpl in *|-.
  rewrite H0. rewrite H2. simpl; trivial.
  rewrite H0. rewrite H2. simpl; trivial.
  destruct n; simpl in *|-.
  rewrite H0. rewrite H2. simpl; trivial.
  rewrite H0. simpl. fequals. rewrite H2.
  apply H with (m := length L) (n:=n); try omega; trivial.
Qed.
  

End ListFacts.    


