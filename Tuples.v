(***************************************************************************
 * Tuples.v                						   *		
***************************************************************************)

Require Import Perm.


(** Computes the lenght of a tuple regarding the nth AC function symbol *)

Fixpoint TPlength (t: term) (m n: nat) : nat :=
match t with 
 | (<|t1,t2|>)  => (TPlength t1 m n) + (TPlength t2 m n) 
 | (Fc m1 n1 t1)  => if m1 === m then
                     if n1 === n then (TPlength t1 m n)
                     else 1 else 1
 | _ => 1  
end.

(** Computes the ith argument from the tuple t, 
   argument of the nth AC function symbol 
   It is assumed that i was previously computed such that 1 <= i <= (TPlength t m n).
   If i = 0 or i > (TPlength t m n) then the result is "<<>>" 
 *)

Fixpoint TPith (i: nat) (t: term) (m n: nat) : term :=
  match t with 

   |  (<|t1,t2|>) => let l1 :=  (TPlength t1 m n) in 
                         if (le_dec i l1) then (TPith i t1 m n)
                         else (TPith (i - l1) t2 m n)

   | (Fc m1 n1 t1) => let l1 :=  (TPlength t m n) in 
                         if i === 0 then (<<>>) else
                          if (le_dec i l1) then 
                             (if m1 === m then 
                                if n1 === n then (TPith i t1 m n) 
                                else t
                              else t)
                          else (<<>>)

   | _  => if (i === 1) then t else (<<>>) 
end.


(** Eliminates the ith argument in the tuple t, argument of the AC operator n 
    It is assumed that i was previously computed such that 
    1 <= i <= (TPlength t m n)
   
   If i = 0 or i > (TPlength t m n) then the result is "t" 
 *)

Fixpoint TPithdel (i: nat) (t: term) (m n: nat) : term :=
  match t with 

   | (<|t1,t2|>) => let l1 := (TPlength t1 m n) in 
                      let l2 := (TPlength t2 m n) in 
                       if i === 0 then t else 
                        if (le_dec i l1) then 
                         (if (l1 === 1) then t2 
                         else (<|(TPithdel i t1 m n),t2|>))
                        else
                         let ii := (i - l1) in
                         if (le_dec ii l2) then
                          (if (l2 === 1) then t1
                          else (<|t1,(TPithdel ii t2 m n)|>)) 
                         else t (* unexpected case: i > (TPlength t n) *)

   | (Fc m1 n1 t1) =>  let  l := (TPlength t m n) in 
                       if i === 0 then t else (* unexpected case: i = 0 *)
                        if (le_dec i l) then
                         (if m1 === m then 
                           if n1 === n then 
                            if (l === 1) then (<<>>) else 
                             (Fc m1 n1 (TPithdel i t1 m n)) 
                           else (<<>>) 
                          else (<<>>))
                        else t (* unexpected case: i > (TPlength t n) *)  

   | _ => if i === 1 then (<<>>) else t
end.


(** i-applications of a (Fc m n) function symbol *)

Fixpoint Fc_app (i m n: nat) (t : term)  : term :=
match i with
  | 0 => t
  | S i0 => Fc m n (Fc_app i0 m n t)
end.
   

Fixpoint rem_Fc_app (t : term) (m n : nat): term :=
match t with 
  | Fc m1 n1 t1 => if m1 === m then 
                        if n1 === n then (rem_Fc_app t1 m n)
                        else t
                   else t
  | _ => t
end.


(* TPlength properties *)

Lemma TPlength_geq_1 : forall t m n, TPlength t m n >= 1.
Proof. intros; induction t; simpl; repeat case_nat; omega. Qed.

Hint Resolve TPlength_geq_1.

Lemma TPlength_Pr_neq_1 : forall t1 t2 m n, TPlength (<|t1,t2|>) m n <> 1.
Proof.
 intros. simpl.
 assert (TPlength t1 m n >= 1). apply TPlength_geq_1.
 assert (TPlength t2 m n >= 1). apply TPlength_geq_1.
 omega.
Qed.

Hint Resolve TPlength_Pr_neq_1.

Lemma TPlength_Fc_eq : forall m n t,  TPlength (Fc m n t) m n = TPlength t m n.
Proof. intros; simpl; repeat case_nat; trivial. Qed.

Hint Rewrite TPlength_Fc_eq : tuples.

Lemma TPlength_Fc_diff_m : forall m m' n n' t, m <> m' -> 
 TPlength (Fc m n t) m' n' = 1.
Proof. intros; simpl; repeat case_nat; trivial. Qed.

Hint Resolve TPlength_Fc_diff_m.

Lemma TPlength_Fc_diff_n : forall m m' n n' t, n <> n' -> 
 TPlength (Fc m n t) m' n' = 1.
Proof. intros; simpl; repeat case_nat; trivial. Qed.

Hint Resolve TPlength_Fc_diff_n.

Lemma TPlength_Fc_TPlength_1 : forall m m' n n' t,
 TPlength t m' n' = 1 -> TPlength (Fc m n t) m' n' = 1. 
Proof.
 intros. case (m === m'); case (n === n'); intros H1 H2; auto.
 rewrite H1. rewrite H2. autorewrite with tuples; trivial.
Qed.

Hint Resolve TPlength_Fc_TPlength_1.

Lemma TPlength_TPith : forall t m n i, TPlength (TPith i t m n) m n = 1.
Proof.
 intros t m n. induction t; simpl; intros;
 repeat case_nat; simpl; trivial; 
 try case (le_dec i (TPlength t1 m n)); auto.
 case (le_dec i (TPlength t m n)); auto.
 case (le_dec i 1); auto; intro. 
 case (le_dec i 1); auto; intro. 
Qed.

Hint Rewrite TPlength_TPith : tuples.

Lemma Perm_TPlength : forall t m n pi, 
 TPlength (pi @@ t) m n = TPlength t m n. 
Proof.
 intros. induction t; autorewrite with perm; trivial.
 simpl. rewrite IHt1. rewrite IHt2. trivial.
 case (n0 === m); case (n1 === n); intros H0 H1.
 rewrite H0. rewrite H1. autorewrite with tuples. trivial.
 rewrite 2 TPlength_Fc_diff_n; trivial.
 rewrite 2 TPlength_Fc_diff_m; trivial.
 rewrite 2 TPlength_Fc_diff_m; trivial.
Qed.

Hint Rewrite Perm_TPlength : tuples.

(** TPith properties *)

Lemma TPith_0 : forall t m n, TPith 0 t m n = <<>>.
Proof. intros; induction t; simpl; trivial. Qed.

Hint Rewrite TPith_0 : tuples.

Lemma TPith_Pr_le : forall i t1 t2 m n, 
 i <= TPlength t1 m n -> TPith i (<|t1,t2|>) m n = TPith i t1 m n. 
Proof.
 intros; simpl; 
 case (le_dec i (TPlength t1 m n)); 
 intro H0; try contradiction; trivial. 
Qed.

Hint Resolve TPith_Pr_le.

Lemma TPith_Pr_gt : forall i t1 t2 m n,
 i >  TPlength t1 m n -> 
 TPith i (<|t1,t2|>) m n = TPith (i - (TPlength t1 m n)) t2 m n.
Proof.
 intros; simpl; 
 case (le_dec i (TPlength t1 m n)); intro H0; trivial. 
 apply False_ind. omega.
Qed.

Hint Resolve TPith_Pr_gt.

Lemma TPith_overflow : forall m n i t, i > (TPlength t m n) ->
                          TPith i t m n = <<>>.
Proof.
 introv. gen i. assert (Q: ~ 1 > 1). omega.
 induction t; simpl; introv; 
 repeat case_nat; intro H; auto.
 false; omega. false; omega.
 rewrite IHt1; try rewrite IHt2; try omega.
 case (le_dec i (TPlength t1 m n)); intro; trivial.
 case (le_dec i (TPlength t m n)); intro; auto.
 case (le_dec i 1); intro; trivial. apply False_ind. omega. 
 case (le_dec i 1); intro; trivial. apply False_ind. omega.  
 false; omega.
Qed.

Hint Resolve TPith_overflow.

Lemma TPith_Fc_eq : forall i t m n, TPith i (Fc m n t) m n = TPith i t m n. 
Proof.
 intros. simpl; repeat case_nat. 
 rewrite TPith_0; trivial. 
 case (le_dec i (TPlength t m n)); intro; trivial.
 rewrite TPith_overflow; try omega; trivial.
Qed.

Hint Rewrite TPith_Fc_eq : tuples.

Lemma TPith_Fc_diff_m : forall i t m m' n n', i <> 0 -> i <= 1 -> m <> m' ->
 TPith i (Fc m n t) m' n' = Fc m n t. 
Proof.
 intros. simpl; repeat case_nat.
 case (le_dec i 1); intro; try contradiction; trivial.
Qed.

Hint Resolve TPith_Fc_diff_m.

Lemma TPith_Fc_diff_n : forall i t m m' n n', i <> 0 -> i <= 1 -> n <> n' ->
 TPith i (Fc m n t) m' n' = Fc m n t. 
Proof.
 intros. simpl; repeat case_nat.
 case (le_dec i 1); intro; try contradiction; trivial.
 case (le_dec i 1); intro; try contradiction; trivial.
Qed.

Hint Resolve TPith_Fc_diff_n.


Lemma Perm_TPith : forall t pi m n i,
 pi @ (TPith i t m n) = TPith i (pi @ t) m n.
Proof.
 intros. gen i. induction t; intros; autorewrite with perm. 
 simpl. case_nat; autorewrite with perm; trivial.
 simpl. case_nat; autorewrite with perm; trivial.
 simpl. case_nat; autorewrite with perm; trivial. Focus 3.
 simpl. case_nat; autorewrite with perm; trivial.
 case (le_dec i (TPlength t1 m n)); intro H0.
 rewrite 2 TPith_Pr_le; autorewrite with tuples; trivial.
 rewrite 2 TPith_Pr_gt; autorewrite with tuples; try omega; trivial.
 case (i === 0); intro H0. rewrite H0. autorewrite with perm tuples; trivial.
 case (le_dec i (TPlength (Fc n0 n1 t) m n)); intro H1.
 case (n0 === m); case (n1 === n); intros H3 H4.
 rewrite H3. rewrite H4. autorewrite with tuples. trivial.
 rewrite TPlength_Fc_diff_n in H1; trivial. 
 rewrite 2 TPith_Fc_diff_n; trivial.
 autorewrite with perm; trivial. 
 rewrite TPlength_Fc_diff_m in H1; trivial. 
 rewrite 2 TPith_Fc_diff_m; trivial.
 autorewrite with perm; trivial.
 rewrite TPlength_Fc_diff_m in H1; trivial. 
 rewrite 2 TPith_Fc_diff_m; trivial.
 autorewrite with perm; trivial.
 rewrite 2 TPith_overflow; autorewrite with perm; try omega; trivial.
 gen H1. simpl; repeat case_nat; intro; autorewrite with perm tuples; try omega.
Qed.


(** TPithdel properties *)

Lemma TPithdel_0 : forall m n t, TPithdel 0 t m n = t.
Proof. intros. induction t; intros; simpl; trivial. Qed.

Hint Rewrite TPithdel_0 : tuples.

Lemma TPithdel_TPlength_1 : forall m n t, 
 TPlength t m n = 1 -> TPithdel 1 t m n = <<>>.
Proof.
 intros. destruct t; simpl; trivial. 
 apply False_ind. generalize H. apply TPlength_Pr_neq_1.
 repeat case_nat. case (le_dec 1 (TPlength t m n)); intro H0; trivial.
 apply False_ind. omega.
 autorewrite with tuples in H. contradiction.
 case (le_dec 1 1); intro H'; trivial. apply False_ind. auto.
 case (le_dec 1 1); intro H'; trivial. apply False_ind. auto.
Qed.

Hint Resolve TPithdel_TPlength_1.

Lemma TPithdel_Fc_eq : forall i t m n, 
 i > 0 ->
 i <= TPlength t m n ->
 TPlength t m n <> 1 ->
 TPithdel i (Fc m n t) m n = Fc m n (TPithdel i t m n).
Proof. 
 intros; simpl; repeat case_nat; trivial. 
 apply False_ind. omega. contradiction.
 case (le_dec i (TPlength t m n)); try contradiction; trivial.
Qed.

Hint Resolve TPithdel_Fc_eq.

Lemma TPithdel_1_Fc_diff_m : forall t m m' n n', m <> m' ->
 TPithdel 1 (Fc m n t) m' n' = <<>>.
Proof.
 intros. rewrite TPithdel_TPlength_1; auto.
Qed.

Hint Resolve TPithdel_1_Fc_diff_m.

Lemma TPithdel_1_Fc_diff_n : forall t m m' n n', n <> n' ->
 TPithdel 1 (Fc m n t) m' n' = <<>>.
Proof.
 intros. rewrite TPithdel_TPlength_1; auto.
Qed.

Hint Resolve TPithdel_1_Fc_diff_n.

Lemma TPithdel_Fc_diff_m : forall i t m m' n n', m <> m' ->
 i <> 1 -> TPithdel i (Fc m n t) m' n' = Fc m n t.
Proof.
 intros. simpl. repeat case_nat; trivial.
 case (le_dec i 1); intro H1; trivial. 
 apply False_ind. omega.
Qed.

Hint Resolve TPithdel_Fc_diff_m. 

Lemma TPithdel_Fc_diff_n : forall i t m m' n n', n <> n' ->
 i <> 1 -> TPithdel i (Fc m n t) m' n' = Fc m n t.
Proof.
 intros. simpl. repeat case_nat; trivial.
 case (le_dec i 1); intro H1; trivial. 
 apply False_ind. omega.
 case (le_dec i 1); intro H1; trivial. 
 apply False_ind. omega.
Qed.

Hint Resolve TPithdel_Fc_diff_n.

Lemma TPithdel_t1_Pr : forall t1 t2 m n, 
 TPlength t1 m n = 1 ->
 TPithdel 1 (<|t1,t2|>) m n = t2. 
Proof.
 intros; simpl. rewrite H.
 case (le_dec 1 1); intro H0. case_nat; trivial.
 apply False_ind. omega.
Qed.

Hint Resolve TPithdel_t1_Pr.

Lemma TPithdel_t2_Pr : forall t1 t2 m n, 
 TPlength t2 m n = 1 ->
 TPithdel (TPlength t1 m n + 1) (<|t1,t2|>) m n = t1. 
Proof.
 intros; simpl. rewrite H.
 case_nat. assert (TPlength t1 m n >= 1). auto.
 apply False_ind. omega.
 case (le_dec (TPlength t1 m n + 1) (TPlength t1 m n)); intro H0.
 apply False_ind. omega.
 case (le_dec (TPlength t1 m n + 1 - TPlength t1 m n) 1); intro H1.
 case_nat; trivial. apply False_ind. omega.
Qed.

Hint Resolve TPithdel_t2_Pr.

Lemma TPithdel_Pr_le : forall i t1 t2 m n, 
 i > 0 ->
 i <= TPlength t1 m n ->
 TPlength t1 m n <> 1 ->
 TPithdel i (<|t1,t2|>) m n = <|(TPithdel i t1 m n),t2|>. 
Proof.
 intros; simpl. case_nat. apply False_ind. omega.
 case (le_dec i (TPlength t1 m n)); intro H2; try contradiction. 
 case_nat; try contradiction; trivial.
Qed.  

Hint Resolve TPithdel_Pr_le.

Lemma TPithdel_Pr_gt : forall i t1 t2 m n, 
 i > TPlength t1 m n ->
 i <=  TPlength t1 m n + TPlength t2 m n ->
 TPlength t2 m n <> 1 ->
 TPithdel i (<|t1,t2|>) m n = <|t1,(TPithdel (i - TPlength t1 m n) t2 m n)|>. 
Proof.
 intros; simpl. case_nat. apply False_ind. omega.
 case (le_dec i (TPlength t1 m n)); intro H2.
 apply False_ind. omega. 
 case (le_dec (i - TPlength t1 m n) (TPlength t2 m n)); intro H3.
 case_nat; trivial. contradiction. apply False_ind. omega.
Qed.

Hint Resolve TPithdel_Pr_gt.

Lemma TPithdel_overflow : forall m n t i, 
 i > TPlength t m n -> TPithdel i t m n = t.
Proof.
 intros. destruct t.
 simpl; case_nat; trivial. 
 simpl in *|-*; case_nat; trivial. apply False_ind. omega.
 simpl in *|-*; case_nat; trivial. apply False_ind. omega.
 simpl in *|-*; case_nat; trivial. case (le_dec i (TPlength t1 m n)); intro.
 apply False_ind. omega. 
 case (le_dec (i - TPlength t1 m n) (TPlength t2 m n)); intro; trivial.
 apply False_ind; omega. 
 case (n0 === m); case (n1 === n); intros H0 H1.
 rewrite H0 in *|-*. rewrite H1 in *|-*. 
 autorewrite with tuples in H. 
 simpl; repeat case_nat; trivial. rewrite e1 in *|-*.
 case (le_dec i 1); intro H1; trivial. apply False_ind. omega.
 case (le_dec i (TPlength t n0 n1)); intro H2; trivial. 
 apply False_ind. omega. 
 rewrite TPlength_Fc_diff_n in H; trivial.
 rewrite TPithdel_Fc_diff_n; try omega; trivial.
 rewrite TPlength_Fc_diff_m in H; trivial.
 rewrite TPithdel_Fc_diff_m; try omega; trivial.
 rewrite TPlength_Fc_diff_m in H; trivial.
 rewrite TPithdel_Fc_diff_m; try omega; trivial.
 simpl in *|-*; case_nat; trivial.  apply False_ind. omega.
Qed.

Hint Resolve TPithdel_overflow.

Lemma TPlength_TPithdel : forall m n i t,
 i > 0 -> i <= (TPlength t m n) -> 
 (TPlength t m n) <> 1 -> 
 TPlength (TPithdel i t m n) m n = (TPlength t m n) - 1.
Proof.
 introv. gen i. induction t; intros.
 simpl in *|-*. apply False_ind. omega.
 simpl in *|-*. apply False_ind. omega.
 simpl in *|-*. apply False_ind. omega. Focus 3.
 simpl in *|-*. apply False_ind. omega.
 case (le_dec i (TPlength t1 m n)); intro H2.
 case ((TPlength t1 m n) === 1); intro H3. assert (i = 1). omega.
 rewrite H4. rewrite TPithdel_t1_Pr; trivial. simpl; omega.
 rewrite TPithdel_Pr_le; try omega. simpl. rewrite IHt1; omega.
 case ((TPlength t2 m n) === 1); intro H3. simpl in H0. 
 assert (i = TPlength t1 m n + 1). omega. rewrite H4.
 rewrite TPithdel_t2_Pr; trivial. simpl. omega. simpl in H0.
 rewrite TPithdel_Pr_gt; try omega. simpl. rewrite IHt2; omega.
 case (n0 === m); case (n1 === n); intros H2 H3.
 rewrite H2 in *|-*. rewrite H3 in *|-*.
 autorewrite with tuples in *|-. rewrite TPithdel_Fc_eq; trivial.
 autorewrite with tuples. apply IHt; trivial.
 rewrite TPlength_Fc_diff_n in *|-; trivial. apply False_ind. omega.
 rewrite TPlength_Fc_diff_m in *|-; trivial. apply False_ind. omega.
 rewrite TPlength_Fc_diff_m in *|-; trivial. apply False_ind. omega.
Qed.

Hint Resolve TPlength_TPithdel.

Lemma TPith_TPithdel_lt : forall t m n i0 i1,
 i0 < i1 -> i0 > 0 -> i1 > 0 -> i1 <= TPlength t m n ->  
 TPith i0 (TPithdel i1 t m n) m n = TPith i0 t m n.
Proof.
 intros t m n. induction t; intros; simpl in H2. 
 apply False_ind; omega. apply False_ind; omega.
 apply False_ind; omega. Focus 3.  apply False_ind; omega.
 
 case (le_dec i1 (TPlength t1 m n)); intro H3.
 rewrite TPithdel_Pr_le; try omega; trivial. 
 repeat rewrite TPith_Pr_le; try omega.
 apply IHt1; trivial. rewrite TPlength_TPithdel; try omega.
 case (TPlength t2 m n === 1); intro H4. 
 assert (i1 = TPlength t1 m n + 1). omega. rewrite H5.
 rewrite TPithdel_t2_Pr; trivial.  rewrite TPith_Pr_le; try omega; trivial.
 rewrite TPithdel_Pr_gt; try omega. 
 case (le_dec i0 (TPlength t1 m n)); intro H5. 
 repeat rewrite TPith_Pr_le; trivial. repeat rewrite TPith_Pr_gt; try omega.
 apply IHt2; omega.

 gen H2. case (n0 === m); case (n1 === n); intros H2 H3 H4.
 rewrite H2. rewrite H3. rewrite TPithdel_Fc_eq; try omega.
 rewrite 2 TPith_Fc_eq. apply IHt; trivial.
 apply False_ind; omega. apply False_ind; omega.
 apply False_ind; omega.
Qed.

Hint Resolve TPith_TPithdel_lt.

Lemma TPith_TPithdel_geq : forall t m n i0 i1,
 i0 >= i1 -> i0 > 0 -> i1 > 0 -> i0 <= TPlength t m n - 1 ->  
 TPith i0 (TPithdel i1 t m n) m n = TPith (i0 + 1) t m n.
Proof.
 intros t m n. induction t; intros; simpl in H2. 
 apply False_ind; omega. apply False_ind; omega.
 apply False_ind; omega. Focus 3.  apply False_ind; omega.
 
 case (le_dec i1 (TPlength t1 m n)); intro H3.
 case (TPlength t1 m n === 1); intro H4.
 assert (i1 = 1); try omega. rewrite H5. 
 rewrite TPithdel_t1_Pr; trivial.
 rewrite TPith_Pr_gt; try omega. rewrite H4. 
 replace (i0 + 1 -1) with i0; try omega; trivial.
 rewrite TPithdel_Pr_le; trivial.
 case (le_dec i0 ((TPlength t1 m n) - 1)); intro H5.
 rewrite 2 TPith_Pr_le; try omega; trivial. 
 apply IHt1; trivial. rewrite TPlength_TPithdel; omega.
 rewrite 2 TPith_Pr_gt; try omega; 
 try rewrite TPlength_TPithdel; try omega. 
 replace (i0 - (TPlength t1 m n - 1)) with 
         (i0 + 1 - TPlength t1 m n); try omega; trivial.
 rewrite TPithdel_Pr_gt; try omega. rewrite 2 TPith_Pr_gt; try omega.
 replace (i0 + 1 - TPlength t1 m n) with (i0 - TPlength t1 m n + 1); try omega.
 apply IHt2; omega.

 gen H2. case (n0 === m); case (n1 === n); intros H2 H3 H4.
 rewrite H2. rewrite H3. rewrite TPithdel_Fc_eq; try omega.
 rewrite 2 TPith_Fc_eq. apply IHt; trivial.
 apply False_ind; omega. apply False_ind; omega.
 apply False_ind; omega.
Qed.

Hint Resolve TPith_TPithdel_geq.

Lemma TPith_TPithdel : forall t m n i0 i1, 
 i0 > 0 -> i0 <= (TPlength t m n - 1) ->   
 i1 > 0 -> i1 <= TPlength t m n -> 
exists i2, i2 > 0 /\ i2 <= TPlength t m n /\  
 TPith i0 (TPithdel i1 t m n) m n = TPith i2 t m n.
Proof.
 intros. case (le_dec i1 i0); intro H3. 
 exists (i0 + 1). split; try omega; trivial. split; try omega; auto. 
 exists i0. split; trivial. split; try omega; trivial.
 apply TPith_TPithdel_lt; try omega; trivial. 
Qed.

Hint Resolve TPith_TPithdel.

Lemma TPithdel_comm_lt : forall t m n i j, 
 TPlength t m n > 1 -> i < j ->
 i > 0 -> j > 0 -> j <= TPlength t m n ->
 TPithdel i (TPithdel j t m n) m n = TPithdel (j - 1) (TPithdel i t m n) m n.
Proof.
 intros t m n. induction t; intros.
 simpl in H. false. omega. simpl in H. false. omega. 
 simpl in H. false. omega. Focus 3. simpl in H. false. omega.

 clear H. simpl in H3. 
 case (le_dec j (TPlength t1 m n)); intro H4. clear H3.
 case (TPlength t1 m n === 1); intro H5. assert (Q:j=1). omega.
 false. omega.  assert (Q : TPlength t1 m n >= 1). auto. 
 rewrite TPithdel_Pr_le; try omega; trivial.
 rewrite TPithdel_Pr_le with (i := i) (t1 := t1); try omega; trivial. 
 case (TPlength t1 m n === 2); intro H6. 
 assert (Qi:i=1). omega.  assert (Qj:j-1=1). omega. 
 rewrite Qi. rewrite Qj. rewrite 2 TPithdel_t1_Pr; 
 try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite 2 TPithdel_Pr_le; try rewrite TPlength_TPithdel; try omega; trivial. 
 fequals; trivial. apply IHt1; try omega; trivial. 
 case (le_dec i (TPlength t1 m n)); intro H5.
 case (TPlength t1 m n === 1); intro H6. assert (Qi:i=1). omega. rewrite Qi.
 rewrite TPithdel_t1_Pr; trivial.
 case (TPlength t2 m n === 1); intro H7.
 assert (Qj:j=TPlength t1 m n + 1). omega. rewrite Qj.
 rewrite TPithdel_t2_Pr; trivial.
 replace (TPlength t1 m n + 1 - 1) with 1; try omega. 
 rewrite 2 TPithdel_TPlength_1; trivial. rewrite TPithdel_Pr_gt; try omega.
 rewrite TPithdel_t1_Pr; trivial. rewrite H6; trivial.
 rewrite TPithdel_Pr_le with (i:=i); trivial.
 case (TPlength t2 m n === 1); intro H7.
 assert (Qj:j=TPlength t1 m n + 1). omega. rewrite Qj.
 rewrite TPithdel_t2_Pr; trivial. 
 replace (TPlength t1 m n + 1 - 1) with (TPlength (TPithdel i t1 m n) m n + 1).
 rewrite TPithdel_t2_Pr; trivial. rewrite TPlength_TPithdel; omega. 
 rewrite TPithdel_Pr_gt with (i:=j); try omega.  
 rewrite TPithdel_Pr_le with (i:=i); try omega. 
 rewrite TPithdel_Pr_gt; try rewrite TPlength_TPithdel; try omega.
 replace (j - 1 - (TPlength t1 m n - 1)) with (j - TPlength t1 m n); 
 try omega; trivial.
 case (TPlength t2 m n === 1); intro H6. assert (Q:j=TPlength t1 m n + 1). omega.
 false. omega.  assert (Q : TPlength t2 m n >= 1). auto. 
 rewrite TPithdel_Pr_gt; try omega; trivial.
 rewrite TPithdel_Pr_gt with (i := i) (t2 := t2); try omega; trivial. 
 case (TPlength t2 m n === 2); intro H7. 
 assert (Qi:i=TPlength t1 m n +1). omega.  
 assert (Qj:j-1=TPlength t1 m n +1). omega. 
 rewrite Qi. rewrite Qj. rewrite 2 TPithdel_t2_Pr; 
 try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try rewrite TPlength_TPithdel; try omega; trivial. 
 fequals; trivial. replace (j - 1 - TPlength t1 m n) with 
                           (j - TPlength t1 m n - 1); try omega.
 apply IHt2; try omega; trivial. 

 case (n0 === m); intro H4. case (n1 === n); intro H5.
 rewrite H4 in *|-*. rewrite H5 in *|-*. autorewrite with tuples in *|-.
 clear H4 H5. case (TPlength t m n === 2); intro H4.
 rewrite TPithdel_Fc_eq with (i:=i); try omega.
 rewrite TPithdel_Fc_eq with (i:=j); try omega.
 assert (Qi:i=1). omega. assert (Qj:j - 1=1). omega. rewrite Qi. rewrite Qj.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; 
 try rewrite TPlength_TPithdel; try omega; trivial.
 repeat rewrite TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
 fequals; auto. rewrite TPlength_Fc_diff_n in *|- ; trivial. false. omega.
 rewrite TPlength_Fc_diff_m in *|- ; trivial. false. omega.
Qed.

Lemma TPithdel_comm_geq : forall t m n i j, 
 TPlength t m n > 1 -> i >= j ->
 i > 0 -> j > 0 -> i <= TPlength t m n ->
 TPithdel i (TPithdel j t m n) m n = TPithdel j (TPithdel (i + 1) t m n) m n.
Proof.
 intros t m n. induction t; intros.
 simpl in H. false. omega. simpl in H. false. omega. 
 simpl in H. false. omega. Focus 3. simpl in H. false. omega.

 clear H. simpl in H3. 
 case (le_dec i (TPlength t1 m n)); intro H4. clear H3.
 case (TPlength t1 m n === 1); intro H5. 
 assert (Qi:i=1). omega. assert (Qj:j=1). omega.
 rewrite Qi. rewrite Qj. rewrite TPithdel_t1_Pr; trivial.
 replace (1 + 1) with (TPlength t1 m n + 1); try omega. 
 case (TPlength t2 m n === 1); intro H6. 
 rewrite TPithdel_t2_Pr; try omega; trivial. 
 rewrite 2 TPithdel_TPlength_1; trivial.
 rewrite TPithdel_Pr_gt; try omega; trivial. 
 rewrite TPithdel_t1_Pr; trivial. fequals; try omega.
 assert (Q: TPlength t2 m n >= 1). auto. omega. 
 rewrite TPithdel_Pr_le with (i:=j); try omega.
 assert (Qt2: TPlength t2 m n >= 1). auto.  
 case (TPlength t1 m n === i); intro H6. 
 replace (i+1) with (TPlength t1 m n + 1); try omega.
 replace i with (TPlength (TPithdel j t1 m n) m n + 1).
 case (TPlength t2 m n === 1); intro H7.
 rewrite 2 TPithdel_t2_Pr; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try omega; trivial.
 rewrite TPithdel_Pr_le; try omega; trivial. fequals. fequals.
 repeat rewrite TPlength_TPithdel; omega. 
 repeat rewrite TPlength_TPithdel; omega. 
 case (TPlength t1 m n === 2); intro H7. 
 rewrite TPithdel_Pr_le with (i:=i+1); try omega.
 assert (Qi:i=1). omega. assert (Qj:j=1). omega. rewrite Qi. rewrite Qj.
 repeat rewrite TPithdel_t1_Pr; try rewrite TPlength_TPithdel; try omega; trivial.
 repeat rewrite TPithdel_Pr_le; try rewrite TPlength_TPithdel; try omega.
 fequals. apply IHt1; try omega; trivial.
 case (le_dec j (TPlength t1 m n)); intro H5.
 case (TPlength t1 m n === 1); intro H6. assert (Qj:j=1). omega.
 rewrite Qj. rewrite TPithdel_t1_Pr; trivial.
 case (TPlength t2 m n === 1); intro H7. 
 assert (Qi:i=1\/i=2). omega. destruct Qi. rewrite H.
 replace (1+1) with (TPlength t1 m n + 1); omega. rewrite H.
 rewrite TPithdel_overflow; try omega. 
 rewrite TPithdel_overflow with (i:=2+1); try omega.
 rewrite TPithdel_t1_Pr; trivial. simpl; omega.
 case (i === TPlength t1 m n + TPlength t2 m n); intro H8.
 rewrite TPithdel_overflow with (i:=i+1). rewrite TPithdel_t1_Pr; trivial.
 rewrite TPithdel_overflow; try omega. trivial. simpl. omega.
 rewrite TPithdel_Pr_gt with (i:=i+1); try omega. rewrite TPithdel_t1_Pr; trivial.
 fequals; omega. assert (Q: TPlength t2 m n >= 1). auto. 
 rewrite TPithdel_Pr_le with (i:=j); try omega.
 case (i === TPlength t1 m n + TPlength t2 m n); intro H7.
 rewrite TPithdel_overflow with (i:=i+1).
 rewrite TPithdel_overflow with (i:=i); try omega. 
 rewrite TPithdel_Pr_le; try omega; trivial. 
 simpl; try rewrite TPlength_TPithdel; try omega. simpl. omega.
 rewrite TPithdel_Pr_gt with (i:=i); try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite TPithdel_Pr_gt with (i:=i+1); try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite TPithdel_Pr_le; trivial. fequals. fequals; omega.
 case (TPlength t2 m n === 1); intro H6. 
 assert (Qi : i = TPlength t1 m n + 1). omega.
 assert (Qj : j = TPlength t1 m n + 1). omega. rewrite Qi. rewrite Qj.
 rewrite TPithdel_t2_Pr; trivial.  
 rewrite TPithdel_overflow with (i:=TPlength t1 m n + 1 + 1). 
 rewrite TPithdel_t2_Pr; trivial. rewrite TPithdel_overflow; try omega; trivial.
 simpl; omega. rewrite TPithdel_Pr_gt; try omega.
 case (i === TPlength t1 m n + TPlength t2 m n); intro H7.
 rewrite TPithdel_overflow with (i:=i+1). rewrite TPithdel_overflow with (i:=i).
 rewrite TPithdel_Pr_gt; try omega; trivial.
 simpl; try rewrite TPlength_TPithdel; try omega. simpl; omega.
 rewrite TPithdel_Pr_gt with (i:=i+1); try omega. 
 case (TPlength t2 m n === 2); intro H8.
 assert (Qi: i = TPlength t1 m n + 1). omega.
 assert (Qj: j = TPlength t1 m n + 1). omega. rewrite Qi. rewrite Qj.
 rewrite 2 TPithdel_t2_Pr; try rewrite TPlength_TPithdel; try omega; trivial.
 rewrite 2 TPithdel_Pr_gt; try omega.
 replace (i + 1 - TPlength t1 m n) with (i - TPlength t1 m n + 1); try omega.
 fequals. apply IHt2; try omega. rewrite TPlength_TPithdel; try omega.
 rewrite TPlength_TPithdel; try omega. rewrite TPlength_TPithdel; try omega.
 rewrite TPlength_TPithdel; try omega. 

 case (n0 === m); intro H4. case (n1 === n); intro H5.
 rewrite H4 in *|-*. rewrite H5 in *|-*. autorewrite with tuples in *|-.
 clear H4 H5. case (TPlength t m n === 2); intro H4.
 case (i === TPlength t m n); intro H5.
 rewrite TPithdel_overflow with (i := i + 1); 
 autorewrite with tuples; try omega. 
 rewrite TPithdel_Fc_eq with (i:=j); try omega. 
 rewrite TPithdel_overflow; trivial. autorewrite with tuples.
 rewrite TPlength_TPithdel; try omega.

 rewrite TPithdel_Fc_eq with (i:=i+1); try omega.
 rewrite TPithdel_Fc_eq with (i:=j); try omega.
 assert (Qi:i=1). omega. assert (Qj:j=1). omega. rewrite Qi. rewrite Qj.
 rewrite 2 TPithdel_TPlength_1; autorewrite with tuples; 
 try rewrite TPlength_TPithdel; try omega; trivial.

 case (i === TPlength t m n); intro H5.
 rewrite TPithdel_overflow with (i := i + 1); 
 autorewrite with tuples; try omega. 
 rewrite TPithdel_Fc_eq with (i:=j); try omega. 
 rewrite TPithdel_overflow; trivial. autorewrite with tuples.
 rewrite TPlength_TPithdel; try omega.

 repeat rewrite TPithdel_Fc_eq; try rewrite TPlength_TPithdel; try omega.
 fequals; auto. rewrite TPlength_Fc_diff_n in *|- ; trivial. false. omega.
 rewrite TPlength_Fc_diff_m in *|- ; trivial. false. omega.
Qed.

Lemma Perm_TPithdel : forall t pi m n i,
 pi @ (TPithdel i t m n) = TPithdel i (pi @ t) m n.
Proof.
 intros. gen i. induction t; intro; autorewrite with perm.
 simpl. case_nat; autorewrite with perm; trivial.
 simpl. case_nat; autorewrite with perm; trivial.
 simpl. case_nat; autorewrite with perm; trivial. Focus 3.
 simpl. case_nat; autorewrite with perm; trivial. 
 case (i === 0); intro H0. rewrite H0. 
 autorewrite with perm tuples; trivial.
 case (le_dec i (TPlength t1 m n)); intro H1. 
 case (TPlength t1 m n === 1); intro H2.
 assert (i = 1). omega. rewrite H. rewrite 2 TPithdel_t1_Pr;
 autorewrite with tuples; trivial.
 rewrite 2 TPithdel_Pr_le; autorewrite with tuples perm; try omega.
 rewrite IHt1; trivial.
 case (le_dec i (TPlength t1 m n + TPlength t2 m n)); intro H2.
 case (TPlength t2 m n === 1); intro H3.
 assert (i = TPlength t1 m n + 1). omega. rewrite H.
 rewrite TPithdel_t2_Pr; autorewrite with tuples; trivial.
 replace (TPlength t1 m n) with (TPlength (pi @ t1) m n). 
 rewrite TPithdel_t2_Pr; autorewrite with tuples; trivial. 
 autorewrite with tuples; trivial. 
 rewrite 2 TPithdel_Pr_gt; autorewrite with tuples perm; try omega. 
 rewrite IHt2; trivial. 
 rewrite 2 TPithdel_overflow; simpl TPlength;
 autorewrite with perm tuples; try omega; trivial.
 case (i === 0); intro H0. rewrite H0. autorewrite with perm tuples; trivial.
 case (le_dec i (TPlength (Fc n0 n1 t) m n)); intro H1.
 case (TPlength t m n === 1); intro H2. 
 rewrite TPlength_Fc_TPlength_1 in H1; trivial.
 assert (i = 1); try omega. rewrite H.
 rewrite 2 TPithdel_TPlength_1; autorewrite with perm tuples; 
 try rewrite TPlength_Fc_TPlength_1; autorewrite with tuples; trivial.
 case (n0 === m); case (n1 === n); intros H3 H4.
 rewrite H3 in *|-*. rewrite H4 in *|-*. autorewrite with tuples in H1.
 rewrite 2 TPithdel_Fc_eq; autorewrite with perm tuples; try omega.
 rewrite IHt; trivial.
 rewrite TPlength_Fc_diff_n in H1; trivial. assert (i = 1); try omega. 
 rewrite H. rewrite 2 TPithdel_TPlength_1; auto; autorewrite with perm; trivial.
 rewrite TPlength_Fc_diff_m in H1; trivial. assert (i = 1); try omega. 
 rewrite H. rewrite 2 TPithdel_TPlength_1; auto; autorewrite with perm; trivial.
 rewrite TPlength_Fc_diff_m in H1; trivial. assert (i = 1); try omega. 
 rewrite H. rewrite 2 TPithdel_TPlength_1; auto; autorewrite with perm; trivial.
 rewrite 2 TPithdel_overflow; autorewrite with perm tuples; try omega; trivial.
 gen H1. simpl. repeat case_nat; intros; 
 autorewrite with tuples; try omega.
Qed. 

Hint Resolve Perm_TPithdel. 



(** About size_term and TPlength *)

Lemma size_swapp_term : forall s t, size_term (|[s] @ t) = size_term t. 
Proof. 
 intros. destruct s. induction t; simpl; trivial; omega.
Qed.

Hint Rewrite size_swapp_term : tuples.

Lemma size_term_Pr_l : forall t1 t2, size_term t1 < size_term (<|t1,t2|>).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Pr_r : forall t1 t2, size_term t2 < size_term (<|t1,t2|>).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Fc : forall m n t, size_term t < size_term (Fc m n t).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Ab_1 : forall a t, size_term t < size_term ([a]^t).
Proof. intros. simpl. omega. Qed.

Lemma size_term_Ab_2 : forall a s t, size_term (|[s] @ t) < size_term ([a]^t).
Proof. intros. simpl. rewrite size_swapp_term. omega. Qed.

Hint Resolve size_term_Pr_l.
Hint Resolve size_term_Pr_r.
Hint Resolve size_term_Fc.
Hint Resolve size_term_Ab_1.
Hint Resolve size_term_Ab_2.

Lemma size_term_geq_1 : forall t, size_term t >= 1.
Proof. introv. induction t; simpl; try omega; auto. Qed.

Hint Resolve size_term_geq_1.


Lemma TPlength_leq_size_term : forall t m n, TPlength t m n <= size_term t.
Proof. intros. induction t; simpl; repeat case_nat; omega. Qed.

Hint Resolve TPlength_leq_size_term.

Lemma TPlength_1_to_size_term : forall t m n, 
 TPlength t m n = size_term t <-> size_term t = 1.
Proof. 
 intros. induction t; simpl; repeat case_nat; try omega.
 assert (TPlength t1 m n >= 1 /\ 
         TPlength t2 m n >= 1 /\
         size_term t1 >= 1    /\ 
         size_term t2 >= 1    /\ 
         TPlength t1 m n <= size_term t1 /\
         TPlength t2 m n <= size_term t2). repeat split; auto.
 destruct H. destruct H0. destruct H1. destruct H2. destruct H3. 
 split; intro; false; omega. 
 assert (TPlength t m n >= 1 /\ 
         size_term t >= 1    /\ 
         TPlength t m n <= size_term t). split; auto.
 destruct H. destruct H0. split; intro; false; omega.
Qed.

Hint Resolve TPlength_1_to_size_term.

Lemma TPlength_TPithdel_1 : forall t m n, 
 TPlength t m n = 1 ->  TPlength (TPithdel 1 t m n) m n = 1 .
Proof. intros. rewrite TPithdel_TPlength_1; trivial. Qed.

Hint Resolve TPlength_TPithdel_1.

Lemma size_term_TPithdel : forall t m n,
 size_term (TPithdel 1 t m n) <= size_term t.
Proof.
 intros. induction t.
 simpl; trivial. simpl; trivial.
 simpl. assert (Q : size_term t >= 1). auto. omega.
 case (TPlength t1 m n === 1); intro H1. 
 rewrite TPithdel_t1_Pr; trivial. simpl; omega.
 rewrite TPithdel_Pr_le; trivial; simpl; try omega.
 assert (Q : TPlength t1 m n >= 1). auto. omega.
 case (TPlength (Fc n0 n1 t) m n === 1); intro H0.
 rewrite TPithdel_TPlength_1; trivial. simpl.
 assert (Q: size_term t >= 1). auto. omega.
 case (n0 === m); intro H1. case (n1 === n); intro H2.
 rewrite H1 in *|-*. rewrite H2 in *|-*.
 rewrite TPithdel_Fc_eq; simpl; try omega; trivial. 
 assert (Q : TPlength t m n >= 1). auto. omega.
 autorewrite with tuples in H0; trivial.
 rewrite TPlength_Fc_diff_n in H0; trivial. 
 apply False_ind. omega.
 rewrite TPlength_Fc_diff_m in H0; trivial.
 apply False_ind. omega.
 simpl; trivial.
Qed.

Hint Resolve size_term_TPithdel.

Lemma size_term_TPithdel2 : forall t m n, TPlength t m n <> 1 ->
 size_term (TPithdel 1 t m n) < size_term t.
Proof.
 intros. induction t.
 simpl in H. apply False_ind. omega.
 simpl in H. apply False_ind. omega.
 simpl in H. apply False_ind. omega.
 case (TPlength t1 m n === 1); intro H1. 
 rewrite TPithdel_t1_Pr; trivial. 
 rewrite TPithdel_Pr_le; trivial; simpl; try omega.
 assert (Q :  size_term (TPithdel 1 t1 m n) < size_term t1). 
 apply IHt1; trivial. omega.
 assert (Q : TPlength t1 m n >= 1). auto. omega.
 case (n0 === m); intro H1. case (n1 === n); intro H2.
 rewrite H1 in *|-*. rewrite H2 in *|-*. 
 autorewrite with tuples in H.
 rewrite TPithdel_Fc_eq; simpl; try omega; trivial. 
 assert (Q : size_term (TPithdel 1 t m n) < size_term t). 
 apply IHt. trivial. omega.
 assert (Q : TPlength t m n >= 1). auto. omega.
 rewrite TPlength_Fc_diff_n in H; trivial. 
 apply False_ind. omega.
 rewrite TPlength_Fc_diff_m in H; trivial.
 apply False_ind. omega.
 simpl in H. apply False_ind. omega.
Qed.

Hint Resolve size_term_TPithdel2.

Lemma size_term_TPith : forall t m n,
 size_term (TPith 1 t m n) <= size_term t.
Proof.
 intros. induction t.
 simpl; trivial. simpl; trivial. simpl. omega. 
 rewrite TPith_Pr_le; try omega. simpl. omega.
 assert (Q : TPlength t1 m n >= 1). auto. omega.
 case (n0 === m); intro H1. case (n1 === n); intro H2.
 rewrite H1 in *|-*. rewrite H2 in *|-*. 
 autorewrite with tuples; simpl; omega.
 rewrite TPith_Fc_diff_n; simpl; try omega; trivial. 
 rewrite TPith_Fc_diff_m; simpl; try omega; trivial. 
 simpl; trivial.
Qed.

Hint Resolve size_term_TPith. 


Lemma size_term_TPith2 : forall t m n,
 TPlength t m n <> 1 ->
 size_term (TPith 1 t m n) < size_term t.
Proof.
 intros. destruct t; simpl in H.
 false; omega. false; omega. false; omega.
 rewrite TPith_Pr_le; try omega; simpl. 
 assert (Q: size_term (TPith 1 t1 m n) <= size_term t1). auto.
 omega. assert (Q : TPlength t1 m n >= 1). auto. omega.
 repeat case_nat. autorewrite with tuples. simpl.
 assert (Q: size_term (TPith 1 t m n) <= size_term t). auto. omega.
 false; omega.
Qed.


Hint Resolve size_term_TPith2. 


(** About Fc_app *)


Lemma Fc_app_Sn : forall i t m n,  Fc m n (Fc_app i m n t) = Fc_app (S i) m n t.
Proof. intros. simpl. trivial. Qed.

Hint Rewrite  Fc_app_Sn : tuples.

 
Lemma TPlength_2 : forall t m n, TPlength t m n = 2 ->
                             exists i t1 t2, t = Fc_app i m n (<|t1,t2|>)  /\
                                 TPlength t1 m n = 1 /\ TPlength t2 m n = 1 .
Proof.
  intros. induction t; simpl in H; try omega.
  clear IHt1 IHt2.
  assert (Q: TPlength t1 m n >= 1); auto.
  assert (Q': TPlength t2 m n >= 1); auto. 
  exists 0. exists t1. exists t2. simpl.
  repeat split; try omega; trivial.
  repeat case_nat. case (IHt H). clear H IHt.
  intros i H. destruct H. destruct H. destruct H. destruct H0.
  exists (S i). exists x. exists x0. repeat split; trivial.
  simpl. rewrite H. trivial. false. false.
Qed.


Lemma TPlength_Fc_app : forall i t m n, TPlength (Fc_app i m n t) m n = TPlength t m n.
Proof.
 intros. induction i; simpl; repeat case_nat; trivial.
Qed.

Hint Rewrite TPlength_Fc_app : tuples.

Lemma TPlength_rem_Fc_app_diff: forall t m1 m2 n1 n2, (m1 <> m2 \/ n1 <> n2) ->
      TPlength t m2 n2  <> 1 ->                                                
      TPlength (rem_Fc_app t m1 n1) m2 n2 = TPlength t m2 n2.
Proof.
  intros. gen_eq l : (size_term t). intro H'.
  gen t H0 H' H. induction l using peano_induction; intros. destruct t; simpl in H'.
  simpl; trivial. simpl; trivial. simpl; trivial. simpl; trivial.
  simpl; repeat case_nat.
  rewrite H with (m := size_term t); try omega; trivial.  
  rewrite TPlength_Fc_diff_n in H0; trivial. omega.
  rewrite TPlength_Fc_diff_m in H0; trivial. omega.
  autorewrite with tuples; trivial. autorewrite with tuples; trivial.
  rewrite TPlength_Fc_diff_n in H0; trivial. omega.
  rewrite TPlength_Fc_diff_m in H0; trivial. omega.
  autorewrite with tuples; trivial.
  rewrite TPlength_Fc_diff_n in H0; trivial. omega.
  rewrite TPlength_Fc_diff_m in H0; trivial. omega.
  simpl; trivial.
Qed.

  
Lemma TPith_Fc_app : forall i j t m n, TPith i (Fc_app j m n t) m n = TPith i t m n.
Proof.
  intros. induction j; simpl; repeat case_nat; trivial.
  rewrite TPith_0 in IHj; trivial.
  case (le_dec i (TPlength (Fc_app j m n t) m n)); intro H1; trivial.
  rewrite TPlength_Fc_app in H1. rewrite TPith_overflow; try omega; trivial. 
Qed.

Hint Rewrite TPith_Fc_app : tuples.
  
Lemma TPithdel_Fc_app : forall i j t m n, TPlength t m n <> 1 ->
                        TPithdel i (Fc_app j m n t) m n = Fc_app j m n (TPithdel i t m n).
Proof.
  intros. induction j.
  simpl. trivial. simpl. repeat case_nat.
  rewrite TPithdel_0. trivial.
  rewrite TPlength_Fc_app in e1. contradiction.
  case (le_dec i (TPlength (Fc_app j m n t) m n)); intro H1.
  fequals. rewrite TPlength_Fc_app in H1. rewrite TPithdel_overflow; try omega.
  trivial.  
Qed.