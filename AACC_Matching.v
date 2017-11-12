(*
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : AACC_Matching.v
 Authors     : Washington Luis R. de Carvalho Segundo and
               Mauricio Ayala Rincon 
               Universidade de Brasilia (UnB) - Brazil
               Group of Theory of Computation
 
 Last Modified On: April 3, 2017.
 ============================================================================
 *)

Require Import Bool.
Require Export C_Unif Soundness.

(** Ground terms **)

Definition gnd (t : term) :=
  forall s, set_In s (subterms t) -> ~ is_Su s .  

(** Right hand ground promblem **)

Definition rhg (P : Problem) :=
  forall s t, set_In (s~?t) P -> gnd t .


(** Tecnical lemmas **)

Lemma gnd_Ut : gnd Ut.
Proof.
  unfold gnd. intros.
  simpl in H. destruct H; try contradiction.
  rewrite <- H. simpl. intro; trivial.
Qed.

Lemma gnd_At : forall a, gnd (%a).
Proof.
  unfold gnd. intros.
  simpl in H. destruct H; try contradiction.
  rewrite <- H. simpl. intro; trivial.
Qed.

Lemma gnd_Fc : forall E n s, gnd (Fc E n s) <-> gnd s.
Proof.
  intros. unfold gnd. split~; intros.
  apply H. simpl. apply set_add_intro1; trivial.
  simpl in H0. apply set_add_elim in H0.
  destruct H0. rewrite H0. simpl. intro; trivial.
  apply H; trivial.
Qed.

Lemma gnd_Ab : forall a s, gnd ([a]^s) <-> gnd s.
Proof.
 intros. unfold gnd. split~; intros.
 apply H. simpl. apply set_add_intro1; trivial.
 simpl in H0. apply set_add_elim in H0.
 destruct H0. rewrite H0. simpl. intro; trivial.
 apply H; trivial.
Qed.

Lemma gnd_Pr : forall s t, gnd (<|s,t|>) <-> (gnd s /\ gnd t).
Proof.
 intros. unfold gnd. split; intros.
 split~; intros.
 apply H. simpl.
 apply set_add_intro1. apply set_union_intro1; trivial.
 apply H. simpl.
 apply set_add_intro1. apply set_union_intro2; trivial. 
 simpl in H0. apply set_add_elim in H0. destruct H0.
 rewrite H0. simpl. intro; trivial.
 destruct H.
 apply set_union_elim in H0. destruct H0.
 apply H; trivial. apply H1; trivial.
Qed. 

Lemma not_gnd_Su : forall pi X, ~ gnd (pi|.X).
Proof.
  intros. intro.
  unfold gnd in H.
  assert (Q : ~ is_Su (pi|.X)). apply H.
   simpl. left~.
   apply Q. simpl; trivial.
Qed.
   

Lemma gnd_perm : forall pi t, gnd t <-> gnd (pi @ t).
Proof.
  intros. induction t; autorewrite with perm.
  split; intro; trivial.
  split; intro; apply gnd_At.
  split; intro;
  apply gnd_Ab in H; apply gnd_Ab; apply IHt; trivial.
  split; intro;
  apply gnd_Pr in H.
  apply gnd_Pr; split~; [apply IHt1 | apply IHt2] ; apply H.
  apply gnd_Pr; split~; [apply IHt1 | apply IHt2] ; apply H.
  split; intro;
  apply gnd_Fc in H; apply gnd_Fc; apply IHt; trivial.
  split; intro; apply not_gnd_Su in H; contradiction.
Qed.


Lemma gnd_subs : forall t S, gnd t -> t|^S = t. 
Proof.
  intros. induction t; simpl; trivial.
  apply gnd_Ab in H. rewrite IHt; trivial.
  apply gnd_Pr in H. destruct H.
  rewrite IHt1; try rewrite IHt2; trivial.
  apply gnd_Fc in H. rewrite IHt; trivial.
  apply not_gnd_Su in H. contradiction.
Qed.  
  
  
Lemma rhg_add : forall P u,  rhg (P |+ u) <-> (rhg ([u]) /\ rhg P).
Proof.
  intros. unfold rhg. split; intros.
  split; intros; apply (H s).  
  simpl in H0. destruct H0; try contradiction.
  apply set_add_intro2. symmetry. trivial.
  apply set_add_intro1; trivial.
  apply set_add_elim in H0.
  destruct H. destruct H0.
  apply (H s). simpl. left~.
  apply (H1 s); trivial.
Qed.

Lemma rhg_union : forall P P', rhg (P \cup P') <-> (rhg P /\ rhg  P').
Proof.
  intros. unfold rhg.
  split; try split; intros.
  apply (H s). apply set_union_intro1; trivial.
  apply (H s). apply set_union_intro2; trivial.  
  apply set_union_elim in H0. destruct H.
  destruct H0; [apply (H s) | apply (H1 s)]; trivial.
Qed.

Lemma rhg_rem : forall P u, rhg P -> rhg (P\u).  
Proof.
  intros. unfold rhg in *|-*; intros.
  apply set_remove_1 in H0. apply (H s); trivial.
Qed.

Lemma rhg_fresh : forall a t, rhg ([a#?t]) .
Proof.
  intros. unfold rhg; intros.
  simpl in H. destruct H; try contradiction.
  inverts H.
Qed.  
 
Lemma rhg_equ : forall s t, rhg ([s~?t]) <-> gnd t.
Proof.
  intros. unfold rhg; split~; intros.
  apply (H s). simpl. left~.
  simpl in H0. destruct H0; try contradiction.
  inverts H0; trivial.
Qed.

Lemma rhg_subs_fresh : forall C S, rhg (C /? S).
Proof.
  intros. unfold rhg; intros.
  apply equ_subs_fresh in H.
  contradiction.
Qed.

Lemma rhg_subs_Probl : forall P S, rhg P -> rhg (P|^^S).
Proof.
  intros. unfold rhg in *|-*; intros.
  apply set_In_subs in H0.
  case H0; clear H0; intros u' H0.
  destruct H0. destruct u';
  simpl in H0; inverts H0.
  apply H in H1. rewrite gnd_subs; trivial.  
Qed.  
 
(** Invariance through rh_ground **)


Lemma fresh_sys_rhg : forall T T',
                      fresh_sys T T' -> rhg (snd T) -> rhg (snd T').
Proof.
  intros.
  inverts H; simpl in *|-*;
  try apply rhg_rem;
  try apply rhg_add; try split;
  try apply rhg_add; try split;
  try apply rhg_fresh; trivial.
Qed.  
  
  
Lemma equ_sys_rhg : forall T T',
                    equ_sys T T' -> rhg (snd T) -> rhg (snd T').
Proof.
  intros.
  inverts H; try apply H0 in H1;
  simpl in *|-*;
  try apply rhg_rem;
  try apply rhg_add; try split;
  try apply rhg_add; try split;
  try apply rhg_equ; trivial;
  try apply gnd_Pr in H1;
  try apply gnd_Fc in H1;
  try apply gnd_Ab in H1; try apply H1;
  try apply gnd_Pr in H1; try apply H1.
  apply rhg_fresh.
  apply gnd_perm. apply H0 in H2.
  apply gnd_Ab in H2; trivial.
  apply rhg_union. split~.
  apply rhg_subs_Probl.
  apply rhg_rem. apply rhg_rem; trivial.
  apply rhg_subs_fresh.
  apply H0 in H3.
  apply not_gnd_Su in H3.
  contradiction.
Qed.
  

Lemma unif_step_rhg : forall T T',
                  unif_step T T' -> rhg (snd T) -> rhg (snd T').
Proof.
 intros. destruct H.
 apply equ_sys_rhg with (T:=T); trivial.
 apply fresh_sys_rhg with (T:=T); trivial.
Qed.

Lemma unif_path_rhg : forall T T',
                      unif_path T T' -> rhg (snd T) -> rhg (snd T').
Proof.
  intros. unfold unif_path in H. destruct H.
  induction H; trivial. 
  apply unif_step_rhg with (T:=s); trivial.
  apply IHtr_clos; trivial.
  apply unif_step_rhg with (T:=s); trivial.
Qed.


(** rhs ground problems have all successful leaves with P = [] *)

Lemma unif_path_empty_Probl : forall T T',
                                
                                unif_path T T' ->
                                
                                Proper_Problem (snd T) -> rhg (snd T) ->
                                
                                (exists Sl, sol_c Sl T') ->
                                
                                snd (T') = [].
Proof.
  intros.
  apply unif_path_Proper_Problem with (T':=T') in H0; trivial. 
  apply unif_path_rhg with (T':=T') in H1; trivial.
  unfold unif_path in H.
  destruct H.
  assert (Q : fixpoint_Problem (snd T')).
   apply successful_leaves_ch; trivial.
   split~; trivial.
  unfold fixpoint_Problem in Q.
  unfold rhg in H1.
  apply set_In_nil; intros.
  intro. generalize H4. intro H5.
  apply Q in H4.
  destruct a. unfold fixpoint_equ in H4.
  destruct H4. destruct H4. destruct H4. inverts H6.
  apply H1 in H5.
  unfold fixpoint_equ in H4.
  case H4; clear H4; intros pi H4.
  case H4; clear H4; intros X H4.  
  destruct H4. inverts H6.
  apply not_gnd_Su in H5.
  trivial.
Qed.


(* Definition of solution of a matching problem *)

Definition matching_sol_c (Sl : Context * Subst) (T : Triple) :=
  let C := (fst (fst T)) in
  let S := (snd (fst T)) in
  let P := (snd T) in
  let D := (fst Sl) in
  let W := (snd Sl) in
(* 1 *) ( fresh_env C D W ) /\
(* 2 *) ( forall a t, set_In (a#?t) P -> D |- a # (t|^W) ) /\
(* 3 *) ( forall s t, set_In (s~?t) P -> D |- (s|^W) ~c t ) /\
(* 4 *) ( exists S'', D |- (S©S'') ~:c W ) .



(** Freshness context generator *)

Fixpoint fresh_ctx (a : Atom) (t : term) {struct t} : bool * Context :=
  match t with
      
    | <<>> => (true, [])
                
    | %b => if a ==at b then (false, []) else (true, [])
                                                  
    | Fc E n s => fresh_ctx a s
                            
    | [b]^s => if a ==at b then (true, []) else fresh_ctx a s
                                                          
    | <|u,v|> => let (bool0, ctx0) := fresh_ctx a u in
                 let (bool1, ctx1) := fresh_ctx a v in
                 (bool0 && bool1, set_union Context_eqdec ctx0 ctx1)
                   
    | pi|.X  => (true, [(!pi $ a, X)])
                  
end.


Close Scope nat_scope.

Definition Pair :=  (Context * Problem) . 

Inductive equiv_ctx : Pair -> Pair -> Prop :=
  
 | equiv_ctx_refl : forall C P s, (set_In (s~?s) P) ->
                              equiv_ctx (C,P)
                                        (C,P\(s~?s))

                                        
 | equiv_ctx_Pr : forall C P s0 s1 t0 t1,
                  (set_In ((<|s0,s1|>)~?(<|t0,t1|>)) P) ->
                   equiv_ctx (C,P)
                             (C,(((P|+(s0~?t0))|+(s1~?t1))\((<|s0,s1|>)~?(<|t0,t1|>))))
 .                          


 (*
 | equ_sys_Fc : forall C S P E n t t', (set_In ((Fc E n t)~?(Fc E n t')) P) -> E <> 2 ->
                                                                                      
                                        equ_sys (C,S,P)
                                                (C,S,(P|+(t~?t'))\((Fc E n t)~?(Fc E n t'))) 


 | equ_sys_C1 : forall C S P n s0 s1 t0 t1,    
                  
   (set_In ((Fc 2 n (<|s0,s1|>))~?(Fc 2 n (<|t0,t1|>)))) P ->
                  
     equ_sys (C,S,P)
             (C,S,((P|+(s0~?t0))|+(s1~?t1))\(Fc 2 n (<|s0,s1|>)~?(Fc 2 n (<|t0,t1|>))))


 | equ_sys_C2 : forall C S P n s0 s1 t0 t1,    
                  
   (set_In ((Fc 2 n (<|s0,s1|>))~?(Fc 2 n (<|t0,t1|>)))) P ->
                  
     equ_sys (C,S,P)
             (C,S,((P|+(s0~?t1))|+(s1~?t0))\(Fc 2 n (<|s0,s1|>)~?(Fc 2 n (<|t0,t1|>))))


 | equ_sys_Ab1 : forall C S P a t t', (set_In (([a]^t)~?([a]^t')) P) ->
                                       equ_sys (C,S,P)
                                               (C,S,(P|+(t~?t'))\(([a]^t)~?([a]^t')))

 | equ_sys_Ab2 : forall C S P a b t t',
                    a <> b -> (set_In (([a]^t)~?([b]^t')) P) ->
                    equ_sys (C,S,P)
                            (C,S,((P|+(t~?([(a,b)]@t'))|+(a#?t')))\(([a]^t)~?([b]^t')))

 | equ_sys_inst : forall C S S' P pi X t,

                    (~ set_In X (term_vars t)) ->

                    ((set_In (pi|.X~?t) P) \/ (set_In (t~?(pi|.X)) P)) ->

                    S' = S©([(X,(!pi)@t)]) ->

                    equ_sys (C,S,P)
                            (C,S',((P\(pi|.X~?t)\(t~?(pi|.X)))|^^([(X,(!pi)@t)]))\cup(C/?S'))
                                                          
 | equ_sys_inv : forall C S P pi pi' X,
                   pi <> pi' -> pi' <> [] -> (set_In ((pi|.X)~?(pi'|.X)) P) ->
                   equ_sys (C,S,P)
                   (C,S,(P|+((pi++(!pi'))|.X~?([]|.X)))\((pi|.X)~?(pi'|.X)))
.
*)