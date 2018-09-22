(**
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Adjusted_Generated_Equiv.ml
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : This file is an adjusted version of the extracted code
               in Original_Generated_Equiv.ml, where the extracted naturals 
               are replaced by OCaml integers.

 Last Modified On: Sep 18, 2018.
 ============================================================================
*)

let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

(*
type nat =
| O
| S of nat
*)

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type sumbool =
| Left
| Right

(** val add : int -> int -> int **)

let add n m = n + m

(** val sub : int -> int -> int **)

let sub n m = n - m                    

                   
(** val le_lt_dec : nat -> nat -> sumbool **)

let le_lt_dec n m =
  match (n <= m) with
  | true -> Left
  | false -> Right

(** val le_gt_dec : nat -> nat -> sumbool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : nat -> nat -> sumbool **)

let le_dec =
  le_gt_dec

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

type 'a set = 'a list

(** val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| Nil -> Cons (a, Nil)
| Cons (a1, x1) ->
  (match aeq_dec a a1 with
   | Left -> Cons (a1, x1)
   | Right -> Cons (a1, (set_add aeq_dec a x1)))

(** val eq_nat_rec : nat -> nat -> bool **)

let eq_nat_rec m n =
  match (m = n) with
  | true -> True
  | false -> False 

(** val nat_eqdec : nat -> nat -> sumbool **)

let nat_eqdec m n =
  let b = eq_nat_rec m n in (match b with
                             | True -> Left
                             | False -> Right)

(** val eq_mem_list_dec :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool **)

let rec eq_mem_list_dec aeq_dec a = function
| Nil -> Right
| Cons (y, l0) ->
  (match aeq_dec a y with
   | Left -> Left
   | Right -> eq_mem_list_dec aeq_dec a l0)

type atom = int
  (* singleton inductive, whose constructor was atom *)

type var = int
  (* singleton inductive, whose constructor was var *)

type perm = (atom, atom) prod list

type context = (atom, var) prod list

type term =
| Ut
| At of atom
| Ab of atom * term
| Pr of term * term
| Fc of int * int * term
| Su of perm * var

(** val eq_atom_rec : atom -> atom -> bool **)

let eq_atom_rec =
  eq_nat_rec

(** val atom_eqdec : atom -> atom -> sumbool **)

let atom_eqdec =
  nat_eqdec

(** val eq_var_rec : var -> var -> bool **)

let eq_var_rec =
  eq_nat_rec

(** val var_eqdec : var -> var -> sumbool **)

let var_eqdec =
  nat_eqdec

(** val atom_var_eqdec : (atom, var) prod -> (atom, var) prod -> sumbool **)

let atom_var_eqdec c c' =
  let Pair (a, v) = c in
  let Pair (a0, v0) = c' in
  (match atom_eqdec a a0 with
   | Left -> var_eqdec v v0
   | Right -> Right)

(** val in_context_dec : (atom, var) prod -> context -> sumbool **)

let in_context_dec c c0 =
  eq_mem_list_dec atom_var_eqdec c c0

(** val swapa : (atom, atom) prod -> atom -> atom **)

let swapa s c =
  let Pair (a, b) = s in
  (match atom_eqdec a c with
   | Left -> b
   | Right -> (match atom_eqdec b c with
               | Left -> a
               | Right -> c))

(** val p_act_aux : perm -> atom -> atom **)

let rec p_act_aux p c =
  match p with
  | Nil -> c
  | Cons (p0, p1) -> p_act_aux p1 (swapa p0 c)

(** val perm_act : perm -> term -> term **)

let rec perm_act pi = function
| Ut -> Ut
| At a -> At (p_act_aux pi a)
| Ab (a, s) -> Ab ((p_act_aux pi a), (perm_act pi s))
| Pr (u, v) -> Pr ((perm_act pi u), (perm_act pi v))
| Fc (e, n, s) -> Fc (e, n, (perm_act pi s))
| Su (pi', x) -> Su ((app pi' pi), x)

(** val tPlength : term -> nat -> nat -> nat **)

let rec tPlength t e n =
  match t with
  | Pr (t1, t2) -> add (tPlength t1 e n) (tPlength t2 e n)
  | Fc (e0, n0, t1) ->
    (match match eq_nat_rec e e0 with
           | True -> eq_nat_rec n n0
           | False -> False with
     | True -> tPlength t1 e n
     | False -> 1)
  | _ -> 1

(** val tPith : nat -> term -> nat -> nat -> term **)

let rec tPith i t e n =
  match t with
  | Pr (t1, t2) ->
    let l1 = tPlength t1 e n in
    (match le_dec i l1 with
     | Left -> tPith i t1 e n
     | Right -> tPith (sub i l1) t2 e n)
  | Fc (e0, n0, t0) ->
    (match match eq_nat_rec e e0 with
           | True -> eq_nat_rec n n0
           | False -> False with
     | True -> tPith i t0 e n
     | False -> t)
  | _ -> t

(** val tPithdel : nat -> term -> nat -> nat -> term **)

let rec tPithdel i t e n =
  match t with
  | Pr (t1, t2) ->
    let l1 = tPlength t1 e n in
    let l2 = tPlength t2 e n in
    (match le_dec i l1 with
     | Left ->
       (match eq_nat_rec l1 1 with
        | True -> t2
        | False -> Pr ((tPithdel i t1 e n), t2))
     | Right ->
       let ii = sub i l1 in
       (match eq_nat_rec l2 1 with
        | True -> t1
        | False -> Pr (t1, (tPithdel ii t2 e n))))
  | Fc (e0, n0, t0) ->
    (match eq_nat_rec (tPlength (Fc (e0, n0, t)) e n) 1 with
     | True -> Ut
     | False -> Fc (e0, n0, (tPithdel i t0 e n)))
  | _ -> Ut

(** val atoms_perm : perm -> atom set **)

let rec atoms_perm = function
| Nil -> Nil
| Cons (p, pi0) ->
  let Pair (a, b) = p in
  set_add atom_eqdec a (set_add atom_eqdec b (atoms_perm pi0))

(** val dom_perm_aux : perm -> atom set -> atom set **)

let rec dom_perm_aux pi = function
| Nil -> Nil
| Cons (a, s0) ->
  (match atom_eqdec a (p_act_aux pi a) with
   | Left -> dom_perm_aux pi s0
   | Right -> set_add atom_eqdec a (dom_perm_aux pi s0))

(** val dom_perm : perm -> atom set **)

let dom_perm pi =
  dom_perm_aux pi (atoms_perm pi)

(** val disgr : perm -> perm -> atom set **)

let disgr pi pi' =
  dom_perm (app pi (rev pi'))

(** val fresh_context : atom set -> var -> (atom, var) prod list **)

let rec fresh_context s x =
  match s with
  | Nil -> Nil
  | Cons (a, s0) -> Cons ((Pair (a, x)), (fresh_context s0 x))

(** val sub_context_rec : context -> context -> bool **)

let rec sub_context_rec c c' =
  match c with
  | Nil -> True
  | Cons (c0, c1) ->
    (match in_context_dec c0 c' with
     | Left -> sub_context_rec c1 c'
     | Right -> False)

type ('a, 'b) sigma = { pr1 : 'a; pr2 : 'b }

(** val pr1 : ('a1, 'a2) sigma -> 'a1 **)

let pr1 x = x.pr1

(** val pr2 : ('a1, 'a2) sigma -> 'a2 **)

let pr2 x = x.pr2

(** val fresh_rec : context -> atom -> term -> bool **)

let rec fresh_rec c a = function
| Ut -> True
| At a0 -> (match eq_atom_rec a a0 with
            | True -> False
            | False -> True)
| Ab (a0, s) ->
  (match eq_atom_rec a a0 with
   | True -> True
   | False -> fresh_rec c a s)
| Pr (u, v) ->
  (match fresh_rec c a u with
   | True -> fresh_rec c a v
   | False -> False)
| Fc (_, _, s) -> fresh_rec c a s
| Su (pi, x) ->
  (match in_context_dec (Pair ((p_act_aux (rev pi) a), x)) c with
   | Left -> True
   | Right -> False)

(** val iter : (nat -> bool) -> nat -> nat -> bool **)

let rec iter p i j =
  match j with 
  | 0 -> False
  | _ -> (match p i with
           | True -> True
           | False -> iter p (i + 1) (j - 1))

(** val equiv_rec : context -> term -> term -> bool **)

let equiv_rec c s t =
  let hypspack = { pr1 = c; pr2 = { pr1 = s; pr2 = { pr1 = t; pr2 = Tt } } } in
  let rec fix_F x =
    let c0 = x.pr1 in
    let h = x.pr2 in
    let s0 = h.pr1 in
    let h0 = h.pr2 in
    let t0 = h0.pr1 in
    let equiv_rec0 = fun c1 s1 t1 ->
      let y = { pr1 = c1; pr2 = { pr1 = s1; pr2 = { pr1 = t1; pr2 = Tt } } } in
      (fun _ -> fix_F y)
    in
    (match s0 with
     | Ut -> (match t0 with
              | Ut -> True
              | _ -> False)
     | At a -> (match t0 with
                | At a0 -> eq_atom_rec a a0
                | _ -> False)
     | Ab (a, t1) ->
       (match t0 with
        | Ab (a0, t2) ->
          (match eq_atom_rec a a0 with
           | True -> equiv_rec0 c0 t1 t2 __
           | False ->
             (match fresh_rec c0 a t2 with
              | True ->
                equiv_rec0 c0 t1 (perm_act (Cons ((Pair (a, a0)), Nil)) t2) __
              | False -> False))
        | _ -> False)
     | Pr (t1, t2) ->
       (match t0 with
        | Pr (t3, t4) ->
          (match equiv_rec0 c0 t1 t3 __ with
           | True -> equiv_rec0 c0 t2 t4 __
           | False -> False)
        | _ -> False)

     | Fc (n, n0, t1) ->
        (match n with
           
        | 0 ->
          (match t0 with
           | Fc (n1, n2, t2) ->
             (match match eq_nat_rec n0 n2 with
                    | True -> eq_nat_rec 0 n1
                    | False -> False with
              | True ->
                (match equiv_rec0 c0 (tPith 1 t1 0 n0)
                         (tPith 1 t2 0 n0) __ with
                 | True ->
                   equiv_rec0 c0 (tPithdel 1 (Fc (0, n0, t1)) 0 n0)
                     (tPithdel 1 (Fc (0, n0, t2)) 0 n0) __
                 | False -> False)
              | False -> False)
           | _ -> False)

        | 1 ->

             (match t0 with
              | Fc (n2, n3, t2) ->
                (match match eq_nat_rec n0 n3 with
                       | True -> eq_nat_rec 1 n2
                       | False -> False with
                 | True ->
                   let branch = fun i ->
                     match equiv_rec0 c0 (tPith 1 t1 1 n0)
                             (tPith i t2 1 n0) __ with
                     | True ->
                       equiv_rec0 c0
                         (tPithdel 1 (Fc (1, n0, t1)) 1 n0)
                         (tPithdel i (Fc (1, n0, t2)) 1 n0) __
                     | False -> False
                   in
                   iter branch 1 (tPlength t2 1 n0)
                 | False -> False)
              | _ -> False)

        | 2 ->

                (match t1 with
                 | Pr (t2, t3) ->
                   (match t0 with
                    | Fc (n3, n4, t4) ->
                      (match t4 with
                       | Pr (t5, t6) ->
                         (match match eq_nat_rec n0 n4 with
                                | True -> eq_nat_rec 2 n3
                                | False -> False with
                          | True ->
                            (match match equiv_rec0 c0 t2 t5 __ with
                                   | True -> equiv_rec0 c0 t3 t6 __
                                   | False -> False with
                             | True -> True
                             | False ->
                               (match equiv_rec0 c0 t2 t6 __ with
                                | True -> equiv_rec0 c0 t3 t5 __
                                | False -> False))
                          | False -> False)
                       | x0 ->
                         (match match eq_nat_rec 2 n3 with
                                | True -> eq_nat_rec n0 n4
                                | False -> False with
                          | True -> equiv_rec0 c0 (Pr (t2, t3)) x0 __
                          | False -> False))
                    | _ -> False)
                 | x0 ->
                   (match t0 with
                    | Fc (n3, n4, t2) ->
                      (match match eq_nat_rec 2 n3 with
                             | True -> eq_nat_rec n0 n4
                             | False -> False with
                       | True -> equiv_rec0 c0 x0 t2 __
                       | False -> False)
                    | _ -> False))

          | _ ->
                (match t0 with
                 | Fc (n4, n5, t2) ->
                   (match match eq_nat_rec n n4 with
                          | True -> eq_nat_rec n0 n5
                          | False -> False with
                    | True -> equiv_rec0 c0 t1 t2 __
                    | False -> False)
                 | _ -> False))
          
     | Su (p, v) ->
       (match t0 with
        | Su (p0, v0) ->
          (match eq_var_rec v v0 with
           | True -> sub_context_rec (fresh_context (disgr p p0) v) c0
           | False -> False)
        | _ -> False))

  in fix_F hypspack
