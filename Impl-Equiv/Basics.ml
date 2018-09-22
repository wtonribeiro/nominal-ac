(**
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Basics.ml
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : This file contains the definitions of f_terms, flattening,
               the freshness checking function, iterator function
               and the difference set operator.


 Last Modified On: Sep 18, 2018.
 ============================================================================
*)

open List

(** list' is an alias to the original type list.
    This is necessary to avoid collision with the Coq's definition 
    of list in the further automatically extracted code. *) 
       
type 'a list' = 'a list 

(** atoms and variables are defined as integers, and 
    permutations and freshness contexts are defined, 
    respectively, as lists of pairs of atoms x atoms
    and atoms x variables *)  
                   
type atom' = int              

type var' = int             
             
type perm' = (atom' * atom') list'
                             
type context' = (atom' * var') list'

(** f_term is the definition of the grammar of terms 
    in a signature that contains syntactic F_Fc, 
    associative A, associative-commutative AC and
    commutative C function symbols. Notice that,
    except for C, the argument of the function symbols
    are lists of f_terms. *)                                  
                               
type f_term =
| F_Ut
| F_At of atom'
| F_Ab of atom' * f_term
| F_Fc of int * f_term list'                  
| A of int * f_term list'
| AC of int * f_term list'                    
| C of int * f_term * f_term
| F_Su of perm' * var'


(** flat_term is a recursive function that in the case 
    of A and AC eliminates nested occurrences of the 
    same function symbol *)                    
           
let rec flat_term t =
  match t with
  | A (n, lt) -> A (n, f_term_to_list_A n lt) 
  | AC (n, lt) -> AC (n, f_term_to_list_AC n lt)
  | _ -> t

  and f_term_to_list_A n lt =
      match lt with
      | [] -> []
      | t :: lt0 ->
         match t with
         | A (n0, lt1) ->
            if (n = n0)
            then List.concat [f_term_to_list_A n lt1;
                              f_term_to_list_A n lt0]
            else t :: (f_term_to_list_A n lt0)
         | _ -> t :: (f_term_to_list_A n lt0)                               

  and f_term_to_list_AC n lt =
      match lt with
      | [] -> []
      | t :: lt0 ->
         match t with
         | AC (n0, lt1) ->
            if (n = n0)
            then List.concat [f_term_to_list_AC n lt1;
                              f_term_to_list_AC n lt0]
            else t :: (f_term_to_list_AC n lt0)
         | _ -> t :: (f_term_to_list_AC n lt0)   
        


(** The following concat_opt, iter_test1 to iter_test4, are
    functions used in the iteration over lists of terms,
    checking equivalence between f_terms, and also, in the case 
    of iter_test3 and iter_test4, building a representation
    of bipartite graph by a list of pairs of integers *)  

                          
let concat_opt opt_lu opt_lv =
  match opt_lu, opt_lv with
  | Some lu, Some lv -> Some (concat [lu; lv])
  | _, _ -> None
                          

let rec iter_test1 p l =
  match l with
  | [] -> true
  | u :: l0 -> if p u then iter_test1 p l0 else false          

let rec iter_test2 p lu lv =
  match lu, lv with
  | [], [] -> true
  | u :: lu0, v :: lv0 -> if p u v
                          then iter_test2 p lu0 lv0
                          else false
  | _, _ -> false                               

              
let rec iter_test3 p u lv i j =
  match lv with
  | [] -> []
  | v :: lv0 -> if p u v
               then concat [[(i,j)]; iter_test3 p u lv0 i (j + 1)]
               else iter_test3 p u lv0 i (j + 1)            
              
                            
let rec iter_test4 p lu lv i =
  match lu with
  | [] -> Some []  
  | u :: lu0 -> let l = iter_test3 p u lv i (length lv + 1) in
                match l with
                | [] -> None
                | l0 -> concat_opt (Some l0) (iter_test4 p lu0 lv (i + 1))




(** The following swapa', perm_act_aux' and perm_act' are recursive 
    functions that implement the action of permutations. Since
    the automatically generated Coq code has definitions with the 
    same names, and to avoid collisions, the prime character was added 
    at the end of each given function name. *)
                       
let swapa' s c =
  let (a, b) = s in
  if (a = c)
  then b
  else if (b = c)
       then a
       else c

              
let rec perm_act_aux' pi c =
  match pi with
  | [] -> c
  | s :: pi -> perm_act_aux' pi (swapa' s c)

                         
let rec perm_act' pi t =
  match t with  
  | F_Ut -> F_Ut
  | F_At a -> F_At (perm_act_aux' pi a)
  | F_Ab (a, s) -> F_Ab ((perm_act_aux' pi a), (perm_act' pi s))
  | F_Fc (n, ls) -> F_Fc (n, map (perm_act' pi) ls)                       
  | A (n, ls) -> A (n, map (perm_act' pi) ls)
  | AC (n, ls) -> AC (n, map (perm_act' pi) ls)
  | C (n, u, v) -> C (n, perm_act' pi u, perm_act' pi v)                    
  | F_Su (pi', x) -> F_Su (concat[pi'; pi], x)  


                                   
(** fresh_rec_F is a implementation of the checking of a is fresh for t in the 
    context c, where t is a f_term *)                                   
                          
let rec fresh_rec_F c a t =
  match t with
  | F_Ut -> true
  | F_At a0 -> if (a = a0) then false else true       
  | F_Ab (a0, s) -> if (a = a0) then true else fresh_rec_F c a s
  | F_Fc (n, ls) -> iter_test1 (fresh_rec_F c a) ls                        
  | A (n, ls) -> iter_test1 (fresh_rec_F c a) ls
  | AC (n, ls) -> iter_test1 (fresh_rec_F c a) ls            
  | C (n, u, v) -> if fresh_rec_F c a u
                   then fresh_rec_F c a v
                   else false               
  | F_Su (pi, x) -> if mem (perm_act_aux' (List.rev pi) a, x) c
                    then true
                    else false


(** The following definitions set_add', set_rem', set_union',
    dom_perm_aux', dom_perm' are used  in the differences set 
    operator disgr'. Definitions constr and is_sublist are 
    used in the definitions graph_equiv and impr_equiv that are, respectively, 
    in files Graph_Equiv.ml and Improved_Equiv.ml .  *)

let rec set_add' a l =
  match l with
  | [] -> [a]
  | a0 :: l0 -> if a = a0
                then l
                else a0 :: set_add' a l0
                                    
let rec set_rem' a l =
  match l with
  | [] -> []
  | b :: l0 -> if a = b
               then l0
               else b :: set_rem' a l0  


let rec set_union' l l' =
  match l, l' with
  | a :: l0, b :: l'0 -> if a = b
                         then a :: set_union' l l'
                         else a :: b :: set_union' l l'                     
  | [], l' -> l'
  | l, [] -> l
                
                                    
let rec atoms_perm' pi =
  match pi with
  | [] -> []  
  | (a, b)::pi0 -> set_add' b (set_add' a (atoms_perm' pi0))


let rec dom_perm_aux' pi atoms =
  match atoms with
  | [] -> []  
  | a :: atoms0 -> if (perm_act_aux' pi a) = a
                   then dom_perm_aux' pi atoms0
                   else (a :: (dom_perm_aux' pi atoms0))   

let dom_perm' pi = dom_perm_aux' pi (atoms_perm' pi)

let disgr' pi pi' = dom_perm' (concat [pi; List.rev pi'])

let constr x a = (a, x)                            
                                                    
let rec is_sublist l l' =
  match l with
  | [] -> true
  | a :: l0 -> if mem a l'
               then is_sublist l0 l'
               else false
