open List

(** Inductive definitions **)

(** Trees **)       

type 'a tree =  
  | Leaf of string * 'a  
  | Node of string * 'a * (('a tree) list)        
             
(** Terms **)

type term =
  | Ut
  | At of string
  | Ab of string * term
  | Pr of term * term
  | Fc of string * string * term
  | Su of ((string * string) list) * string

(** Constraints **)
                                       
type constr =
  | Fresh of (string * term)
  | Equ of (term * term)             

                                       
(** Recursive functions **)


(** Adding an element in a list with prevention of element duplications **)

let set_add a l = if mem a l
                  then l
                  else a :: l

(** "Union" of two lists with prevention of element duplications **)
                                   
let rec set_union l l' =
  match l with
  | [] -> l'
  | a0 :: l0 -> set_add a0 (set_union l0 l')


(** "Intersection of two lists" **)

let rec set_inter l l' =
  match l with
  | [] -> []  
  | a0 :: l0 -> if mem a0 l'
                then set_add a0 (set_inter l0 l')
                else set_inter l0 l'             
          
             
(** Permutation action over atoms *)
             
let rec p_act pi (c : string) =
  match pi with
  | [] -> c
  | (a,b)::pi0 -> if a = c then p_act pi0 b else
                  if b = c then p_act pi0 a else p_act pi0 c  

(** Extension of permutation action to terms **)
                                                        
let rec p_act_t pi t =
  match t with
  | Ut -> Ut
  | At a -> At (p_act pi a)
  | Ab (a, s) -> Ab (p_act pi a, p_act_t pi s)
  | Pr (u, v) -> Pr (p_act_t pi u, p_act_t pi v)
  | Fc (e, n, s) -> Fc (e, n, p_act_t pi s)
  | Su (pi0, x) -> Su (pi0 @ pi, x) 


(** Atoms of a permutation *)
                      
let rec perm_atoms (pi : (string * string) list) =
  match pi with
  | [] -> []  
  | (a, b)::pi0 -> if (mem a (perm_atoms pi0))
                   then
                     if (mem b (perm_atoms pi0))
                     then perm_atoms pi0
                     else (b :: (perm_atoms pi0))
                   else
                     if (mem b (perm_atoms pi0)) 
                     then (a :: (perm_atoms pi0))
                     else (a :: b :: (perm_atoms pi0))
                            

(** Domain of a permutation **)                            
                      
let rec dom_perm_aux (pi : (string * string) list) (atoms  : string list) =
  match atoms with
  | [] -> []  
  | a :: atoms0 -> if (p_act pi a) = a
                   then dom_perm_aux pi atoms0
                   else (a :: (dom_perm_aux pi atoms0))   

let dom_perm pi = dom_perm_aux pi (perm_atoms pi)

                               
(** Disagreement set *)

let disagr pi pi' = dom_perm (pi @ (rev pi'))

                            
(** Context of an atom set fresh to a variable **)

let rec fresh_atoms (atoms : string list) (x : string) =
  match atoms with
  | [] -> []
  | a :: atoms0 -> (a, x) :: (fresh_atoms atoms0 x) 
                       


(** Length of a tuple regarding the nth E function symbol **)

let rec tplength t (lb : string * string) =
  
  match t with 

  | Pr (s,t) -> (tplength s lb) + (tplength t lb) 

  | Fc (e, n, s)  -> if (e, n) = lb then (tplength s (e, n)) else 1
                                                                     
  | _ -> 1  


(** ith argument from the tuple t, argument of the nth E function symbol **)

let rec tpith i t lb =
  
  match t with 

  | Pr (u,v) ->  let l1 = (tplength u lb) in 
                 if i <= l1
                 then (tpith i u lb)
                 else (tpith (i-l1) v lb)   

  | Fc (e, n, s) -> if (e,n) = lb
                    then (tpith i s lb) 
                    else t
                             
  | _  -> t


(** Eliminates the ith argument in the tuple t, argument of the nth E function symbol **)

let rec tpithdel i t lb =
  
  match t with 

 | Pr (u,v) -> let l1 = (tplength u lb) in 
               let l2 = (tplength v lb) in 
               if i <= l1
               then 
                 if l1 = 1
                 then v 
                 else Pr (tpithdel i u lb, v)
               else
                 let ii = i-l1 in   
                 if l2 = 1
                 then u
                 else Pr (u, tpithdel ii v lb) 

 | Fc (e, n, s) -> if (tplength (Fc (e, n, s)) lb) = 1
                   then Ut
                   else Fc (e, n, tpithdel i s lb)
                               
                               
 | _ -> Ut


(** Variables that occur in a term **)

let rec vars t =
  match t with
  | Ab (a, s) -> vars s
  | Pr (u, v) -> (vars u) @ (vars v)
  | Fc (e, n, s) -> vars s
  | Su (pi, x) -> [x]
  | _ -> []                  

(** Variables that occur in a list of constraints **)
           
let rec prb_vars ctrl =
  match ctrl with
  | [] -> []
  | Fresh (a, t) :: ctrl0 -> set_union (vars t) (prb_vars ctrl0)
  | Equ (s, t) :: ctrl0 -> set_union (set_union (vars s) (vars t)) (prb_vars ctrl0)

(** Variables that occur in the equations **)
           
let rec prb_eq_vars ctrl =
  match ctrl with
  | [] -> []
  | Fresh (a, t) :: ctrl0 -> prb_eq_vars ctrl0
  | Equ (s, t) :: ctrl0 -> set_union (set_union (vars s) (vars t)) (prb_eq_vars ctrl0)                                           
                                                                  

(** Auxiliar function to build substituion action **)                      
                      
let rec look_up (x : string) (sub : (string * term) list) =
  match sub with
  | [] -> Su ([],x)
  | (y,t)::s0  -> if y = x then t else (look_up x s0)

                                         
(** Substition action *)
                                         
let rec sub_act (t : term) sub  =
  match  t with
  | Ut -> Ut
  | At a -> At a  
  | Ab (a, s) -> Ab (a, sub_act s sub)
  | Pr (u, v) -> Pr (sub_act u sub, sub_act v sub)
  | Fc (e, n, s) -> Fc (e, n, sub_act s sub)
  | Su (pi, x) -> p_act_t pi (look_up x sub)

                          
(** Alist_rec allows the construction of a fuction of composition of substitutions *)

let rec alist_rec s1 (s2 : (string * term) list) f  =
  match s1 with
  | [] -> s2
  | (x,t)::s0 -> f x t s2 (alist_rec s0 s2 f)
                  
let f_rec s1 (x : string) t (s2 : (string * term) list) s3 = (x, sub_act t s1)::s3 

(** Composition of two substitutions *)
                                                                                  
let sub_comp s1 s2 = alist_rec s1 s2 (f_rec s2)          
          
(** Generating freshness contraints by a freshness context and a substitution **) 

let rec sub_fresh c s =
  match c with
  | [] -> []
  | (a, x) :: c0 -> (if look_up x s <> Su ([], x)
                     then [Fresh (a, look_up x s)]
                     else []) @ sub_fresh c0 s                                    
                               
(** Applying a substitution to a list of constraints **)

let rec sub_prb prb s =
  match prb with
  | [] -> []
  | Fresh (a, t) :: prb0 -> Fresh (a, sub_act t s) :: sub_prb prb0 s 
  | Equ (u, v) :: prb0 -> Equ (sub_act u s, sub_act v s) :: sub_prb prb0 s



(** Verifies if a constraint is a fixpoint equation **)

let is_fixpoint_equ ctr =
  match ctr with
  | Fresh (a, u) -> false      
  | Equ (Su (pi, x), Su ([], y)) -> if x = y && pi <> []
                                    then true else false
  | _ -> false                                                   
                                           
(** Verifies if the equational part of a problem is a set of fixpoint equations **)
                                                                    
let rec is_fixpoint_set prb =
  match prb with
  | [] -> true
  | Fresh (a, u) :: prb0 -> is_fixpoint_set prb0         
  | Equ (s, t) :: prb0 -> if is_fixpoint_equ (Equ (s, t))
                          then is_fixpoint_set prb0
                          else false                                                                  

(** Verifies if a problem contains only freshness constraints **)
                                                                    
let rec is_freshness_set prb =
  match prb with
  | [] -> true
  | Fresh (a, u) :: prb0 -> is_freshness_set prb0         
  | Equ (s, t) :: prb0 -> false

(** Verifies if a problem contains freshness constraints *)

let rec has_freshness prb =
  match prb with
  | [] -> false
  | Fresh (a, u) :: prb0 -> true         
  | Equ (s, t) :: prb0 -> has_freshness prb0                            
                                 
   
(** Verifies if a problem is composed only by equations *) 

let rec is_equation_set prb =
  match prb with
  | [] -> true
  | Fresh (a, u) :: prb0 -> false
  | Equ (u, v) :: prb0 -> is_equation_set prb0    
