(**
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Perfect_Matching.ml
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : This file contains an improved implementation of 
               A, AC and C equality checking algorithm that flattens terms 
               and simplifies the process of searching for a perfect
               matching in a bipartite graph, just searching for 
               pair of arguments of AC operators that are equivalent. 
               In the AC checking, since edges of the corresponding graph 
               represent equivalence between lhs and rhs arguments, 
               the process of finding a perfect matching is simplified
               drastically by just fixing an edge when such an edge is 
               detected.

 Last Modified On: Sep 18, 2018.
 ============================================================================
*)

open List
open Basics      
                      
                               
let rec impr_equiv c s t =

  match s, t with

  (** Unit *)

  | F_Ut, F_Ut -> true

  (** Atom term *)                  

  | F_At a, F_At b -> if (a = b) then true else false

  (** Abstraction *)
                                                  
  | F_Ab (a, u), F_Ab (b, v) ->
     if (a = b)
     then impr_equiv c u v
     else
       if fresh_rec_F c a v
       then
          impr_equiv c u (perm_act' [(a,b)] v)
       else false

  (** Syntactic function symbols.

      In this case the operator iter_test2 
      performs iteratively a check 
      between the ith's elements of lu and of lv. 
      This iterative process returns "false" only if 
      a k-th check returns "false" for k = 0 .. (length lu) - 1.
    
   *)             

  | F_Fc (n0, lu), F_Fc (n1, lv) ->
     if (n0 = n1)
     then
       if length lu = length lv 
       then iter_test2 (impr_equiv c) lu lv
       else false       
     else false

  (** Associative function symbols.
     
      For associative function symbols the checking 
      is the same as the syntactic case. 
      The only difference in whole process 
      is the pre-operation of flattening
      nested occurrences of A function symbols, 
      that is performed in the arguments before
      the application of impr_equiv. 
       
   *)

  | A (n0, lu), A (n1, lv) ->
     if (n0 = n1)
     then
       if length lu = length lv 
       then iter_test2 (impr_equiv c) lu lv
       else false       
     else false


  (** Associative-commutative function symbols.

    In the AC-checking impr_rec c (AC (n0, lu)) (AC (n1, lv)),
    first the conditions n0 = n1 and length lu = length lv are 
    verified. If both conditions are satisfied, an auxiliary 
    mutable array bool_array with size length u is initialised 
    with "false" in all its elements. Then the operators iter_test1    
    and iter_test2 are combined searching for each element of lu that 
    is equivalent to an element of lv. Notice that if u was checked 
    equivalent to v, theat are, 
    respectively, in the positions i of lu and j of lv, 
    with 0 <= i, j <= length lu, then the bool_array is changed to 
    "true" is the position j, and the iteration process moves to 
    check if u', that is the position i+1, is equivalent to any other element 
    in lv but not that ones whose the correspondent positions have 
    value "true" in the bool_array, including v. This approach 
    implements the idea of fixing edges between checked equivalent nodes 
    in a bipartite graph, solving the problem of searching 
    a perfect match. The representation of nodes and edges 
    is given directly by lists lu and lv the bool_array. 

   *)

  | AC (n0, lu), AC (n1, lv) ->
     if (n0 = n1)
     then
       
       if length lu = length lv
                             
       then let bool_array = Array.init (length lu) (fun i -> false) in

            let rec iter_test1 u lv i =
              (match lv with
               | [] -> None
               | v :: lv0 -> if bool_array.(i)
                                          
                             then iter_test1 u lv0 (i+1)
                                            
                             else
                               
                               if impr_equiv c u v
                                                  
                               then Some (bool_array.(i) <- true)

                               else iter_test1 u lv0 (i+1)) in
            

            let rec iter_test2 lu lv =
              (match lu with
                 
               | [] -> true
                         
               | u :: lu0 -> (match (iter_test1 u lv 0) with
                                
                              | None -> false
                                          
                              | _ -> iter_test2 lu0 lv)) in
            
               
            iter_test2 lu lv
           
       else false       
     else false

  (** Commutative function symbols. 
      
     The two cases of the C checking.
  
   *)
            
            
  | C (n0, u0, u1), C (n1, v0, v1) ->
     if (n0 = n1)
     then
       if impr_equiv c u0 v0
       then impr_equiv c u1 v1
       else
         if impr_equiv c u0 v1
         then impr_equiv c u1 v0
         else false   
     else false

  (** Suspensions.
    
      First the condition x = y is verified, then  
      the disagreements set between pi and pi'
      fresh to x must be a subset of c.

   *)
            
  | F_Su (pi, x), F_Su (pi', y) ->
     if (x = y)
     then is_sublist (map (constr x) (disgr' pi pi')) c
     else false

  (** All the other cases returns "false" *)

  | _, _ -> false




