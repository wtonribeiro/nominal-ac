(**
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Graph_Equiv.ml
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : Implementation of the A, C and AC equality checking
               algorithm using the Perfect_Matching.ml algorithm.
               This is a very inefficient solution since for equality
               checking one just need to detect equivalences among
               arguments of AC operators. But perfect matchings will
               be required when one will deal with matching and 
               unification.     

 Last Modified On: Sep 18, 2018.
 ============================================================================
*)

open Basics
open Perfect_Matching
open List       
                               
let rec graph_equiv c s t =

  match s, t with

  | F_Ut, F_Ut -> true

  | F_At a, F_At b -> if (a = b) then true else false
                                                  
  | F_Ab (a, u), F_Ab (b, v) ->
     if (a = b)
     then graph_equiv c u v
     else
       if fresh_rec_F c a v
       then
          graph_equiv c u (perm_act' [(a,b)] v)
       else false

  | F_Fc (n0, lu), F_Fc (n1, lv) ->
     if (n0 = n1)
     then
       if length lu = length lv 
       then iter_test2 (graph_equiv c) lu lv
       else false       
     else false       

  | A (n0, lu), A (n1, lv) ->
     if (n0 = n1)
     then
       if length lu = length lv 
       then iter_test2 (graph_equiv c) lu lv
       else false       
     else false

  | AC (n0, lu), AC (n1, lv) ->
     if (n0 = n1)
     then
       if length lu = length lv 
       then let op_l = iter_test4 (graph_equiv c) lu lv 1 in
            (match op_l with
             | Some l -> perfect_match l (length lu) 
             | None -> false)
       else false       
     else false

  | C (n0, u0, u1), C (n1, v0, v1) ->
     if (n0 = n1)
     then
       if graph_equiv c u0 v0
       then graph_equiv c u1 v1
       else
         if graph_equiv c u0 v1
         then graph_equiv c u1 v0
         else false   
     else false
            
  | F_Su (pi, x), F_Su (pi', y) ->
     if (x = y)
     then is_sublist (map (constr x) (disgr' pi pi')) c
     else false

  | _, _ -> false




