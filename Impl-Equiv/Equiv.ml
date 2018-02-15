open List
open Basic

(** Freshness checking **)

let rec fresh (c, a, t) =

  match t with
  
  | Ut -> true

  | At b -> if a = b then false else true

  | Ab (b, s) -> if a = b
                 then true
                 else fresh (c, a, s)

  | Pr (u, v) -> (fresh (c, a, u)) && (fresh (c, a, v))

  | Fc (e, n, s) -> fresh (c, a, s)

  | Su (pi, x) -> if mem (p_act (rev pi) a, x) c
                  then true
                  else false       

       
                    
(** alpha, A, AC and C - equational checking **)                                             
                         
let rec equiv (c, s, t) =
  
  match (s, t) with
    
  | (Ut, Ut) -> true

  | (At a, At b) -> if a = b then true else false

  | (Ab (a, u), Ab (b, v)) -> if a = b
                              then equiv (c, u, v)
                              else (fresh (c, a, v)) && (equiv (c, u, (p_act_t [(a, b)] v))) 

  | (Pr (u0, u1), Pr (v0, v1)) -> (equiv (c, u0, v0)) && (equiv (c, u1, v1))

                                                     
  | (Fc (e0, n0, Pr (u0, u1)), Fc (e1, n1, Pr (v0, v1))) ->
     
     if (e0, n0) = (e1, n1)
                     
        then
                             
          if e0 = "A"
          then equiv (c, (tpith 1 s (e0, n0)), (tpith 1 t (e0, n0))) &&
               equiv (c, (tpithdel 1 s (e0, n0)), (tpithdel 1 t (e0, n0)))
          else
                                
            if e0 = "AC"
            then
              
              let rec ac_check i =
                  if tplength s (e0, n0) = tplength t (e0, n0)  
                  then
                    
                    if i <= tplength s (e0, n0)
                    then
                      
                      if (equiv (c, (tpith 1 s (e0, n0)), (tpith i t (e0, n0))))
                           
                      then (equiv (c, (tpithdel 1 s (e0, n0)), (tpithdel i t (e0, n0))))
                             
                      else ac_check (i+1)
                                    
                    else false 
                  else false
                                                
              in ac_check 1
                                                 
            else             

              if e0 = "C"
              then
                if (equiv (c, u0, v0)) && (equiv (c, u1, v1))
                then true
                else (equiv (c, u0, v1)) && (equiv (c, u1, v0))
              else (equiv (c, u0, v0)) && (equiv (c, u1, v1))
                                                                
     else false                             
 
                                    
  | (Fc (e0, n0, u), Fc (e1, n1, v)) -> if (e0, n0) = (e1, n1)
                                        then equiv (c, u, v)
                                        else false

  | (Su (pi, x), Su (pi', y)) -> if (x = y) &&
                                 is_sublist (fresh_atoms (disagr pi pi') x) c
                                 then true
                                 else false

  | ( _ , _ ) -> false           
