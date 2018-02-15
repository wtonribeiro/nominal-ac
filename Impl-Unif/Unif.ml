open List
open Basic                     

                   
(** Equational Rules **)                                             

                                            
let rec equiv_sys (tr : ((string * string) list) * ((string * term) list) * (constr list) ) =
 
  match tr with
    
  | (c, s, []) -> Leaf ("\\approx Success", (c, s, []))            

   (*** ~ Refl : Ut ***)   
            
  | (c, s, Equ (Ut, Ut) :: prb) ->
     Node ("\\approx Refl", tr,  [equiv_sys (c, s, prb)])

          
  (*** ~ Refl : At ***)                                        
                                         
                                         
  | (c, s, Equ (At a, At b) :: prb) ->
     if a = b
     then Node ("\\approx Refl", tr, [equiv_sys (c, s, prb)])
     else Leaf ("\\approx Fail", tr)
     
                          
  (*** ~ [aa] / [ab] ***)                         


  | (c, s, Equ (Ab (a, u0), Ab (b , u1)) :: prb) ->

      if a = b
      then
        let label = "\\approx [aa]" in
        let rec_call = equiv_sys (c, s, Equ (u0, u1) :: prb) in
         Node (label, tr, [rec_call])
      else 
        let label = "\\approx [ab]" in
        let rec_call = equiv_sys (c, s, (Equ (u0, p_act_t [(a, b)] u1)) :: (Fresh (a, u1)) :: prb) in
         Node (label, tr, [rec_call])
     
                             
  (*** ~ C ***)

  | (c, s, Equ (Fc (e0, n0, (Pr (u0, v0))), Fc (e1, n1, (Pr (u1, v1)))) :: prb) ->
    
     if (e0 = e1) && (n0 = n1)
                       
     then  

       if (e0 <> "C")
       then Node ("\\approx C", tr, [equiv_sys (c, s, Equ (u0, u1) :: Equ (v0, v1) :: prb)])
       else Node ("\\approx C", tr, [equiv_sys (c, s, Equ (u0, u1) :: Equ (v0, v1) :: prb); equiv_sys (c, s, Equ (u0, v1) :: Equ (v0, u1) :: prb)])

     else Leaf ("\\approx Fail", tr)

                                                     
  (*** ~ App ***)          
                           
  | (c, s, Equ (Fc (e0, n0, u0), Fc (e1, n1, u1)) :: prb) ->

     if ((e0 = e1) && (n0 = n1))

     then Node ("\\approx App", tr,
                 [equiv_sys (c, s, Equ (u0, u1) :: prb)] )

     else Leaf ("\\approx Fail", tr)


   (*** Pr ***)
                      
                      
  | (c, s, Equ (Pr (u0, v0), Pr (u1 ,v1)) :: prb) ->
     Node ("\\approx Pr", tr, 
    [equiv_sys (c, s, (Equ (u0, u1)) :: (Equ (v0, v1)) :: prb)])                          



  (*** Inv / Refl ***)                          

  | (c, s, Equ (Su (pi, x), Su (pi', y)) :: prb) ->
     
     if is_fixpoint_equ (Equ (Su (pi, x), Su (pi', y)))
                        
     then if is_fixpoint_set prb
                             
          then Leaf ("\\approx Success", tr)
                    
          else equiv_sys (c, s, prb @ [Equ (Su (pi, x), Su (pi', y))])
                         
      else if x = y

           then if pi' <> []

                then Node ("\\approx Inv", tr, [equiv_sys (c, s, prb @ [Equ (Su (pi @ (rev pi'), x), Su ([], x))])])

                else Node ("\\approx Refl", tr, [equiv_sys (c, s, prb)])
                          
                          
  (*** Inst ***)
                                                                                         
           else let s' = sub_comp s [(x, Su (pi' @ (rev pi), y))] in
                Node ("\\approx Inst", tr, [equiv_sys (c, s', (sub_prb prb [(x, Su (pi' @ (rev pi), y))]) @ sub_fresh c s')])

                    
  | (c, s, Equ (Su (pi, x), t) :: prb) ->
     
      if not (mem x (vars t))

      then let s' = sub_comp s [(x, p_act_t (rev pi) t)] in
           Node ("\\approx Inst", tr, [equiv_sys (c, s', (sub_prb prb [(x, p_act_t (rev pi) t)]) @ sub_fresh c s')])
                
      else Leaf ("\\approx Fail", tr)


 | (c, s, Equ (t, Su (pi, x)) :: prb) ->
     
      if not (mem x (vars t))

      then let s' = sub_comp s [(x, p_act_t (rev pi) t)] in
           Node ("\\approx Inst", tr, [equiv_sys (c, s', (sub_prb prb [(x, p_act_t (rev pi) t)]) @ sub_fresh c s')])
                
      else Leaf ("\\approx Fail", tr)


 (*** Freshness constaints are ignored **)
                
 | (c, s, Fresh (a, u) :: prb) ->

    if is_fixpoint_set prb

    then Leaf ("\\approx Success", tr)

    else equiv_sys (c, s, prb @ [Fresh  (a, u)])


 (*** Remaining cases are leaves of fail **)                  
                       
 | (c, s, _ :: prb) -> Leaf ("\\approx Fail", tr)                          




(** Freshness Rules **)                                                               
                               
let rec fresh_sys tr  =

  match tr with

  | (c, s, []) -> Leaf ("\\# Success", (c, s, [])) 
    

  (** # Ut **)

  | (c, s, Fresh (a, Ut) :: prb) -> Node ("\\# Ut", tr, [fresh_sys (c, s, prb)])
                                             
  (** # At **)                                       
                                         
  | (c, s, Fresh (a, At b) :: prb) ->

      if a <> b
                                                       
      then Node ("\\# At", tr, [fresh_sys (c, s, prb)])
                  
      else Leaf ("\\# Fail", tr)     

 
  (** # [aa] / [ab] **)

  | (c, s, Fresh (a, Ab (b, t)) :: prb) ->
     
      if a = b
                               
      then Node ("\\# [aa]", tr, [fresh_sys (c, s, prb)])
                          
      else Node ("\\# [ab]", tr, [fresh_sys (c, s, Fresh (a, t) :: prb)])


  (** # Pr **)                                                              
                                                                 
  | (c, s, Fresh (a, Pr (u, v)) :: prb) -> Node ("\\# Pr", tr, [fresh_sys (c, s, Fresh (a, u) :: Fresh (a, v) :: prb)]) 
                                                                         

  (** Fc **)
                                                                         
  | (c, s, Fresh (a, Fc (e, n, t)) :: prb) -> Node ("\\# App", tr, [fresh_sys (c, s, Fresh (a, t) :: prb)]) 


  (** Su **)                                                       
                                                         
  | (c, s, Fresh (a, Su (pi, x)) :: prb) -> Node ("\\# Su", tr, [fresh_sys ((p_act (rev pi) a, x) :: c, s, prb)])


  (** Equations **)                                                                
                                                                  
  | (c, s, Equ (u, v) :: prb) ->

      if is_equation_set prb

      then Leaf ("\\# Success", tr)

      else fresh_sys (c, s, prb @ [Equ (u, v)])          
     



let rec app_fresh_tree tree =
                   
  match tree with
    
  | Leaf (lab, tr0) ->

     if lab = "\\approx Success"

     then fresh_sys tr0

     else tree

  | Node (lab, tr0, tree_list) ->

      Node (lab, tr0, List.map app_fresh_tree tree_list)
                      
      

(** The C-unification algorithm **)

let c_unif tr =
  app_fresh_tree (equiv_sys tr)


(** c_unif_str outputs list with the successful triples **)                  

let rec c_unif_str trl =
  match trl with

  | [] -> []
    
  | Leaf (lab, tr) :: trl0 ->
     
     (if lab = "\\approx Success"
      then [tr]
      else []) @ c_unif_str trl0
                                    
  | Node (_, _, trl0) :: trl1 -> c_unif_str trl0 @
                                 c_unif_str trl1

                  
                   



                          

                   



                                                  
