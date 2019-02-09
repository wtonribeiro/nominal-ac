open List
open Basic                     

                   
(** Equational Rules **)                                             

                                            
let rec equ_sys (qr : ((string * string) list) * (string list) * ((string * term) list) * (constr list) ) =
 
  match qr with
    
  | (c, varSet, s, []) -> Leaf ("\\top", (c, varSet, s, []))            

   (*** ~ Refl : Ut ***)   
            
  | (c, varSet, s, Equ (Ut, Ut) :: prb) ->
     Node ("\\approx_? refl", qr,  [equ_sys (c, varSet, s, prb)])

          
  (*** ~ Refl : At ***)                                        
                                         
                                         
  | (c, varSet, s, Equ (At a, At b) :: prb) ->
     if a = b
     then Node ("\\approx_? refl", qr, [equ_sys (c, varSet, s, prb)])
     else Leaf ("\\bot", qr)
     
                          
  (*** ~ [aa] / [ab] ***)                         


  | (c, varSet, s, Equ (Ab (a, u0), Ab (b , u1)) :: prb) ->

      if a = b
      then
        let label = "\\approx_? [aa]" in
        let rec_call = equ_sys (c, varSet, s, set_add (Equ (u0, u1)) prb) in
         Node (label, qr, [rec_call])
      else 
        let label = "\\approx_? [ab]" in
        let rec_call = equ_sys (c, varSet, s, set_add (Equ (u0, p_act_t [(a, b)] u1)) (set_add (Fresh (a, u1)) prb)) in
         Node (label, qr, [rec_call])
     
                             
  (*** ~ C ***)

  | (c, varSet, s, Equ (Fc (e0, n0, (Pr (u0, v0))), Fc (e1, n1, (Pr (u1, v1)))) :: prb) ->
    
     if (e0 = e1) && (n0 = n1)
                       
     then  

       if (e0 <> "C")
       then Node ("\\approx_? app \\& pair", qr, [equ_sys (c, varSet, s, set_add (Equ (u0, u1)) (set_add (Equ (v0, v1)) prb))])
       else Node ("\\approx_? C", qr, [equ_sys (c, varSet, s, set_add (Equ (u0, u1)) (set_add (Equ (v0, v1)) prb));
                                       equ_sys (c, varSet, s, set_add (Equ (u0, v1)) (set_add (Equ (v0, u1)) prb))])

     else Leaf ("\\bot", qr)

                                                     
  (*** ~ App ***)          
                           
  | (c, varSet, s, Equ (Fc (e0, n0, u0), Fc (e1, n1, u1)) :: prb) ->

     if ((e0 = e1) && (n0 = n1))

     then Node ("\\approx_? app", qr,
                 [equ_sys (c, varSet, s, set_add (Equ (u0, u1)) prb)] )

     else Leaf ("\\bot", qr)


   (*** Pr ***)
                      
                      
  | (c, varSet, s, Equ (Pr (u0, v0), Pr (u1 ,v1)) :: prb) ->
     Node ("\\approx_? pair", qr, 
    [equ_sys (c, varSet, s, set_add (Equ (u0, u1)) (set_add (Equ (v0, v1)) prb))])                          



  (*** Inv / Refl ***)                          

  | (c, varSet, s, Equ (Su (pi, x), Su (pi', y)) :: prb) ->
     
      if x = y

      then if pi = pi'

           then Node ("\\approx_? refl", qr, [equ_sys (c, varSet, s, prb)])
                     
           else if pi' = []

                then if is_fixpoint_set prb

                     then Leaf ("\\top", qr)

                     else equ_sys (c, varSet, s, prb @ [Equ (Su (pi, x), Su (pi', y))])
                  
                else Node ("\\approx_? inv", qr, [equ_sys (c, varSet, s, prb @ [Equ (Su (pi @ (rev pi'), x), Su ([], x))])])

      else               
                          
  (*** Inst ***)

        if not (mem x varSet)

        then let s' = sub_comp s [(x, Su (pi' @ (rev pi), y))] in
             Node ("\\approx_? inst", qr, [equ_sys (c, varSet, s', (sub_prb prb [(x, Su (pi' @ (rev pi), y))]) @ sub_fresh c s')])
                
        else Leaf ("\\bot", qr)
                                                                                   
                    
  | (c, varSet, s, Equ (Su (pi, x), t) :: prb) ->
     
      if (not (mem x (vars t)) && not (mem x varSet))

      then let s' = sub_comp s [(x, p_act_t (rev pi) t)] in
           Node ("\\approx_? inst", qr, [equ_sys (c, varSet, s', (sub_prb prb [(x, p_act_t (rev pi) t)]) @ sub_fresh c s')])
                
      else Leaf ("\\bot", qr)


 | (c, varSet, s, Equ (t, Su (pi, x)) :: prb) ->
     
      if not ((mem x (vars t)) && not (mem x varSet))

      then let s' = sub_comp s [(x, p_act_t (rev pi) t)] in
           Node ("\\approx_? inst", qr, [equ_sys (c, varSet, s', (sub_prb prb [(x, p_act_t (rev pi) t)]) @ sub_fresh c s')])
                
      else Leaf ("\\bot", qr)


 (*** Freshness constaints are ignored **)
                
 | (c, varSet, s, Fresh (a, u) :: prb) ->

    if is_fixpoint_set prb

    then Leaf ("\\top", qr)

    else equ_sys (c, varSet, s, prb @ [Fresh  (a, u)])                  


 (*** Remaining cases are leaves of fail **)                  
                       
 | (c, varSet, s, _ :: prb) -> Leaf ("\\bot", qr)                          



(******************************************)


(** Freshness Rules **)                                                               
                               
let rec fresh_sys qr  =

  match qr with

  | (c, varSet, s, []) -> Leaf ("\\top", (c, varSet, s, [])) 
    

  (** # Ut **)

  | (c, varSet, s, Fresh (a, Ut) :: prb) -> Node ("\\#_?\\, \\langle\\rangle", qr, [fresh_sys (c, varSet, s, prb)])
                                             
  (** # At **)                                       
                                         
  | (c, varSet, s, Fresh (a, At b) :: prb) ->

      if a <> b
                                                       
      then Node ("\\#_?\\, a\\bar{b}", qr, [fresh_sys (c, varSet, s, prb)])
                  
      else Leaf ("\\bot", qr)     

 
  (** # [aa] / [ab] **)

  | (c, varSet, s, Fresh (a, Ab (b, t)) :: prb) ->
     
      if a = b
                               
      then Node ("\\#_?\\, a[a]", qr, [fresh_sys (c, varSet, s, prb)])
                          
      else Node ("\\#_?\\, a[b]", qr, [fresh_sys (c, varSet, s, set_add (Fresh (a, t)) prb)])


  (** # Pr **)                                                              
                                                                 
  | (c, varSet, s, Fresh (a, Pr (u, v)) :: prb) ->
     Node ("\\#_?\\, pair", qr, [fresh_sys (c, varSet, s, set_add (Fresh (a, u)) (set_add (Fresh (a, v)) prb))]) 
                                                                         

  (** Fc **)
                                                                         
  | (c, varSet, s, Fresh (a, Fc (e, n, t)) :: prb) ->
     Node ("\\#_?\\, app", qr, [fresh_sys (c, varSet, s, set_add (Fresh (a, t))  prb)]) 


  (** Su **)                                                       
                                                         
  | (c, varSet, s, Fresh (a, Su (pi, x)) :: prb) ->
     Node ("\\#_?\\, var", qr, [fresh_sys (set_add (p_act (rev pi) a, x) c, varSet, s, prb)])


  (** Fixed point equations **)                                                                
                                                                  
  | (c, varSet, s, Equ (Su (pi, x), Su ([], y)) :: prb) ->

     if x = y then

        if mem x varSet

        then Node ("\\mu_{fp}", qr, [fresh_sys (set_union (fresh_atoms (dom_perm pi) x) c, varSet, s, prb)])

        else if ((set_inter varSet (prb_eq_vars prb) != []) || has_freshness prb)

             then fresh_sys (c, varSet, s, prb @ [Equ (Su (pi, x), Su ([], x))])

             else Leaf ("\\top", qr)

     else Leaf ("\\bot", qr)
               

  (** Other equations **)

  | (c, varSet, s, Equ (u, v) :: prb ) -> Leaf ("\\bot", qr)       
     

(******************************************)                 


let rec app_fresh_tree tree =
                   
  match tree with
    
  | Leaf (lab, qr0) ->

     if lab = "\\top"

     then fresh_sys qr0

     else tree

  | Node (lab, qr0, tree_list) ->

      Node (lab, qr0, List.map app_fresh_tree tree_list)
                      
      

(** The C-unification algorithm **)

let c_unif qr =
  app_fresh_tree (equ_sys qr)


(** c_unif_str outputs list with the successful triples **)                  

let rec c_unif_str qrl =
  match qrl with

  | [] -> []
    
  | Leaf (lab, qr) :: qrl0 ->
     
     (if lab = "\\top"
      then [qr]
      else []) @ c_unif_str qrl0
                                    
  | Node (_, _, qrl0) :: qrl1 -> c_unif_str qrl0 @
                                 c_unif_str qrl1

                  
                   



                          

                   



                                                  
