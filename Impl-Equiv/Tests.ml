open Basic
open Equiv
       

(** Equiv tests **)                                      

let eq1 = ([], At "a", At "a")
            
let eq2 = ([], Su ([("a", "b")], "x"), Su ([("b", "c")], "x"))

let eq3 = (("a", "x")::("b", "x")::[("c", "x")], Su ([("a", "b")], "x"), Su ([("b", "c")], "x"))
            
let eq4 = (("a", "x")::[("b", "x")], Su ([("a", "b")], "x"), Su ([("b", "c")], "x"))
            
let eq5 = ([], Ab ("a", At "a"), Ab ("b", At "b"))
            
let eq6 = ([], Ab ("a", At "a"), Ab ("b", At "c")) 

let eq7 = ([], Fc ("E", "n", At "a"), Fc ("E0", "n", At "a"))

let eq8 = ([], Fc ("E", "n", At "a"), Fc ("E", "n0", At "a"))            

let eq9 = ([], Fc ("E", "n", Ab ("a", At "a")), Fc ("E", "n", Ab ("b", At "b")))

let eq10 = ([], Fc ("E", "n", Pr (Pr (At "a", At "b"), At "c")),
                Fc ("E", "n", Pr (At "a", Pr (At "b", At "c"))))                

let eq11 = ([], Fc ("A", "n", Pr (Pr (At "a", At "b"), At "c")),
                Fc ("A", "n", Pr (At "a", Pr (At "b", At "c"))))

let eq12 = ([], Fc ("A", "n", Pr (Pr (At "a", At "b"), At "c")),
                Fc ("A", "n", Pr (At "c", Pr (At "a", At "b"))))

let eq13 = ([], Fc ("AC", "n", Pr (Pr (At "a", At "b"), At "c")),
                Fc ("AC", "n", Pr (At "c", Pr (At "a", At "b"))))

let eq14 = ([], Fc ("E", "n", Pr (At "a", At "b")),
                Fc ("E", "n", Pr (At "b", At "a")))              

let eq15 = ([], Fc ("C", "n", Pr (At "a", At "b")),
                Fc ("C", "n", Pr (At "b", At "a")))

let eq16 = ([], Fc ("A", "n", Ab ("a", At "a")), Fc ("A", "n", Ab ("b", At "b")))
             
let eq17 = ([], Fc ("AC", "n", Ab ("a", At "a")), Fc ("AC", "n", Ab ("b", At "b")))             

let eq18 = ([], Fc ("C", "n", Ab ("a", At "a")), Fc ("C", "n", Ab ("b", At "b")))


      


