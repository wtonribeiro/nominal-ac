open Basic
open Unif
open Output      


let c_unif_tree tr = create_file unif_triple_string c_unif tr 

                                 
(** Unif Tests *)                                            

                                            
let tr1 = ([],[],[Equ (At "a", At "b")])

let tr2 = ([],[],[Equ (At "a", At "a")])

let tr3 = ([],[], [Fresh ("a", At "a"); Equ (Su ([],"Y"), Su ([],"X"))])

let tr4 = ([],[],[Equ (Ab ("e", Fc ("C", "n", Pr (At "e", At "a"))),
                       Ab ("e", Fc ("C", "n", Pr (At "e", At "a"))))])

let tr5 = ([],[],[Equ (Ab ("e", Fc ("C", "n", Pr (At "e", At "a"))),
                       Ab ("f", Fc ("C", "n", Pr (At "f", At "a"))))])            
     
let tr6 = ([],[],[Equ (Ab ("a", Ab ("b", Su ([], "X"))) ,
                       Ab ("b", Ab ("a", Su ([], "X"))))])             
            
let tr7 = ([],[],[Equ (Ab ("e", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                       Ab ("f", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let tr8 = ([("a","X")],[], [Equ (Ab ("a", (Fc ("C", "n", Pr (Fc ("E","m", At "a"), Su ([], "X"))))),
                                 Ab ("b", (Fc ("C", "n", Pr (Fc ("E","k", At "b"), Su ([], "X"))))))])
      


