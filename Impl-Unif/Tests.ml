open Basic
open Unif
open Output      


let c_unif_tree qr = create_file unif_triple_string c_unif qr 

                                 
(** Unification Tests *)                                            

                                            
let qr1 = ([],[],[],[Equ (At "a", At "b")])

let qr2 = ([],[],[],[Equ (At "a", At "a")])

let qr3 = ([],[],[],[Fresh ("a", At "a"); Equ (Su ([],"Y"), Su ([],"X"))])

let qr4 = ([],[],[],[Equ (Su ([],"Y"), Fc ("E", "n", Su ([],"Y")))])

let qr5 = ([],[],[],[Equ (Ab ("a", Fc ("C", "n", Pr (At "b", At "a"))),
                          Ab ("b", Fc ("C", "n", Pr (At "a", At "b"))))])

let qr6 = ([],[],[],[Equ (Ab ("a", Fc ("C", "n", Pr (At "a", At "c"))),
                          Ab ("b", Fc ("C", "n", Pr (At "b", At "c"))))])            

let qr7 = ([("a","X")],[],[],[Equ (Ab ("a", (Fc ("C", "n", Pr (Fc ("E","m", At "a"), Su ([], "X"))))),
                                   Ab ("b", (Fc ("C", "n", Pr (Fc ("E","k", At "b"), Su ([], "X"))))))])

let qr8 = ([],[],[],[Equ (Su ([],"Y"), Su ([],"X"))])

let qr9 = ([],["X"],[],[Equ (Su ([],"Y"), Su ([],"X"))])            

let qr10 = ([],["Y"],[],[Equ (Su ([],"Y"), Su ([],"X"))])

let qr11 = ([],["Y"],[],[Equ (Su ([],"Y"), Fc ("E", "n", Su ([],"X")))])

let qr12 = ([],[],[],[Equ (Ab ("a", Ab ("b", Su ([], "X"))) ,
                          Ab ("b", Ab ("a", Su ([], "X"))))])

let qr13 = ([],["X"],[],[Equ (Ab ("a", Ab ("b", Su ([], "X"))) ,
                              Ab ("b", Ab ("a", Su ([], "X"))))])
            
let qr14 = ([],[],[],[Equ (Ab ("a'", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                          Ab ("b'", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let qr15 = ([],["X"],[],[Equ (Ab ("a'", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                              Ab ("b'", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let qr16 = ([],["Y"],[],[Equ (Ab ("a'", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                              Ab ("b'", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let qr17 = ([],["X"; "Y"],[],[Equ (Ab ("a'", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                                   Ab ("b'", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])   
             
let qr18 = ([],[],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y")))), Su ([], "Z"))),
                           Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Z"))))])

let qr19 = ([],["X"; "Z"],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y")))), Su ([], "Z"))),
                                   Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Z"))))])

let qr20 = ([],["X"; "Y"; "Z"],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y")))), Su ([], "Z"))),
                                        Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Z"))))])

let qr21 = ([],["X"; "Y"],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), At "b"))), Su ([], "Y"))),
                                   Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Y"))))])


let qr22 = ([],[],[],[Equ (Ab ("a'", Pr (Fc ("C", "n", Pr (Su ([("a","c")],"X"), Su ([("a","c");("b","c")],"Y"))), Su ([("a","d");("b","d");("c","d")], "X"))),
                           Ab ("b'", Pr (Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y"))), Su ([], "X"))))])


let qr23 = ([],[],[],[Equ (Fc ("C", "0", Pr (Fc ("C", "1", Pr (Su ([], "X"), Su ([], "Y"))), Fc ("C", "1", Pr (At "a", At "b")))),  
                           Fc ("C", "0", Pr (Fc ("C", "1", Pr (At "c", At "d")), Fc ("C", "1", Pr (Su ([], "Z"), Su ([], "W"))))))])

let qr24 = ([],["X"],[],[Equ (Fc ("C", "n", Pr (Su ([("a", "b")], "X"), Su ([("c", "d")], "X"))),
                              Fc ("C", "n", Pr (Su ([("c", "d");("b", "d");("a", "d")], "X"), Su ([], "X"))))])

let qr25 = ([],[],[],[Equ (Fc ("C", "0", Pr (Ab ("a", Ab ("c", Su ([], "X") )), Ab ("b", Ab ("d",  Su ([], "X"))))) ,
                           Fc ("C", "0", Pr (Ab ("c", Ab ("a", Su ([], "X") )), Ab ("d", Ab ("b",  Su ([], "X"))))))])
