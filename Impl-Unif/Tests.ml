open Basic
open Unif
open Output      


let c_unif_tree qr = create_file unif_triple_string c_unif qr 

                                 
(** Unif Tests *)                                            

                                            
let qr1 = ([],[],[],[Equ (At "a", At "b")])

let qr2 = ([],[],[],[Equ (At "a", At "a")])

let qr3 = ([],[],[],[Fresh ("a", At "a"); Equ (Su ([],"Y"), Su ([],"X"))])

let qr4 = ([],[],[],[Equ (Ab ("e", Fc ("C", "n", Pr (At "e", At "a"))),
                       Ab ("e", Fc ("C", "n", Pr (At "e", At "a"))))])

let qr5 = ([],[],[],[Equ (Ab ("e", Fc ("C", "n", Pr (At "e", At "a"))),
                       Ab ("f", Fc ("C", "n", Pr (At "f", At "a"))))])            
     
let qr6 = ([],[],[],[Equ (Ab ("a", Ab ("b", Su ([], "X"))) ,
                       Ab ("b", Ab ("a", Su ([], "X"))))])             
            
let qr7 = ([],[],[],[Equ (Ab ("a'", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                       Ab ("b'", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let qr8 = ([("a","X")],[],[],[Equ (Ab ("a", (Fc ("C", "n", Pr (Fc ("E","m", At "a"), Su ([], "X"))))),
                                   Ab ("b", (Fc ("C", "n", Pr (Fc ("E","k", At "b"), Su ([], "X"))))))])

let qr9 = ([],[],[],[Equ (Su ([],"Y"), Su ([],"X"))])

let qr10 = ([],["X"],[],[Equ (Su ([],"Y"), Su ([],"X"))])            

let qr11 = ([],["Y"],[],[Equ (Su ([],"Y"), Su ([],"X"))])

let qr12 = ([],["X"],[],[Equ (Ab ("a", Ab ("b", Su ([], "X"))) ,
                              Ab ("b", Ab ("a", Su ([], "X"))))])

let qr13 = ([],["X"],[],[Equ (Ab ("e", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                              Ab ("f", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let qr14 = ([],["Y"],[],[Equ (Ab ("e", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                              Ab ("f", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])

let qr15 = ([],["X"; "Y"],[],[Equ (Ab ("e", Fc ("C", "n", Pr (Su ([("a","b")],"X"), Su ([],"Y")))),
                                   Ab ("f", Fc ("C", "n", Pr (Su ([("a","c");("c","d")],"X"), Su ([],"Y")))))])   

let qr16 = ([],[],[],[Equ (Su ([],"Y"), Fc ("E", "n", Su ([],"Y")))])

let qr17 = ([],["Y"],[],[Equ (Su ([],"Y"), Fc ("E", "n", Su ([],"X")))])

             
let qr18 = ([],[],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y")))), Su ([], "Z"))),
                           Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Z"))))])

let qr19 = ([],["X"; "Z"],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y")))), Su ([], "Z"))),
                                   Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Z"))))])


let qr20 = ([],["X"; "Y"; "Z"],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), Su ([],"Y")))), Su ([], "Z"))),
                                        Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Z"))))])


let qr21 = ([],["X"; "Y"],[],[Equ (Ab ("a", Pr (Ab ("b", Fc ("C", "n", Pr (Su ([],"X"), At "b"))), Su ([], "Y"))),
                                   Ab ("b", Pr (Ab ("a", Fc ("C", "n", Pr (At "a", Su ([],"X")))), Su ([], "Y"))))])

