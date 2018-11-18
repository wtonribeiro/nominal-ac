open Basic
open Printf  

(*** Generating latex code **)
       
let rec perm_string pi =
  match pi with 
  | [] -> ""
  | (a,b) :: pi0 -> "(" ^ a ^ "\\," ^ b ^ ")" ^ perm_string pi0

                                                            
let rec term_string t =
  match t with
  | Ut -> "\\langle\\rangle"
  | At a -> "\\overline{" ^ a ^ "}"          
  | Ab (a, s) -> "[" ^ a ^ "]" ^ term_string s
  | Pr (u, v) -> "\\langle " ^ term_string u ^ ", " ^ term_string v ^ " \\rangle"
  | Fc (e, n, s) -> "f^{" ^ e ^ "}_{" ^ n ^ "} " ^ term_string s
  | Su ([], x) -> x                                                          
  | Su (pi, x) -> perm_string pi ^ "." ^ x 

                                           
let rec fresh_ctx_string ctx =
  match ctx with
  | [(a,x)] -> a ^ "\\#" ^ x         
  | (a,x) :: ctx0 -> a ^ "\\#" ^ x ^ ", \\;" ^ fresh_ctx_string ctx0                                   
  | [] -> ""                                         

            
let rec subst_string sub =
  match sub with
  | [(x,t)] -> x ^ "/" ^ term_string t
  | (x,t) :: sub0 -> "\\{" ^ x ^ "/" ^ term_string t ^ ", \\;" ^ subst_string sub0 ^ "\\}"
  | [] -> "id"                                         
                 
            
let rec constr_string ctr =
  match ctr with
  | Fresh (a, t) -> a ^ "\\#_?" ^ term_string t
  | Equ (s, t) -> term_string s ^ "\\approx_?" ^ term_string t

                                                             
let rec probl_string (pbr : constr list) =
  match pbr with
  | [ctr] -> constr_string ctr      
  | ctr :: pbr0 -> constr_string ctr ^ ",\\; " ^ probl_string pbr0                                     
  | [] -> ""


let rec varSet_string list =
  match list with
  | [] -> ""
  | [x] -> x          
  | x :: list0 -> x ^ ", " ^ varSet_string list0
            
                                                                                          
let unif_triple_string qr =
  match qr with 
    (c, varSet, s, prb) -> "\\langle\\{" ^ fresh_ctx_string c ^ "\\}, \\;" ^
                              "\\{" ^ varSet_string varSet ^ "\\}, \\;" ^
                              subst_string s ^ ", \\;\\{" ^ probl_string prb ^ "\\} \\rangle"

                                                                        
let rec list_string f_string list =
  match list with
  | [] -> ""
  | a :: list0 -> f_string a ^ " " ^ list_string f_string list0         

                                                 
let rec tree_string (f_string : 'a -> string) tree =
  match tree with
  | Leaf (lab, obj) -> "[.{$" ^ (f_string obj) ^ "$} [.{\\tiny ${\\tt " ^ lab ^ "}$} ]]"
  | Node (lab, obj, list) -> "[.{$" ^ (f_string obj) ^ "$}\n\t" ^
                                     "\\edge node[auto=right] {\\tiny ${\\tt " ^ lab ^ "}$};\n" ^
                                       list_string (tree_string f_string) list ^ " ]\n"


(*** File outputing ***)                                                                            
                                                                                   
let file = "out.tex"

let message f_string alg obj =
"\\documentclass[11pt]{article}
\\usepackage[a4paper]{geometry}

\\usepackage{tikz-qtree}
\\usepackage{fullpage}
\\usepackage{pdflscape}

\\begin{document}

\\pagestyle{empty}

\\begin{landscape}
{\\footnotesize
\\begin{tikzpicture}[
  level distance=1.5cm,sibling distance=0.5cm,
  edge from parent path={(\\tikzparentnode) -- (\\tikzchildnode)}]
\\tikzstyle{level 1}=[level distance=1.5cm] 
\\Tree" ^ tree_string f_string (alg obj) ^
"\\end{tikzpicture}
}
\\end{landscape}

\\end{document}"


(** create_file generate the latex file with the tree **)
                            
let create_file f_string alg obj =
  (* Write message to file *)
  let oc = open_out file in    (* create or truncate file, return channel *)
  fprintf oc "%s\n" (message f_string alg obj);   (* write something *)   
  close_out oc;                (* flush and close the channel *)   
