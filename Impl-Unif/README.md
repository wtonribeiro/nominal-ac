**Implementation (in OCaml) of the nominal C-unification algorithm**

**Compiled with OCaml Version 4.02.3:**

**File** | Short description
------------ | -------------
**Basic.ml**  | Basic data and function definitions (terms, action of permutations, action of substitutions etc) 
**Unif.ml**   | Specification of the nominal C-unification algorithm 
**Output.ml** | Functions to output the derivation trees in the latex format
**Tests.ml**  | Some pre-setted execution tests 
**build.sh**  | Script used to compile Basic.ml, Unif.ml and Output.ml
**ex0.tex to ex5.tex and ex0.pdf to ex5.pdf** | Examples of execution 


**Instructions for compiling and execution:**

1) Install OCaml version >= 4.0 (https://ocaml.org/docs/install.html)

2) Being inside folder Unif_Impl/ , give permition of execution of build.sh:

   $ sudo chmod +x build.sh

3) Execute 
   
   $ ./build.sh

4) Install Utop (https://ocaml.org/docs/install.html)
  
5) At the Utop prompt, execute:

   #load "Basic.cmo";;

   #load "Unif.cmo";;

   #load "Output.cmo";;      

   #use "Tests.ml";;


6) At the Utop prompt, and to run an especific test for tr1 to tr8, execute for example:

    c_unif_tree qr20;;

   It will generates the latex file out.tex inside forder Unif_Impl/.  
   This file can be compiled with pdflatex to  generate a out.pdf file. 
