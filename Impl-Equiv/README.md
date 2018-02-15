**Implementation (in OCaml) of the naive nominal A, C and AC-checking algoritm**

**Compiled with OCaml Version 4.02.3:**

**File** | Short description
------------ | -------------
**Basic.ml**  | Basic data and function definitions (terms, action of permutations, action of substitutions etc) 
**Equiv.ml**  | Specification of the naive nominal A, C and AC-checking algoritm 
**Tests.ml**  | Some pre-setted execution tests 
**build.sh**  | Script used to compile Basic.ml and Equiv.ml


**Instructions for compiling and execution:**

1) Install OCaml version >= 4.0 (https://ocaml.org/docs/install.html)

2) Being inside folder Impl/ , give permition of execution of build.sh:

   $ sudo chmod +x build.sh

3) Execute 
   
   $ ./build.sh

4) Install Utop (https://ocaml.org/docs/install.html)
  
5) At the Utop prompt, execute:

   #load "Basic.cmo";;

   #load "Equiv.cmo";;      

   #use "Tests.ml";;


6) At the Utop prompt, and to run an especific test for eq1 to eq18, execute for example:

    equiv eq5;;

   This case will return "true",
   because eq5 = ([], Ab ("a", At "a"), Ab ("b", At "b")).
