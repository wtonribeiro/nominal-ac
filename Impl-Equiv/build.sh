ocamlc -c Original_Generated_Equiv.ml
ocamlopt -c Original_Generated_Equiv.ml
ocamlc -c Adjusted_Generated_Equiv.ml
ocamlopt -c Adjusted_Generated_Equiv.ml
ocamlc -c Basics.ml
ocamlopt -c Basics.ml
ocamlc -c Improved_Equiv.ml
ocamlopt -c Improved_Equiv.ml
ocamlfind ocamlc -linkpkg -thread -package ocamlgraph Perfect_Matching.ml
ocamlfind ocamlopt -linkpkg -thread -package ocamlgraph Perfect_Matching.ml
ocamlc -c Graph_Equiv.ml
ocamlopt -c Graph_Equiv.ml

