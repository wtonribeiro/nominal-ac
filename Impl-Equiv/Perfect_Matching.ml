(**
 ============================================================================
 Project     : Nominal A, AC and C Unification
 File        : Perfect_Matching.ml
 Authors     : Washington Lu\'is R. de Carvalho Segundo and
               Mauricio Ayala Rinc\'on 
               Universidade de Bras\'ilia (UnB) - Brazil
               Group of Theory of Computation
 
 Description : Implementation of the perfect_match function used 
               by Graph_Equiv.ml. This uses the ocamlgraph library.

 Last Modified On: Sep 18, 2018.
 ============================================================================
*)


(** The perfect_match function is based in the implementation 
    of the Ford-Fulkerson maximum flow algorithm available 
    in the library ocamlgraph. *)

open Graph
open Flow

(** Nodes are labelled with integers. *)       
             
module V = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

(** Edges are weighted with integers *)
             
module E = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = 0
end  

(** A directed graph is defined having as arguments the 
    defined nodes and edges *) 
             
module G = Imperative.Digraph.AbstractLabeled(V)(E)

(** The attribution of minimum (0) and maximum (1) capacities and
    the initial flow (0) of the edges is given as follows *)                                              
                                             
module W = struct
  type t = int
  type label = int
  let max_capacity x = 1
  let flow x = 0                       
  let add = (+)
  let sub = (-)            
  let zero = 0
  let compare = compare
  let min_capacity x = 0                
end

(** The definition of the application of the Ford-Fulkerson algorithm 
    using a graph G and a distribution of capacities and initial flow W *)  
             
module FF = Ford_Fulkerson(G)(W)

(** The imperative creation of a new empty graph g *)                          
                                             
let g = G.create ()

(** A function that recursively sums all all values in a list of integers *)
                 
let rec sum_list l =
  match l with
  | [] -> 0
  | i :: l0 -> i + sum_list l0                 
                 

(** Finally the perfect_match function is built having as arguments a list 
    of pairs of integers l and integer n. This function builds 
    the graph that will be given as input to the maximum flow algorithm and
    then verifies if the number of edges in maximum match is equal to n. *)
                            
let perfect_match l n =

  (** m is the number of nodes of the graph that is based  
      in n, which must be the number of nodes of the left-hand side 
      of the bipartite graph. *)

  let m = 2 * n + 2 in

  (** Since the bipartite graph represented by the list l has the same
      number of nodes in the right and the left-hand side, and this
      bipartite graph has nodes labelled form 1 to m, the source
      node is then labelled with 0 and the target node is labelled with (m+1) *)   

   let nodes =              
   let new_node i = let v = G.V.create i in G.add_vertex g v; v in
   Array.init (m + 1) (fun i -> new_node i) in
              
   let node i = nodes.(i) in

   (** Edges are added according list l. For instance, (1,5) is translated
       as an edge form node 1 to node 5 *)
                  
   let () =
   List.iter (fun p -> G.add_edge g (node (fst p)) (node (snd p))) l in

   (** Edges form the node 0 to the left-hand side nodes are created *)
   
   let () =
     List.iter (fun p -> G.add_edge g (node 0) (node (fst p))) l in

   (** Edges form the nodes of the right-hand side to node m are created *)

   let () =
     List.iter (fun p -> G.add_edge g (node (snd p)) (node m)) l in

   (** The algorithm of maximum flow between node 0 and node m in the graph g is executed *)

   let max_flow_result = FF.maxflow g (node 0) (node m) in

   (** The maximum flow for each edge is extracted to result_list *) 
   
   let result_list = 
    List.map (fst (max_flow_result))  
      (List.map (fun p -> (G.find_edge g (node (fst p)) (node (snd p)))) l)
   in

   (** The maximum match is reached by the set of edges that has maximum flow = 1. 
       One has a perfect matching if the number or edges that are in the maximum match  
       is equal to n. Remembering that n is the half of the number of elements of 
       the bipartite graph given as input. *) 

   if sum_list (result_list) = n then true else false
             

    
