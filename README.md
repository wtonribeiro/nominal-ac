# Nominal-ac

# A Formalisation (in Coq) of Nominal Equivalence with Associative and Commutative Function Symbols

# Compiled with the Coq Proof Assistant Version 8.4:

Makefile        - The organizer of the code compilation with the "make" tool;

LibTactics.v    - A Library of tactics given by http://www.chargueraud.org/softs/tlc/ ;

Terms.v         - The syntax definition of nominal terms and some properties about;

Perm.v          - The Permutation action and its properties;

Disgr.v         - The difference, or disagreement set and its properties;

Tuples.v        - The three operators: TPlength, TPith and TPithdel and 
                  many formalised properties about these recursive functions;

Fresh.v         - The freshness relation and its basic properties;

w_Equiv.v       - The "weak" equivalence and the formalisation of its soundness 
                  as its equivariance and its freshness preservation;

Alpha_Equiv.v   - The nominal alpha_equivalence and its soundness;

Equiv.v         - The extentions of nominal alpha_equivalence in a modular way;

Equiv_Tuples.v  - The interaction between the extentions of nominal alpha_equivalence and tuples;

AAC_Equiv.v     - The A+AC, A and AC nominal soundness.
