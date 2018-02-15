**A Formalisation (in Coq) of Nominal C-Unification and Nominal A, C and AC-Equivalence**

**Compiled with the Coq Proof Assistant Version 8.6:**

**File** | Short description
------------ | -------------
**[Impl_Equiv/](https://github.com/wtonribeiro/nominal-ac/tree/master/Impl-Equiv)** | Folder with the implementation (in OCaml) of the naive nominal A, C and AC-checking algorithm
**[Impl_Unif/](https://github.com/wtonribeiro/nominal-ac/tree/master/Impl-Unif)** | Folder with the implementation (in OCaml) of the nominal C-unification algorithm
**Completeness.v**  | Formalisation of the completeness of  $\Rightarrow_{\#}$ and $\Rightarrow_{\approx}$
**Soundness.v**     | Formalisation of the soundness of $\Rightarrow_{\#}$ and $\Rightarrow_{\approx}$ and successful leaves characterisation of the derivation tree
**Termination.v**   | Formalisation of the termination of  $\Rightarrow_{\#}$ and $\Rightarrow_{\approx}$
**C_Unif.v**        | Definition of the rule transformation systems $\Rightarrow_{\#}$ and $\Rightarrow_{\approx}$
**Substs.v**        | Definition of substitutions and some lemmas about
**Problems.v**      | Definition of nominal C-unification problems and some lemmas about
**C_Equiv.v**       | Specific Lemmas about nominal C-equivalence
**AACC_Equiv.v**    | Definitions of the nominal A+AC+C, A, AC and C-equivalences and the formalisation of their soundness
**Equiv_Tuples.v**  | Interactions between the extentions of nominal alpha_equivalence and tuples
**Equiv.v**         | Extentions of nominal alpha_equivalence in a parametrised way
**Alpha_Equiv.v**   | Definition of the nominal alpha_equivalence and the formalisation of its soundness
**w_Equiv.v**       | *Weak* equivalence definition and the formalisation of its soundness, equivariance and freshness preservation
**Fresh.v**         | Deftinition of the freshness relation and some related basic properties
**Tuples.v**        | Definitions of TPlength, TPith and TPithdel and many formalised properties about
**Disgr.v**         | Disagreement set definition and its properties
**Perm.v**          | Permutation action definition and its properties
**Terms.v**         | Syntax definition of nominal terms and some properties about
**LibTactics.v**    | Library of tactics given by http://www.chargueraud.org/softs/tlc/
**Makefile**        | Organisation of the code compilation with the "make" tool


















