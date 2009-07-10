(*  Title:      FOL/ex/Propositional_Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* First-Order Logic: propositional examples (intuitionistic version) *}

theory Propositional_Int
imports IFOL
begin

text {* commutative laws of @{text "&"} and @{text "|"} *}

lemma "P & Q  -->  Q & P"
  by (tactic "IntPr.fast_tac 1")

lemma "P | Q  -->  Q | P"
  by (tactic "IntPr.fast_tac 1")


text {* associative laws of @{text "&"} and @{text "|"} *}
lemma "(P & Q) & R  -->  P & (Q & R)"
  by (tactic "IntPr.fast_tac 1")

lemma "(P | Q) | R  -->  P | (Q | R)"
  by (tactic "IntPr.fast_tac 1")


text {* distributive laws of @{text "&"} and @{text "|"} *}
lemma "(P & Q) | R  --> (P | R) & (Q | R)"
  by (tactic "IntPr.fast_tac 1")

lemma "(P | R) & (Q | R)  --> (P & Q) | R"
  by (tactic "IntPr.fast_tac 1")

lemma "(P | Q) & R  --> (P & R) | (Q & R)"
  by (tactic "IntPr.fast_tac 1")

lemma "(P & R) | (Q & R)  --> (P | Q) & R"
  by (tactic "IntPr.fast_tac 1")


text {* Laws involving implication *}

lemma "(P-->R) & (Q-->R) <-> (P|Q --> R)"
  by (tactic "IntPr.fast_tac 1")

lemma "(P & Q --> R) <-> (P--> (Q-->R))"
  by (tactic "IntPr.fast_tac 1")

lemma "((P-->R)-->R) --> ((Q-->R)-->R) --> (P&Q-->R) --> R"
  by (tactic "IntPr.fast_tac 1")

lemma "~(P-->R) --> ~(Q-->R) --> ~(P&Q-->R)"
  by (tactic "IntPr.fast_tac 1")

lemma "(P --> Q & R) <-> (P-->Q)  &  (P-->R)"
  by (tactic "IntPr.fast_tac 1")


text {* Propositions-as-types *}

-- {* The combinator K *}
lemma "P --> (Q --> P)"
  by (tactic "IntPr.fast_tac 1")

-- {* The combinator S *}
lemma "(P-->Q-->R)  --> (P-->Q) --> (P-->R)"
  by (tactic "IntPr.fast_tac 1")


-- {* Converse is classical *}
lemma "(P-->Q) | (P-->R)  -->  (P --> Q | R)"
  by (tactic "IntPr.fast_tac 1")

lemma "(P-->Q)  -->  (~Q --> ~P)"
  by (tactic "IntPr.fast_tac 1")


text {* Schwichtenberg's examples (via T. Nipkow) *}

lemma stab_imp: "(((Q-->R)-->R)-->Q) --> (((P-->Q)-->R)-->R)-->P-->Q"
  by (tactic "IntPr.fast_tac 1")

lemma stab_to_peirce:
  "(((P --> R) --> R) --> P) --> (((Q --> R) --> R) --> Q)  
                              --> ((P --> Q) --> P) --> P"
  by (tactic "IntPr.fast_tac 1")

lemma peirce_imp1: "(((Q --> R) --> Q) --> Q)  
                --> (((P --> Q) --> R) --> P --> Q) --> P --> Q"
  by (tactic "IntPr.fast_tac 1")
  
lemma peirce_imp2: "(((P --> R) --> P) --> P) --> ((P --> Q --> R) --> P) --> P"
  by (tactic "IntPr.fast_tac 1")

lemma mints: "((((P --> Q) --> P) --> P) --> Q) --> Q"
  by (tactic "IntPr.fast_tac 1")

lemma mints_solovev: "(P --> (Q --> R) --> Q) --> ((P --> Q) --> R) --> R"
  by (tactic "IntPr.fast_tac 1")

lemma tatsuta: "(((P7 --> P1) --> P10) --> P4 --> P5)  
  --> (((P8 --> P2) --> P9) --> P3 --> P10)  
  --> (P1 --> P8) --> P6 --> P7  
  --> (((P3 --> P2) --> P9) --> P4)  
  --> (P1 --> P3) --> (((P6 --> P1) --> P2) --> P9) --> P5"
  by (tactic "IntPr.fast_tac 1")

lemma tatsuta1: "(((P8 --> P2) --> P9) --> P3 --> P10)  
  --> (((P3 --> P2) --> P9) --> P4)  
  --> (((P6 --> P1) --> P2) --> P9)  
  --> (((P7 --> P1) --> P10) --> P4 --> P5)  
  --> (P1 --> P3) --> (P1 --> P8) --> P6 --> P7 --> P5"
  by (tactic "IntPr.fast_tac 1")

end
