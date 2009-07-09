(*  Title:      FOL/ex/Propositional_Cla.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* First-Order Logic: propositional examples (classical version) *}

theory Propositional_Cla
imports FOL
begin

text {* commutative laws of @{text "&"} and @{text "|"} *}

lemma "P & Q  -->  Q & P"
  by (tactic "IntPr.fast_tac 1")

lemma "P | Q  -->  Q | P"
  by fast


text {* associative laws of @{text "&"} and @{text "|"} *}
lemma "(P & Q) & R  -->  P & (Q & R)"
  by fast

lemma "(P | Q) | R  -->  P | (Q | R)"
  by fast


text {* distributive laws of @{text "&"} and @{text "|"} *}
lemma "(P & Q) | R  --> (P | R) & (Q | R)"
  by fast

lemma "(P | R) & (Q | R)  --> (P & Q) | R"
  by fast

lemma "(P | Q) & R  --> (P & R) | (Q & R)"
  by fast

lemma "(P & R) | (Q & R)  --> (P | Q) & R"
  by fast


text {* Laws involving implication *}

lemma "(P-->R) & (Q-->R) <-> (P|Q --> R)"
  by fast

lemma "(P & Q --> R) <-> (P--> (Q-->R))"
  by fast

lemma "((P-->R)-->R) --> ((Q-->R)-->R) --> (P&Q-->R) --> R"
  by fast

lemma "~(P-->R) --> ~(Q-->R) --> ~(P&Q-->R)"
  by fast

lemma "(P --> Q & R) <-> (P-->Q)  &  (P-->R)"
  by fast


text {* Propositions-as-types *}

-- {* The combinator K *}
lemma "P --> (Q --> P)"
  by fast

-- {* The combinator S *}
lemma "(P-->Q-->R)  --> (P-->Q) --> (P-->R)"
  by fast


-- {* Converse is classical *}
lemma "(P-->Q) | (P-->R)  -->  (P --> Q | R)"
  by fast

lemma "(P-->Q)  -->  (~Q --> ~P)"
  by fast


text {* Schwichtenberg's examples (via T. Nipkow) *}

lemma stab_imp: "(((Q-->R)-->R)-->Q) --> (((P-->Q)-->R)-->R)-->P-->Q"
  by fast

lemma stab_to_peirce:
  "(((P --> R) --> R) --> P) --> (((Q --> R) --> R) --> Q)  
                              --> ((P --> Q) --> P) --> P"
  by fast

lemma peirce_imp1: "(((Q --> R) --> Q) --> Q)  
                --> (((P --> Q) --> R) --> P --> Q) --> P --> Q"
  by fast
  
lemma peirce_imp2: "(((P --> R) --> P) --> P) --> ((P --> Q --> R) --> P) --> P"
  by fast

lemma mints: "((((P --> Q) --> P) --> P) --> Q) --> Q"
  by fast

lemma mints_solovev: "(P --> (Q --> R) --> Q) --> ((P --> Q) --> R) --> R"
  by fast

lemma tatsuta: "(((P7 --> P1) --> P10) --> P4 --> P5)  
  --> (((P8 --> P2) --> P9) --> P3 --> P10)  
  --> (P1 --> P8) --> P6 --> P7  
  --> (((P3 --> P2) --> P9) --> P4)  
  --> (P1 --> P3) --> (((P6 --> P1) --> P2) --> P9) --> P5"
  by fast

lemma tatsuta1: "(((P8 --> P2) --> P9) --> P3 --> P10)  
  --> (((P3 --> P2) --> P9) --> P4)  
  --> (((P6 --> P1) --> P2) --> P9)  
  --> (((P7 --> P1) --> P10) --> P4 --> P5)  
  --> (P1 --> P3) --> (P1 --> P8) --> P6 --> P7 --> P5"
  by fast

end
