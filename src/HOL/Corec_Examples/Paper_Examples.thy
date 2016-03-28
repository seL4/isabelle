(*  Title:      HOL/Corec_Examples/Paper_Examples.thy
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2016

Small examples from the paper.
*)

section \<open>Small Examples from the Paper\<close>

theory Paper_Examples
imports "~~/src/HOL/Library/BNF_Corec"
begin

subsection \<open>Examples from the introduction\<close>

codatatype 'a stream = SCons (hd: 'a) (tl: "'a stream") (infixr "\<lhd>" 65)

corec "from" :: "nat \<Rightarrow> nat stream" where
  "from n = n \<lhd> from (n + 1)"

corec (friend) addOne :: "nat stream \<Rightarrow> nat stream" where
  "addOne n = (hd n + 1) \<lhd> addOne (tl n)"

corec from' :: "nat \<Rightarrow> nat stream" where
  "from' n = n \<lhd> addOne (from' n)"


subsection \<open>Examples from Section 5\<close>

text \<open>
We curry the example functions in this section because infix syntax works only for curried
functions.
\<close>

corec (friend) Plus :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix "\<oplus>" 67) where
  "x\<^sub>1 \<oplus> x\<^sub>2 = (hd x\<^sub>1 + hd x\<^sub>2) \<lhd> (tl x\<^sub>1 \<oplus> tl x\<^sub>2)"

corec zeros :: "nat stream" where "zeros = 0 \<lhd> zeros"

corec (friend) Plus' :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix "\<oplus>''" 67) where
  "x\<^sub>1 \<oplus>' x\<^sub>2 = hd x\<^sub>1 \<lhd> (tl (tl zeros) \<oplus>' x\<^sub>2)"

corec (friend) heart :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix "\<heartsuit>" 67) where
  "x\<^sub>1 \<heartsuit> x\<^sub>2 = (hd x\<^sub>1 * hd x\<^sub>2) \<lhd> (x\<^sub>2 \<heartsuit> ((x\<^sub>1 \<heartsuit> ((x\<^sub>1 \<heartsuit> tl x\<^sub>2) \<oplus> (tl x\<^sub>1 \<heartsuit> x\<^sub>2)))))"

corec spade :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix "\<spadesuit>" 67) where
  "x\<^sub>1 \<spadesuit> x\<^sub>2 = (hd x\<^sub>1 \<lhd> (x\<^sub>1 \<spadesuit> x\<^sub>2)) \<oplus> (hd x\<^sub>1 \<lhd> ((x\<^sub>1 \<spadesuit> tl x\<^sub>2) \<oplus> (tl x\<^sub>1 \<spadesuit> x\<^sub>2)))"

corec collatz :: "nat \<Rightarrow> nat stream" where
  "collatz n = (if even n \<and> n > 0 then collatz (n div 2) else n \<lhd> collatz (3 * n + 1))"

end
