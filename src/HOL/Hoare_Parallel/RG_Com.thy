chapter \<open>The Rely-Guarantee Method\<close>

section \<open>Abstract Syntax\<close>

theory RG_Com imports Main begin

text \<open>Semantics of assertions and boolean expressions (bexp) as sets
of states.  Syntax of commands @{text com} and parallel commands
@{text par_com}.\<close>

type_synonym 'a bexp = "'a set"

datatype 'a com =
    Basic "'a \<Rightarrow>'a"
  | Seq "'a com" "'a com"
  | Cond "'a bexp" "'a com" "'a com"
  | While "'a bexp" "'a com"
  | Await "'a bexp" "'a com"

type_synonym 'a par_com = "'a com option list"

end