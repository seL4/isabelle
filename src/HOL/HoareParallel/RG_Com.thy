
header {* \chapter{The Rely-Guarantee Method} 

\section {Abstract Syntax}
*}

theory RG_Com = Main:

text {* Semantics of assertions and boolean expressions (bexp) as sets
of states.  Syntax of commands @{text com} and parallel commands
@{text par_com}. *}

types
  'a bexp = "'a set"

datatype 'a com = 
    Basic "'a \<Rightarrow>'a"
  | Seq "'a com" "'a com"
  | Cond "'a bexp" "'a com" "'a com"         
  | While "'a bexp" "'a com"       
  | Await "'a bexp" "'a com"                 

types 'a par_com = "(('a com) option) list"

end