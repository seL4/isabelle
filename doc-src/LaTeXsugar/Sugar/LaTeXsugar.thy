(*<*)
theory LaTeXsugar
imports Main
begin

(* LOGIC *)
syntax (latex output)
  If            :: "[bool, 'a, 'a] => 'a"
  ("(\<^raw:\textsf{>if\<^raw:}> (_)/ \<^raw:\textsf{>then\<^raw:}> (_)/ \<^raw:\textsf{>else\<^raw:}> (_))" 10)

  "_Let"        :: "[letbinds, 'a] => 'a"
  ("(\<^raw:\textsf{>let\<^raw:}> (_)/ \<^raw:\textsf{>in\<^raw:}> (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^raw:\textsf{>case\<^raw:}> _ \<^raw:\textsf{>of\<^raw:}>/ _)" 10)

(* SETS *)

(* empty set *)
syntax (latex output)
  "_emptyset" :: "'a set"              ("\<emptyset>")
translations
  "_emptyset"      <= "{}"

(* insert *)
translations 
  "{x} \<union> A" <= "insert x A"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"

(* set comprehension *)
syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ | _})")
translations
  "_Collect p P"      <= "{p. P}"

(* LISTS *)

(* Cons *)
syntax (latex)
  Cons :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" ("_\<cdot>/_" [66,65] 65)

(* length *)
syntax (latex output)
  length :: "'a list \<Rightarrow> nat" ("|_|")

(* nth *)
syntax (latex output)
  nth :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" ("_\<^raw:\ensuremath{_{[\mathit{>_\<^raw:}]}}>" [1000,0] 1000)

(* DUMMY *)
consts DUMMY :: 'a ("\<^raw:\_>")

(* THEOREMS *)
syntax (Rule output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{\mbox{>_\<^raw:}}>\<^raw:{\mbox{>_\<^raw:}}>")

  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{>_\<^raw:}>\<^raw:{\mbox{>_\<^raw:}}>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^raw:\mbox{>_\<^raw:}\\>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}>")

syntax (IfThen output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\rmfamily\upshape\normalsize{}>If\<^raw:\,}> _/ \<^raw:{\rmfamily\upshape\normalsize \,>then\<^raw:\,}>/ _.")
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\rmfamily\upshape\normalsize{}>If\<^raw:\,}> _ /\<^raw:{\rmfamily\upshape\normalsize \,>then\<^raw:\,}>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}> /\<^raw:{\rmfamily\upshape\normalsize \,>and\<^raw:\,}>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}>")

syntax (IfThenNoBox output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\rmfamily\upshape\normalsize{}>If\<^raw:\,}> _/ \<^raw:{\rmfamily\upshape\normalsize \,>then\<^raw:\,}>/ _.")
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\rmfamily\upshape\normalsize{}>If\<^raw:\,}> _ /\<^raw:{\rmfamily\upshape\normalsize \,>then\<^raw:\,}>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^raw:{\rmfamily\upshape\normalsize \,>and\<^raw:\,}>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")

end
(*>*)