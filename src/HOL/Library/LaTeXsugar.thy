(*  Title:      HOL/Library/LaTeXsugar.thy
    Author:     Gerwin Klain, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(*<*)
theory LaTeXsugar
imports Main
begin

(* LOGIC *)
notation (latex output)
  If  ("(\<^raw:\textsf{>if\<^raw:}> (_)/ \<^raw:\textsf{>then\<^raw:}> (_)/ \<^raw:\textsf{>else\<^raw:}> (_))" 10)

syntax (latex output)

  "_Let"        :: "[letbinds, 'a] => 'a"
  ("(\<^raw:\textsf{>let\<^raw:}> (_)/ \<^raw:\textsf{>in\<^raw:}> (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^raw:\textsf{>case\<^raw:}> _ \<^raw:\textsf{>of\<^raw:}>/ _)" 10)

(* should become standard syntax once x-symbols supports it *)
syntax (latex)
  nexists :: "('a => bool) => bool"           (binder "\<nexists>" 10)
translations
  "\<nexists>x. P" <= "\<not>(\<exists>x. P)"

(* SETS *)

(* empty set *)
notation (latex)
  "Set.empty" ("\<emptyset>")

(* insert *)
translations 
  "{x} \<union> A" <= "insert x A"
  "{x,y}" <= "{x} \<union> {y}"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"
  "{x}" <= "{x} \<union> \<emptyset>"

(* set comprehension *)
syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ | _})")
translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"

(* LISTS *)

(* Cons *)
notation (latex)
  Cons  ("_\<cdot>/_" [66,65] 65)

(* length *)
notation (latex output)
  length  ("|_|")

(* nth *)
notation (latex output)
  nth  ("_\<^raw:\ensuremath{_{[\mathit{>_\<^raw:}]}}>" [1000,0] 1000)

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

syntax (Axiom output)
  "Trueprop" :: "bool \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{\mbox{}}{\mbox{>_\<^raw:}}>")

syntax (IfThen output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _/ \<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _ /\<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}> /\<^raw:{\normalsize \,>and\<^raw:\,}>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}>")

syntax (IfThenNoBox output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _/ \<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _ /\<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^raw:{\normalsize \,>and\<^raw:\,}>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")

end
(*>*)