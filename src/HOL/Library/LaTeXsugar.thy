(*  Title:      HOL/Library/LaTeXsugar.thy
    ID:         $Id$
    Author:     Gerwin Klain, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(*<*)
theory LaTeXsugar
imports Main
begin

(* LOGIC *)
const_syntax (latex output)
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
syntax (latex output)
  "_emptyset" :: "'a set"              ("\<emptyset>")
translations
  "_emptyset"      <= "{}"

(* insert *)
translations 
  "{x} \<union> A" <= "insert x A"
  "{x,y}" <= "{x} \<union> {y}"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"
  "{x}" <= "{x} \<union> _emptyset"

(* set comprehension *)
syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ | _})")
translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"

(* LISTS *)

(* Cons *)
const_syntax (latex)
  Cons  ("_\<cdot>/_" [66,65] 65)

(* length *)
const_syntax (latex output)
  length  ("|_|")

(* nth *)
const_syntax (latex output)
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