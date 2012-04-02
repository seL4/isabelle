(*  Title:      HOL/Library/LaTeXsugar.thy
    Author:     Gerwin Klain, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(*<*)
theory LaTeXsugar
imports Main
begin

(* DUMMY *)
consts DUMMY :: 'a ("\<^raw:\_>")

(* THEOREMS *)
notation (Rule output)
  "==>"  ("\<^raw:\mbox{}\inferrule{\mbox{>_\<^raw:}}>\<^raw:{\mbox{>_\<^raw:}}>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{>_\<^raw:}>\<^raw:{\mbox{>_\<^raw:}}>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^raw:\mbox{>_\<^raw:}\\>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}>")

notation (Axiom output)
  "Trueprop"  ("\<^raw:\mbox{}\inferrule{\mbox{}}{\mbox{>_\<^raw:}}>")

notation (IfThen output)
  "==>"  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _/ \<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
syntax (IfThen output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _ /\<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}> /\<^raw:{\normalsize \,>and\<^raw:\,}>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}>")

notation (IfThenNoBox output)
  "==>"  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _/ \<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
syntax (IfThenNoBox output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:{\normalsize{}>If\<^raw:\,}> _ /\<^raw:{\normalsize \,>then\<^raw:\,}>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^raw:{\normalsize \,>and\<^raw:\,}>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")

end
(*>*)