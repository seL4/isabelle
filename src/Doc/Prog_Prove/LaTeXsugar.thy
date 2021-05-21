(*  Title:      HOL/Library/LaTeXsugar.thy
    Author:     Gerwin Klein, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(*<*)
theory LaTeXsugar
imports Main
begin

(* DUMMY *)
consts DUMMY :: 'a ("\<^latex>\<open>\\_\<close>")

(* THEOREMS *)
notation (Rule output)
  Pure.imp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>\\mbox{}\\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\\\\\<close>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

notation (Axiom output)
  "Trueprop"  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{}}{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

notation (IfThen output)
  Pure.imp  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
syntax (IfThen output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close> /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

notation (IfThenNoBox output)
  Pure.imp  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
syntax (IfThenNoBox output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")

setup \<open>
  Document_Output.antiquotation_pretty_source \<^binding>\<open>const_typ\<close>
    (Scan.lift Args.embedded_inner_syntax)
    (fn ctxt => fn c =>
      let val tc = Proof_Context.read_const {proper = false, strict = false} ctxt c in
        Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
          Pretty.brk 1, Syntax.pretty_typ ctxt (fastype_of tc)]
      end)
\<close>

end
(*>*)
