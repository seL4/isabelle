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
  "{x} \<union> A" <= "CONST insert x A"
  "{x,y}" <= "{x} \<union> {y}"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"
  "{x}" <= "{x} \<union> \<emptyset>"

(* set comprehension *)
syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ | _})")
  "_CollectIn" :: "pttrn => 'a set => bool => 'a set"   ("(1{_ \<in> _ | _})")
translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"
  "_CollectIn p A P"  <= "{p : A. P}"

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

setup{*
  let
    fun pretty ctxt c =
      let val tc = Proof_Context.read_const_proper ctxt false c
      in Pretty.block [Thy_Output.pretty_term ctxt tc, Pretty.str " ::",
            Pretty.brk 1, Syntax.pretty_typ ctxt (fastype_of tc)]
      end
  in
    Thy_Output.antiquotation @{binding "const_typ"}
     (Scan.lift Args.name_source)
       (fn {source = src, context = ctxt, ...} => fn arg =>
          Thy_Output.output ctxt
            (Thy_Output.maybe_pretty_source pretty ctxt src [arg]))
  end;
*}

end
(*>*)