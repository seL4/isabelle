(*  Title:      HOL/Library/LaTeXsugar.thy
    Author:     Gerwin Klein, Tobias Nipkow, Norbert Schirmer
    Copyright   2005 NICTA and TUM
*)

(*<*)
theory LaTeXsugar
imports Main
begin

(* LOGIC *)
notation (latex output)
  If  ("(\<^latex>\<open>\\textsf{\<close>if\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\textsf{\<close>then\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\textsf{\<close>else\<^latex>\<open>}\<close> (_))" 10)

syntax (latex output)

  "_Let"        :: "[letbinds, 'a] => 'a"
  ("(\<^latex>\<open>\\textsf{\<close>let\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\textsf{\<close>in\<^latex>\<open>}\<close> (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^latex>\<open>\\textsf{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\\textsf{\<close>of\<^latex>\<open>}\<close>/ _)" 10)


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

(* card *)
notation (latex output)
  card  ("|_|")

(* LISTS *)

(* Cons *)
notation (latex)
  Cons  ("_ \<cdot>/ _" [66,65] 65)

(* length *)
notation (latex output)
  length  ("|_|")

(* nth *)
notation (latex output)
  nth  ("_\<^latex>\<open>\\ensuremath{_{[\\mathit{\<close>_\<^latex>\<open>}]}}\<close>" [1000,0] 1000)

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
  Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>const_typ\<close>
    (Scan.lift Args.embedded_inner_syntax)
    (fn ctxt => fn c =>
      let val tc = Proof_Context.read_const {proper = false, strict = false} ctxt c in
        Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
          Pretty.brk 1, Syntax.pretty_typ ctxt (fastype_of tc)]
      end)
\<close>

setup\<open>
let
  fun dummy_pats (wrap $ (eq $ lhs $ rhs)) =
    let
      val rhs_vars = Term.add_vars rhs [];
      fun dummy (v as Var (ixn as (_, T))) =
            if member ((=) ) rhs_vars ixn then v else Const (\<^const_name>\<open>DUMMY\<close>, T)
        | dummy (t $ u) = dummy t $ dummy u
        | dummy (Abs (n, T, b)) = Abs (n, T, dummy b)
        | dummy t = t;
    in wrap $ (eq $ dummy lhs $ rhs) end
in
  Term_Style.setup \<^binding>\<open>dummy_pats\<close> (Scan.succeed (K dummy_pats))
end
\<close>

setup \<open>
let

fun eta_expand Ts t xs = case t of
    Abs(x,T,t) =>
      let val (t', xs') = eta_expand (T::Ts) t xs
      in (Abs (x, T, t'), xs') end
  | _ =>
      let
        val (a,ts) = strip_comb t (* assume a atomic *)
        val (ts',xs') = fold_map (eta_expand Ts) ts xs
        val t' = list_comb (a, ts');
        val Bs = binder_types (fastype_of1 (Ts,t));
        val n = Int.min (length Bs, length xs');
        val bs = map Bound ((n - 1) downto 0);
        val xBs = ListPair.zip (xs',Bs);
        val xs'' = drop n xs';
        val t'' = fold_rev Term.abs xBs (list_comb(t', bs))
      in (t'', xs'') end

val style_eta_expand =
  (Scan.repeat Args.name) >> (fn xs => fn ctxt => fn t => fst (eta_expand [] t xs))

in Term_Style.setup \<^binding>\<open>eta_expand\<close> style_eta_expand end
\<close>

end
(*>*)
