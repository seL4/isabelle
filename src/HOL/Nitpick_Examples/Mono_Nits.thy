(*  Title:      HOL/Nitpick_Examples/Mono_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Examples featuring Nitpick's monotonicity check.
*)

header {* Examples Featuring Nitpick's Monotonicity Check *}

theory Mono_Nits
imports Main
begin

ML {*
exception FAIL

val defs = Nitpick_HOL.all_axioms_of @{theory} |> #1
val def_table = Nitpick_HOL.const_def_table @{context} defs
val ext_ctxt : Nitpick_HOL.extended_context =
  {thy = @{theory}, ctxt = @{context}, max_bisim_depth = ~1, boxes = [],
   user_axioms = NONE, debug = false, wfs = [], destroy_constrs = false,
   specialize = false, skolemize = false, star_linear_preds = false,
   uncurry = false, fast_descrs = false, tac_timeout = NONE, evals = [],
   case_names = [], def_table = def_table, nondef_table = Symtab.empty,
   user_nondefs = [], simp_table = Unsynchronized.ref Symtab.empty,
   psimp_table = Symtab.empty, intro_table = Symtab.empty,
   ground_thm_table = Inttab.empty, ersatz_table = [],
   skolems = Unsynchronized.ref [], special_funs = Unsynchronized.ref [],
   unrolled_preds = Unsynchronized.ref [], wf_cache = Unsynchronized.ref [],
   constr_cache = Unsynchronized.ref []}
(* term -> bool *)
val is_mono = Nitpick_Mono.formulas_monotonic ext_ctxt @{typ 'a} [] []
fun is_const t =
  let val T = fastype_of t in
    is_mono (Logic.mk_implies (Logic.mk_equals (Free ("dummyP", T), t),
                               @{const False}))
  end
fun mono t = is_mono t orelse raise FAIL
fun nonmono t = not (is_mono t) orelse raise FAIL
fun const t = is_const t orelse raise FAIL
fun nonconst t = not (is_const t) orelse raise FAIL
*}

ML {* const @{term "A::('a\<Rightarrow>'b)"} *}
ML {* const @{term "(A::'a set) = A"} *}
ML {* const @{term "(A::'a set set) = A"} *}
ML {* const @{term "(\<lambda>x::'a set. x a)"} *}
ML {* const @{term "{{a}} = C"} *}
ML {* const @{term "{f::'a\<Rightarrow>nat} = {g::'a\<Rightarrow>nat}"} *}
ML {* const @{term "A \<union> B"} *}
ML {* const @{term "P (a::'a)"} *}
ML {* const @{term "\<lambda>a::'a. b (c (d::'a)) (e::'a) (f::'a)"} *}
ML {* const @{term "\<forall>A::'a set. A a"} *}
ML {* const @{term "\<forall>A::'a set. P A"} *}
ML {* const @{term "P \<or> Q"} *}
ML {* const @{term "A \<union> B = C"} *}
ML {* const @{term "(if P then (A::'a set) else B) = C"} *}
ML {* const @{term "let A = C in A \<union> B"} *}
ML {* const @{term "THE x::'b. P x"} *}
ML {* const @{term "{}::'a set"} *}
ML {* const @{term "(\<lambda>x::'a. True)"} *}
ML {* const @{term "Let a A"} *}
ML {* const @{term "A (a::'a)"} *}
ML {* const @{term "insert a A = B"} *}
ML {* const @{term "- (A::'a set)"} *}
ML {* const @{term "finite A"} *}
ML {* const @{term "\<not> finite A"} *}
ML {* const @{term "finite (A::'a set set)"} *}
ML {* const @{term "\<lambda>a::'a. A a \<and> \<not> B a"} *}
ML {* const @{term "A < (B::'a set)"} *}
ML {* const @{term "A \<le> (B::'a set)"} *}
ML {* const @{term "[a::'a]"} *}
ML {* const @{term "[a::'a set]"} *}
ML {* const @{term "[A \<union> (B::'a set)]"} *}
ML {* const @{term "[A \<union> (B::'a set)] = [C]"} *}
ML {* const @{term "\<forall>P. P a"} *}

ML {* nonconst @{term "{%x. True}"} *}
ML {* nonconst @{term "{(%x. x = a)} = C"} *}
ML {* nonconst @{term "\<forall>P (a::'a). P a"} *}
ML {* nonconst @{term "\<forall>a::'a. P a"} *}
ML {* nonconst @{term "(\<lambda>a::'a. \<not> A a) = B"} *}
ML {* nonconst @{term "THE x. P x"} *}
ML {* nonconst @{term "SOME x. P x"} *}

ML {* mono @{prop "Q (\<forall>x::'a set. P x)"} *}
ML {* mono @{prop "P (a::'a)"} *}
ML {* mono @{prop "{a} = {b}"} *}
ML {* mono @{prop "P (a::'a) \<and> P \<union> P = P"} *}
ML {* mono @{prop "\<forall>F::'a set set. P"} *}
ML {* mono @{prop "\<not> (\<forall>F f g (h::'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h)"} *}
ML {* mono @{prop "\<not> Q (\<forall>x::'a set. P x)"} *}
ML {* mono @{prop "\<not> (\<forall>x. P x)"} *}

ML {* nonmono @{prop "\<forall>x. P x"} *}
ML {* nonmono @{prop "\<forall>F f g (h::'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h"} *}
ML {* nonmono @{prop "myall P = (P = (\<lambda>x. True))"} *}

end
