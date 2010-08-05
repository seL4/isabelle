(*  Title:      HOL/Nitpick_Examples/Mono_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Examples featuring Nitpick's monotonicity check.
*)

header {* Examples Featuring Nitpick's Monotonicity Check *}

theory Mono_Nits
imports Main
begin

ML {*
exception FAIL

val subst = []
val defs = Nitpick_HOL.all_axioms_of @{context} subst |> #1
val def_table = Nitpick_HOL.const_def_table @{context} subst defs
val hol_ctxt : Nitpick_HOL.hol_context =
  {thy = @{theory}, ctxt = @{context}, max_bisim_depth = ~1, boxes = [],
   stds = [(NONE, true)], wfs = [], user_axioms = NONE, debug = false,
   whacks = [], binary_ints = SOME false, destroy_constrs = false,
   specialize = false, star_linear_preds = false, fast_descrs = false,
   tac_timeout = NONE, evals = [], case_names = [], def_table = def_table,
   nondef_table = Symtab.empty, user_nondefs = [],
   simp_table = Unsynchronized.ref Symtab.empty, psimp_table = Symtab.empty,
   choice_spec_table = Symtab.empty, intro_table = Symtab.empty,
   ground_thm_table = Inttab.empty, ersatz_table = [],
   skolems = Unsynchronized.ref [], special_funs = Unsynchronized.ref [],
   unrolled_preds = Unsynchronized.ref [], wf_cache = Unsynchronized.ref [],
   constr_cache = Unsynchronized.ref []}
(* term -> bool *)
fun is_mono t =
  Nitpick_Mono.formulas_monotonic hol_ctxt false @{typ 'a} ([t], [])
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
ML {* const @{term "{{a::'a}} = C"} *}
ML {* const @{term "{f::'a\<Rightarrow>nat} = {g::'a\<Rightarrow>nat}"} *}
ML {* const @{term "A \<union> (B::'a set)"} *}
ML {* const @{term "P (a::'a)"} *}
ML {* const @{term "\<lambda>a::'a. b (c (d::'a)) (e::'a) (f::'a)"} *}
ML {* const @{term "\<forall>A::'a set. A a"} *}
ML {* const @{term "\<forall>A::'a set. P A"} *}
ML {* const @{term "P \<or> Q"} *}
ML {* const @{term "A \<union> B = (C::'a set)"} *}
ML {* const @{term "(if P then (A::'a set) else B) = C"} *}
ML {* const @{term "let A = (C::'a set) in A \<union> B"} *}
ML {* const @{term "THE x::'b. P x"} *}
ML {* const @{term "(\<lambda>x::'a. False)"} *}
ML {* const @{term "(\<lambda>x::'a. True)"} *}
ML {* const @{term "Let (a::'a) A"} *}
ML {* const @{term "A (a::'a)"} *}
ML {* const @{term "insert (a::'a) A = B"} *}
ML {* const @{term "- (A::'a set)"} *}
ML {* const @{term "finite (A::'a set)"} *}
ML {* const @{term "\<not> finite (A::'a set)"} *}
ML {* const @{term "finite (A::'a set set)"} *}
ML {* const @{term "\<lambda>a::'a. A a \<and> \<not> B a"} *}
ML {* const @{term "A < (B::'a set)"} *}
ML {* const @{term "A \<le> (B::'a set)"} *}
ML {* const @{term "[a::'a]"} *}
ML {* const @{term "[a::'a set]"} *}
ML {* const @{term "[A \<union> (B::'a set)]"} *}
ML {* const @{term "[A \<union> (B::'a set)] = [C]"} *}
ML {* const @{term "{(\<lambda>x::'a. x = a)} = C"} *}

ML {* nonconst @{term "\<forall>P (a::'a). P a"} *}
ML {* nonconst @{term "\<forall>a::'a. P a"} *}
ML {* nonconst @{term "(\<lambda>a::'a. \<not> A a) = B"} *}
ML {* nonconst @{term "THE x::'a. P x"} *}
ML {* nonconst @{term "SOME x::'a. P x"} *}

ML {* mono @{prop "Q (\<forall>x::'a set. P x)"} *}
ML {* mono @{prop "P (a::'a)"} *}
ML {* mono @{prop "{a} = {b::'a}"} *}
ML {* mono @{prop "P (a::'a) \<and> P \<union> P = P"} *}
ML {* mono @{prop "\<forall>F::'a set set. P"} *}
ML {* mono @{prop "\<not> (\<forall>F f g (h::'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h)"} *}
ML {* mono @{prop "\<not> Q (\<forall>x::'a set. P x)"} *}
ML {* mono @{prop "\<not> (\<forall>x::'a. P x)"} *}

ML {* nonmono @{prop "\<forall>x::'a. P x"} *}
ML {* nonmono @{prop "myall P = (P = (\<lambda>x::'a. True))"} *}
ML {* nonmono @{prop "\<forall>F f g (h::'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h"} *}

end
