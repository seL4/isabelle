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
exception BUG

val subst = []
val defs = Nitpick_HOL.all_axioms_of @{context} subst |> #1
val def_table = Nitpick_HOL.const_def_table @{context} subst defs
val hol_ctxt : Nitpick_HOL.hol_context =
  {thy = @{theory}, ctxt = @{context}, max_bisim_depth = ~1, boxes = [],
   stds = [(NONE, true)], wfs = [], user_axioms = NONE, debug = false,
   whacks = [], binary_ints = SOME false, destroy_constrs = false,
   specialize = false, star_linear_preds = false, tac_timeout = NONE,
   evals = [], case_names = [], def_table = def_table,
   nondef_table = Symtab.empty, user_nondefs = [],
   simp_table = Unsynchronized.ref Symtab.empty, psimp_table = Symtab.empty,
   choice_spec_table = Symtab.empty, intro_table = Symtab.empty,
   ground_thm_table = Inttab.empty, ersatz_table = [],
   skolems = Unsynchronized.ref [], special_funs = Unsynchronized.ref [],
   unrolled_preds = Unsynchronized.ref [], wf_cache = Unsynchronized.ref [],
   constr_cache = Unsynchronized.ref []}
fun is_mono t =
  Nitpick_Mono.formulas_monotonic hol_ctxt false @{typ 'a} ([t], [])
fun is_const t =
  let val T = fastype_of t in
    is_mono (Logic.mk_implies (Logic.mk_equals (Free ("dummyP", T), t),
                               @{const False}))
  end
fun mono t = is_mono t orelse raise BUG
fun nonmono t = not (is_mono t) orelse raise BUG
fun const t = is_const t orelse raise BUG
fun nonconst t = not (is_const t) orelse raise BUG
*}

ML {* Nitpick_Mono.trace := false *}

ML {* const @{term "A\<Colon>('a\<Rightarrow>'b)"} *}
ML {* const @{term "(A\<Colon>'a set) = A"} *}
ML {* const @{term "(A\<Colon>'a set set) = A"} *}
ML {* const @{term "(\<lambda>x\<Colon>'a set. x a)"} *}
ML {* const @{term "{{a\<Colon>'a}} = C"} *}
ML {* const @{term "{f\<Colon>'a\<Rightarrow>nat} = {g\<Colon>'a\<Rightarrow>nat}"} *}
ML {* const @{term "A \<union> (B\<Colon>'a set)"} *}
ML {* const @{term "\<lambda>A B x\<Colon>'a. A x \<or> B x"} *}
ML {* const @{term "P (a\<Colon>'a)"} *}
ML {* const @{term "\<lambda>a\<Colon>'a. b (c (d\<Colon>'a)) (e\<Colon>'a) (f\<Colon>'a)"} *}
ML {* const @{term "\<forall>A\<Colon>'a set. A a"} *}
ML {* const @{term "\<forall>A\<Colon>'a set. P A"} *}
ML {* const @{term "P \<or> Q"} *}
ML {* const @{term "A \<union> B = (C\<Colon>'a set)"} *}
ML {* const @{term "(\<lambda>A B x\<Colon>'a. A x \<or> B x) A B = C"} *}
ML {* const @{term "(if P then (A\<Colon>'a set) else B) = C"} *}
ML {* const @{term "let A = (C\<Colon>'a set) in A \<union> B"} *}
ML {* const @{term "THE x\<Colon>'b. P x"} *}
ML {* const @{term "(\<lambda>x\<Colon>'a. False)"} *}
ML {* const @{term "(\<lambda>x\<Colon>'a. True)"} *}
ML {* const @{term "(\<lambda>x\<Colon>'a. False) = (\<lambda>x\<Colon>'a. False)"} *}
ML {* const @{term "(\<lambda>x\<Colon>'a. True) = (\<lambda>x\<Colon>'a. True)"} *}
ML {* const @{term "Let (a\<Colon>'a) A"} *}
ML {* const @{term "A (a\<Colon>'a)"} *}
ML {* const @{term "insert (a\<Colon>'a) A = B"} *}
ML {* const @{term "- (A\<Colon>'a set)"} *}
ML {* const @{term "finite (A\<Colon>'a set)"} *}
ML {* const @{term "\<not> finite (A\<Colon>'a set)"} *}
ML {* const @{term "finite (A\<Colon>'a set set)"} *}
ML {* const @{term "\<lambda>a\<Colon>'a. A a \<and> \<not> B a"} *}
ML {* const @{term "A < (B\<Colon>'a set)"} *}
ML {* const @{term "A \<le> (B\<Colon>'a set)"} *}
ML {* const @{term "[a\<Colon>'a]"} *}
ML {* const @{term "[a\<Colon>'a set]"} *}
ML {* const @{term "[A \<union> (B\<Colon>'a set)]"} *}
ML {* const @{term "[A \<union> (B\<Colon>'a set)] = [C]"} *}
ML {* const @{term "{(\<lambda>x\<Colon>'a. x = a)} = C"} *}
ML {* const @{term "(\<lambda>a\<Colon>'a. \<not> A a) = B"} *}
ML {* const @{prop "\<forall>F f g (h\<Colon>'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> \<not> f a"} *}
ML {* const @{term "\<lambda>A B x\<Colon>'a. A x \<and> B x \<and> A = B"} *}
ML {* const @{term "p = (\<lambda>(x\<Colon>'a) (y\<Colon>'a). P x \<or> \<not> Q y)"} *}
ML {* const @{term "p = (\<lambda>(x\<Colon>'a) (y\<Colon>'a). p x y \<Colon> bool)"} *}
ML {* const @{term "p = (\<lambda>A B x. A x \<and> \<not> B x) (\<lambda>x. True) (\<lambda>y. x \<noteq> y)"} *}
ML {* const @{term "p = (\<lambda>y. x \<noteq> y)"} *}
ML {* const @{term "(\<lambda>x. (p\<Colon>'a\<Rightarrow>bool\<Rightarrow>bool) x False)"} *}
ML {* const @{term "(\<lambda>x y. (p\<Colon>'a\<Rightarrow>'a\<Rightarrow>bool\<Rightarrow>bool) x y False)"} *}
ML {* const @{term "f = (\<lambda>x\<Colon>'a. P x \<longrightarrow> Q x)"} *}

ML {* nonconst @{term "\<forall>P (a\<Colon>'a). P a"} *}
ML {* nonconst @{term "\<forall>a\<Colon>'a. P a"} *}
ML {* nonconst @{term "THE x\<Colon>'a. P x"} *}
ML {* nonconst @{term "SOME x\<Colon>'a. P x"} *}
ML {* nonconst @{term "(\<lambda>A B x\<Colon>'a. A x \<or> B x) = myunion"} *}
ML {* nonconst @{term "(\<lambda>x\<Colon>'a. False) = (\<lambda>x\<Colon>'a. True)"} *}
ML {* nonconst @{prop "\<forall>F f g (h\<Colon>'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h"} *}

ML {* mono @{prop "Q (\<forall>x\<Colon>'a set. P x)"} *}
ML {* mono @{prop "P (a\<Colon>'a)"} *}
ML {* mono @{prop "{a} = {b\<Colon>'a}"} *}
ML {* mono @{prop "P (a\<Colon>'a) \<and> P \<union> P = P"} *}
ML {* mono @{prop "\<forall>F\<Colon>'a set set. P"} *}
ML {* mono @{prop "\<not> (\<forall>F f g (h\<Colon>'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h)"} *}
ML {* mono @{prop "\<not> Q (\<forall>x\<Colon>'a set. P x)"} *}
ML {* mono @{prop "\<not> (\<forall>x\<Colon>'a. P x)"} *}
ML {* mono @{prop "myall P = (P = (\<lambda>x\<Colon>'a. True))"} *}
ML {* mono @{prop "myall P = (P = (\<lambda>x\<Colon>'a. False))"} *}
ML {* mono @{prop "\<forall>x\<Colon>'a. P x"} *}
ML {* mono @{term "(\<lambda>A B x\<Colon>'a. A x \<or> B x) \<noteq> myunion"} *}

ML {* nonmono @{prop "A = (\<lambda>x::'a. True) \<and> A = (\<lambda>x. False)"} *}
ML {* nonmono @{prop "\<forall>F f g (h\<Colon>'a set). F f \<and> F g \<and> \<not> f a \<and> g a \<longrightarrow> F h"} *}

end
