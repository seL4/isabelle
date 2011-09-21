(*  Title:      HOL/Nitpick_Examples/Mono_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick's monotonicity check.
*)

header {* Examples Featuring Nitpick's Monotonicity Check *}

theory Mono_Nits
imports Main (* "~/afp/thys/AVL-Trees/AVL2" "~/afp/thys/Huffman/Huffman" *)
begin

ML {*
open Nitpick_Util
open Nitpick_HOL
open Nitpick_Preproc

exception BUG

val thy = @{theory}
val ctxt = @{context}
val stds = [(NONE, true)]
val subst = []
val case_names = case_const_names ctxt stds
val defs = all_defs_of thy subst
val nondefs = all_nondefs_of ctxt subst
val def_tables = const_def_tables ctxt subst defs
val nondef_table = const_nondef_table nondefs
val simp_table = Unsynchronized.ref (const_simp_table ctxt subst)
val psimp_table = const_psimp_table ctxt subst
val choice_spec_table = const_choice_spec_table ctxt subst
val intro_table = inductive_intro_table ctxt subst def_tables
val ground_thm_table = ground_theorem_table thy
val ersatz_table = ersatz_table ctxt
val hol_ctxt as {thy, ...} : hol_context =
  {thy = thy, ctxt = ctxt, max_bisim_depth = ~1, boxes = [],
   stds = stds, wfs = [], user_axioms = NONE, debug = false,
   whacks = [], binary_ints = SOME false, destroy_constrs = true,
   specialize = false, star_linear_preds = false, total_consts = NONE,
   needs = NONE, tac_timeout = NONE, evals = [], case_names = case_names,
   def_tables = def_tables, nondef_table = nondef_table, nondefs = nondefs,
   simp_table = simp_table, psimp_table = psimp_table,
   choice_spec_table = choice_spec_table, intro_table = intro_table,
   ground_thm_table = ground_thm_table, ersatz_table = ersatz_table,
   skolems = Unsynchronized.ref [], special_funs = Unsynchronized.ref [],
   unrolled_preds = Unsynchronized.ref [], wf_cache = Unsynchronized.ref [],
   constr_cache = Unsynchronized.ref []}
val binarize = false

fun is_mono t =
  Nitpick_Mono.formulas_monotonic hol_ctxt binarize @{typ 'a} ([t], [])

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
ML {* const @{term "\<forall>a\<Colon>'a. P a"} *}

ML {* nonconst @{term "\<forall>P (a\<Colon>'a). P a"} *}
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

ML {*
val preproc_timeout = SOME (seconds 5.0)
val mono_timeout = SOME (seconds 1.0)

fun all_unconcealed_theorems_of thy =
  let val facts = Global_Theory.facts_of thy in
    Facts.fold_static
        (fn (name, ths) =>
            if Facts.is_concealed facts name then I
            else append (map (`(Thm.get_name_hint)) ths))
        facts []
  end

fun is_forbidden_theorem name =
  length (space_explode "." name) <> 2 orelse
  String.isPrefix "type_definition" (List.last (space_explode "." name)) orelse
  String.isSuffix "_def" name orelse
  String.isSuffix "_raw" name

fun theorems_of thy =
  filter (fn (name, th) =>
             not (is_forbidden_theorem name) andalso
             (theory_of_thm th, thy) |> pairself Context.theory_name |> op =)
         (all_unconcealed_theorems_of thy)

fun check_formulas tsp =
  let
    fun is_type_actually_monotonic T =
      Nitpick_Mono.formulas_monotonic hol_ctxt binarize T tsp
    val free_Ts = fold Term.add_tfrees (op @ tsp) [] |> map TFree
    val (mono_free_Ts, nonmono_free_Ts) =
      time_limit mono_timeout (List.partition is_type_actually_monotonic)
                 free_Ts
  in
    if not (null mono_free_Ts) then "MONO"
    else if not (null nonmono_free_Ts) then "NONMONO"
    else "NIX"
  end
  handle TimeLimit.TimeOut => "TIMEOUT"
       | NOT_SUPPORTED _ => "UNSUP"
       | exn => if Exn.is_interrupt exn then reraise exn else "UNKNOWN"

fun check_theory thy =
  let
    val path = File.tmp_path (Context.theory_name thy ^ ".out" |> Path.explode)
    val _ = File.write path ""
    fun check_theorem (name, th) =
      let
        val t = th |> prop_of |> Type.legacy_freeze |> close_form
        val neg_t = Logic.mk_implies (t, @{prop False})
        val (nondef_ts, def_ts, _, _, _, _) =
          time_limit preproc_timeout (preprocess_formulas hol_ctxt []) neg_t
        val res = name ^ ": " ^ check_formulas (nondef_ts, def_ts)
      in File.append path (res ^ "\n"); writeln res end
      handle TimeLimit.TimeOut => ()
  in thy |> theorems_of |> List.app check_theorem end
*}

(*
ML {* check_theory @{theory AVL2} *}
ML {* check_theory @{theory Fun} *}
ML {* check_theory @{theory Huffman} *}
ML {* check_theory @{theory List} *}
ML {* check_theory @{theory Map} *}
ML {* check_theory @{theory Relation} *}
*)

ML {* getenv "ISABELLE_TMP" *}

end
