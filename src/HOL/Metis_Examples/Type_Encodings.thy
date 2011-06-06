(*  Title:      HOL/Metis_Examples/Type_Encodings.thy
    Author:     Jasmin Blanchette, TU Muenchen

Example that exercises Metis's (and hence Sledgehammer's) type encodings.
*)

header {*
Example that Exercises Metis's (and Hence Sledgehammer's) Type Encodings
*}

theory Type_Encodings
imports Main
begin

declare [[metis_new_skolemizer]]

sledgehammer_params [prover = e, blocking, timeout = 10, preplay_timeout = 0]


text {* Setup for testing Metis exhaustively *}

lemma fork: "P \<Longrightarrow> P \<Longrightarrow> P" by assumption

ML {*
(* The commented-out type systems are too incomplete for our exhaustive
   tests. *)
val type_syss =
  ["erased",
   "poly_preds",
   "poly_preds_heavy",
   "poly_tags",
   "poly_tags_heavy",
   "poly_args",
   "mono_preds",
   "mono_preds_heavy",
   "mono_tags",
   "mono_tags_heavy",
   "mono_args",
   "mangled_preds",
   "mangled_preds_heavy",
   "mangled_tags",
   "mangled_tags_heavy",
   "mangled_args",
   "simple",
   "poly_preds?",
(* "poly_preds_heavy?", *)
(* "poly_tags?", *)
(* "poly_tags_heavy?", *)
   "mono_preds?",
   "mono_preds_heavy?",
   "mono_tags?",
   "mono_tags_heavy?",
   "mangled_preds?",
   "mangled_preds_heavy?",
   "mangled_tags?",
   "mangled_tags_heavy?",
   "simple?",
   "poly_preds!",
(* "poly_preds_heavy!", *)
(* "poly_tags!", *)
(* "poly_tags_heavy!", *)
   "mono_preds!",
   "mono_preds_heavy!",
   "mono_tags!",
   "mono_tags_heavy!",
   "mangled_preds!",
   "mangled_preds_heavy!",
   "mangled_tags!",
   "mangled_tags_heavy!",
   "simple!"]

fun metis_exhaust_tac ctxt ths =
  let
    fun tac [] st = all_tac st
      | tac (type_sys :: type_syss) st =
        st (* |> tap (fn _ => tracing (PolyML.makestring type_sys)) *)
           |> ((if null type_syss then all_tac else rtac @{thm fork} 1)
               THEN Metis_Tactics.metis_tac [type_sys] ctxt ths 1
               THEN COND (has_fewer_prems 2) all_tac no_tac
               THEN tac type_syss)
  in tac end
*}

method_setup metis_exhaust = {*
  Attrib.thms >>
    (fn ths => fn ctxt => SIMPLE_METHOD (metis_exhaust_tac ctxt ths type_syss))
*} "exhaustively run the new Metis with all type encodings"


text {* Miscellaneous tests *}

lemma "x = y \<Longrightarrow> y = x"
by metis_exhaust

lemma "[a] = [1 + 1] \<Longrightarrow> a = 1 + (1::int)"
by (metis_exhaust last.simps)

lemma "map Suc [0] = [Suc 0]"
by (metis_exhaust map.simps)

lemma "map Suc [1 + 1] = [Suc 2]"
by (metis_exhaust map.simps nat_1_add_1)

lemma "map Suc [2] = [Suc (1 + 1)]"
by (metis_exhaust map.simps nat_1_add_1)

definition "null xs = (xs = [])"

lemma "P (null xs) \<Longrightarrow> null xs \<Longrightarrow> xs = []"
by (metis_exhaust null_def)

lemma "(0::nat) + 0 = 0"
by (metis_exhaust arithmetic_simps(38))

end
