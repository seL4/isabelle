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

sledgehammer_params [prover = spass, blocking, fact_filter = mepo, timeout = 30,
                     preplay_timeout = 0, dont_minimize]

text {* Setup for testing Metis exhaustively *}

lemma fork: "P \<Longrightarrow> P \<Longrightarrow> P" by assumption

ML {*
val type_encs =
  ["erased",
   "poly_guards",
   "poly_guards?",
   "poly_guards??",
   "poly_guards@",
   "poly_tags",
   "poly_tags?",
   "poly_tags??",
   "poly_tags@",
   "poly_args",
   "poly_args?",
   "raw_mono_guards",
   "raw_mono_guards?",
   "raw_mono_guards??",
   "raw_mono_guards@",
   "raw_mono_tags",
   "raw_mono_tags?",
   "raw_mono_tags??",
   "raw_mono_tags@",
   "raw_mono_args",
   "raw_mono_args?",
   "mono_guards",
   "mono_guards?",
   "mono_guards??",
   "mono_tags",
   "mono_tags?",
   "mono_tags??",
   "mono_args"]

fun metis_exhaust_tac ctxt ths =
  let
    fun tac [] st = all_tac st
      | tac (type_enc :: type_encs) st =
        st (* |> tap (fn _ => tracing (PolyML.makestring type_enc)) *)
           |> ((if null type_encs then all_tac else rtac @{thm fork} 1)
               THEN Metis_Tactic.metis_tac [type_enc]
                    ATP_Problem_Generate.combsN ctxt ths 1
               THEN COND (has_fewer_prems 2) all_tac no_tac
               THEN tac type_encs)
  in tac type_encs end
*}

method_setup metis_exhaust = {*
  Attrib.thms >>
    (fn ths => fn ctxt => SIMPLE_METHOD (metis_exhaust_tac ctxt ths))
*} "exhaustively run Metis with all type encodings"

text {* Miscellaneous tests *}

lemma "x = y \<Longrightarrow> y = x"
by metis_exhaust

lemma "[a] = [Suc 0] \<Longrightarrow> a = 1"
by (metis_exhaust last.simps One_nat_def)

lemma "map Suc [0] = [Suc 0]"
by (metis_exhaust map.simps)

lemma "map Suc [1 + 1] = [Suc 2]"
by (metis_exhaust map.simps nat_1_add_1)

lemma "map Suc [2] = [Suc (1 + 1)]"
by (metis_exhaust map.simps nat_1_add_1)

definition "null xs = (xs = [])"

lemma "P (null xs) \<Longrightarrow> null xs \<Longrightarrow> xs = []"
by (metis_exhaust null_def)

lemma "(0\<Colon>nat) + 0 = 0"
by (metis_exhaust add_0_left)

end
