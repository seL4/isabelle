(*  Title:      HOL/Tools/SMT/z3_replay_rules.ML
    Author:     Sascha Boehme, TU Muenchen

Custom rules for Z3 proof replay.
*)

signature Z3_REPLAY_RULES =
sig
  val apply: Simplifier.proc
end;

structure Z3_Replay_Rules: Z3_REPLAY_RULES =
struct

structure Data = Generic_Data
(
  type T = thm Net.net
  val empty = Net.empty
  val merge = Net.merge Thm.eq_thm
)

fun maybe_instantiate ct thm =
  try Thm.first_order_match (Thm.cprop_of thm, ct)
  |> Option.map (fn inst => Thm.instantiate inst thm)

fun apply ctxt ct =
  let
    val net = Data.get (Context.Proof ctxt)
    val xthms = map (Thm.transfer' ctxt) (Net.match_term net (Thm.term_of ct))

    fun select ct = map_filter (maybe_instantiate ct) xthms
    fun select' ct =
      let val thm = Thm.trivial ct
      in map_filter (try (fn rule => rule COMP thm)) xthms end

  in try hd (case select ct of [] => select' ct | xthms' => xthms') end

val prep = `Thm.prop_of

fun ins thm net = Net.insert_term Thm.eq_thm (prep thm) net handle Net.INSERT => net
fun del thm net = Net.delete_term Thm.eq_thm (prep thm) net handle Net.DELETE => net

val add = Thm.declaration_attribute (Data.map o ins o Thm.trim_context)
val del = Thm.declaration_attribute (Data.map o del)

val _ = Theory.setup
 (Attrib.setup \<^binding>\<open>z3_rule\<close> (Attrib.add_del add del) "declaration of Z3 proof rules" #>
  Global_Theory.add_thms_dynamic (\<^binding>\<open>z3_rule\<close>,
    fn context => map (Thm.transfer'' context) (Net.content (Data.get context))))

end;
