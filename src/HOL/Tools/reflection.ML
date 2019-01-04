(*  Title:      HOL/Tools/reflection.ML
    Author:     Amine Chaieb, TU Muenchen

A trial for automatical reflection with user-space declarations.
*)

signature REFLECTION =
sig
  val reflect: Proof.context -> thm list -> thm list -> conv
  val reflection_tac: Proof.context -> thm list -> thm list -> term option -> int -> tactic
  val reflect_with_eval: Proof.context -> thm list -> thm list -> conv -> conv
  val reflection_with_eval_tac: Proof.context -> thm list -> thm list -> conv -> term option -> int -> tactic
  val get_default: Proof.context -> { reification_eqs: thm list, correctness_thms: thm list }
  val add_reification_eq: attribute
  val del_reification_eq: attribute
  val add_correctness_thm: attribute
  val del_correctness_thm: attribute
  val default_reify_tac: Proof.context -> thm list -> term option -> int -> tactic
  val default_reflection_tac: Proof.context -> thm list -> thm list -> term option -> int -> tactic
end;

structure Reflection : REFLECTION =
struct

fun subst_correctness corr_thms ct =
  Conv.rewrs_conv (map (Thm.symmetric o mk_eq) corr_thms) ct
    handle CTERM _ => error "No suitable correctness theorem found";

fun reflect ctxt corr_thms eqs =
  (Reification.conv ctxt eqs) then_conv (subst_correctness corr_thms)

fun reflection_tac ctxt corr_thms eqs =
  Reification.lift_conv ctxt (reflect ctxt corr_thms eqs);

fun first_arg_conv conv =
  let
    fun conv' ct =
      if can Thm.dest_comb (fst (Thm.dest_comb ct))
      then Conv.combination_conv conv' Conv.all_conv ct
      else Conv.combination_conv Conv.all_conv conv ct;
  in conv' end;

fun reflect_with_eval ctxt corr_thms eqs conv =
  (reflect ctxt corr_thms eqs) then_conv (first_arg_conv conv) then_conv (Reification.dereify ctxt eqs);

fun reflection_with_eval_tac ctxt corr_thms eqs conv =
  Reification.lift_conv ctxt (reflect_with_eval ctxt corr_thms eqs conv);

structure Data = Generic_Data
(
  type T = thm list * thm list;
  val empty = ([], []);
  val extend = I;
  fun merge ((ths1, rths1), (ths2, rths2)) =
    (Thm.merge_thms (ths1, ths2), Thm.merge_thms (rths1, rths2));
);

fun get_default ctxt =
  let
    val (reification_eqs, correctness_thms) = Data.get (Context.Proof ctxt);
  in { reification_eqs = reification_eqs, correctness_thms = correctness_thms } end;

val add_reification_eq = Thm.declaration_attribute (Data.map o apfst o Thm.add_thm);
val del_reification_eq = Thm.declaration_attribute (Data.map o apfst o Thm.del_thm);
val add_correctness_thm = Thm.declaration_attribute (Data.map o apsnd o Thm.add_thm);
val del_correctness_thm = Thm.declaration_attribute (Data.map o apsnd o Thm.del_thm);

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>reify\<close>
    (Attrib.add_del add_reification_eq del_reification_eq)
    "declare reification equations" #>
   Attrib.setup \<^binding>\<open>reflection\<close>
    (Attrib.add_del add_correctness_thm del_correctness_thm)
    "declare reflection correctness theorems");

fun default_reify_tac ctxt user_eqs =
  let
    val { reification_eqs = default_eqs, correctness_thms = _ } =
      get_default ctxt;
    val eqs = fold Thm.add_thm user_eqs default_eqs;
  in Reification.tac ctxt eqs end;

fun default_reflection_tac ctxt user_thms user_eqs =
  let
    val { reification_eqs = default_eqs, correctness_thms = default_thms } =
      get_default ctxt;
    val corr_thms = fold Thm.add_thm user_thms default_thms;
    val eqs = fold Thm.add_thm user_eqs default_eqs; 
  in reflection_tac ctxt corr_thms eqs end;

end;
