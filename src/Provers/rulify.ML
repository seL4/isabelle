(*  Title:      Provers/rulify.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Conversion of object-level -->/ALL into meta-level ==>/!!.
*)

signature BASIC_RULIFY =
sig
  val rulify: thm -> thm
  val rulify_no_asm: thm -> thm
  val qed_spec_mp: string -> unit
  val qed_goal_spec_mp: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw_spec_mp: string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
end;

signature RULIFY =
sig
  include BASIC_RULIFY
  val rule_format: 'a attribute
  val rule_format_no_asm: 'a attribute
  val setup: (theory -> theory) list
end;

functor RulifyFun(val make_meta: thm -> thm val full_make_meta: thm -> thm): RULIFY =
struct


(* rulify *)

val tune = Drule.zero_var_indexes o Drule.strip_shyps_warning o Drule.forall_elim_vars_safe;

val rulify = tune o full_make_meta;
val rulify_no_asm = tune o make_meta;


(* attributes *)

fun rule_format x = Drule.rule_attribute (fn _ => rulify) x;
fun rule_format_no_asm x = Drule.rule_attribute (fn _ => rulify_no_asm) x;

fun rule_format_att x = Attrib.syntax
  (Scan.lift (Args.parens (Args.$$$ "no_asm") >> K rule_format_no_asm || Scan.succeed rule_format)) x;


(* qed commands *)

fun qed_spec_mp name = ThmDatabase.ml_store_thm (name, rulify_no_asm (Goals.result ()));

fun qed_goal_spec_mp name thy s p =
  ThmDatabase.bind_thm (name, rulify_no_asm (Goals.prove_goal thy s p));

fun qed_goalw_spec_mp name thy defs s p =
  ThmDatabase.bind_thm (name, rulify_no_asm (Goals.prove_goalw thy defs s p));


(* theory setup *)

val setup =
 [Attrib.add_attributes
  [("rule_format", (rule_format_att, rule_format_att), "result put into standard rule format")]];

end;
