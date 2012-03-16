(*  Title:      ZF/Tools/typechk.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Automated type checking (cf. CTT).
*)

signature TYPE_CHECK =
sig
  val print_tcset: Proof.context -> unit
  val TC_add: attribute
  val TC_del: attribute
  val typecheck_tac: Proof.context -> tactic
  val type_solver_tac: Proof.context -> thm list -> int -> tactic
  val type_solver: solver
  val setup: theory -> theory
end;

structure TypeCheck: TYPE_CHECK =
struct

(* datatype tcset *)

datatype tcset = TC of
 {rules: thm list,     (*the type-checking rules*)
  net: thm Net.net};   (*discrimination net of the same rules*)

fun add_rule ctxt th (tcs as TC {rules, net}) =
  if member Thm.eq_thm_prop rules th then
    (warning ("Ignoring duplicate type-checking rule\n" ^ Display.string_of_thm ctxt th); tcs)
  else
    TC {rules = th :: rules, net = Net.insert_term (K false) (Thm.concl_of th, th) net};

fun del_rule ctxt th (tcs as TC {rules, net}) =
  if member Thm.eq_thm_prop rules th then
    TC {net = Net.delete_term Thm.eq_thm_prop (Thm.concl_of th, th) net,
      rules = remove Thm.eq_thm_prop th rules}
  else (warning ("No such type-checking rule\n" ^ Display.string_of_thm ctxt th); tcs);


(* generic data *)

structure Data = Generic_Data
(
  type T = tcset;
  val empty = TC {rules = [], net = Net.empty};
  val extend = I;
  fun merge (TC {rules, net}, TC {rules = rules', net = net'}) =
    TC {rules = Thm.merge_thms (rules, rules'), net = Net.merge Thm.eq_thm_prop (net, net')};
);

val TC_add =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (add_rule (Context.proof_of context) thm) context);

val TC_del =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (del_rule (Context.proof_of context) thm) context);

val tcset_of = Data.get o Context.Proof;

fun print_tcset ctxt =
  let val TC {rules, ...} = tcset_of ctxt in
    Pretty.writeln (Pretty.big_list "type-checking rules:"
      (map (Display.pretty_thm ctxt) rules))
  end;


(* tactics *)

(*resolution using a net rather than rules*)
fun net_res_tac maxr net =
  SUBGOAL
    (fn (prem,i) =>
      let val rls = Net.unify_term net (Logic.strip_assums_concl prem)
      in
         if length rls <= maxr then resolve_tac rls i else no_tac
      end);

fun is_rigid_elem (Const(@{const_name Trueprop},_) $ (Const(@{const_name mem},_) $ a $ _)) =
      not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*)
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  eq_assume_tac i);

(*Type checking solves a:?A (a rigid, ?A maybe flexible).
  match_tac is too strict; would refuse to instantiate ?A*)
fun typecheck_step_tac (TC{net,...}) =
    FIRSTGOAL (test_assume_tac ORELSE' net_res_tac 3 net);

fun typecheck_tac ctxt = REPEAT (typecheck_step_tac (tcset_of ctxt));

(*Compiles a term-net for speed*)
val basic_res_tac = net_resolve_tac [@{thm TrueI}, @{thm refl}, reflexive_thm, @{thm iff_refl},
                                     @{thm ballI}, @{thm allI}, @{thm conjI}, @{thm impI}];

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_solver_tac ctxt hyps = SELECT_GOAL
    (DEPTH_SOLVE (etac @{thm FalseE} 1
                  ORELSE basic_res_tac 1
                  ORELSE (ares_tac hyps 1
                          APPEND typecheck_step_tac (tcset_of ctxt))));

val type_solver =
  Simplifier.mk_solver "ZF typecheck" (fn ss =>
    type_solver_tac (Simplifier.the_context ss) (Simplifier.prems_of ss));


(* concrete syntax *)

val typecheck_setup =
  Method.setup @{binding typecheck}
    (Method.sections
      [Args.add -- Args.colon >> K (I, TC_add),
       Args.del -- Args.colon >> K (I, TC_del)]
      >> K (fn ctxt => SIMPLE_METHOD (CHANGED (typecheck_tac ctxt))))
    "ZF type-checking";

val _ =
  Outer_Syntax.improper_command @{command_spec "print_tcset"} "print context of ZF typecheck"
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_tcset o Toplevel.context_of)));


(* theory setup *)

val setup =
  Attrib.setup @{binding TC} (Attrib.add_del TC_add TC_del) "declaration of type-checking rule" #>
  typecheck_setup #>
  Simplifier.map_simpset_global (fn ss => ss setSolver type_solver);

end;
