(*  Title:      ZF/Tools/typechk.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Automated type checking (cf. CTT).
*)

signature TYPE_CHECK =
sig
  val print_tcset: Context.generic -> unit
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

fun add_rule th (tcs as TC {rules, net}) =
  if member Drule.eq_thm_prop rules th then
    (warning ("Ignoring duplicate type-checking rule\n" ^ Display.string_of_thm th); tcs)
  else
    TC {rules = th :: rules,
        net = Net.insert_term (K false) (Thm.concl_of th, th) net};

fun del_rule th (tcs as TC {rules, net}) =
  if member Drule.eq_thm_prop rules th then
    TC {net = Net.delete_term Drule.eq_thm_prop (Thm.concl_of th, th) net,
        rules = remove Drule.eq_thm_prop th rules}
  else (warning ("No such type-checking rule\n" ^ Display.string_of_thm th); tcs);


(* generic data *)

structure Data = GenericDataFun
(
  val name = "ZF/type-checking";
  type T = tcset
  val empty = TC {rules = [], net = Net.empty};
  val extend = I;

  fun merge _ (TC {rules, net}, TC {rules = rules', net = net'}) =
    TC {rules = gen_union Drule.eq_thm_prop (rules, rules'),
        net = Net.merge Drule.eq_thm_prop (net, net')};

  fun print context (TC {rules, ...}) =
    Pretty.writeln (Pretty.big_list "type-checking rules:"
      (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
);

val print_tcset = Data.print;

val TC_add = Thm.declaration_attribute (Data.map o add_rule);
val TC_del = Thm.declaration_attribute (Data.map o del_rule);

val tcset_of = Data.get o Context.Proof;


(* tactics *)

(*resolution using a net rather than rules*)
fun net_res_tac maxr net =
  SUBGOAL
    (fn (prem,i) =>
      let val rls = Net.unify_term net (Logic.strip_assums_concl prem)
      in
         if length rls <= maxr then resolve_tac rls i else no_tac
      end);

fun is_rigid_elem (Const("Trueprop",_) $ (Const("op :",_) $ a $ _)) =
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
val basic_res_tac = net_resolve_tac [TrueI,refl,reflexive_thm,iff_refl,
                                     ballI,allI,conjI,impI];

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_solver_tac ctxt hyps = SELECT_GOAL
    (DEPTH_SOLVE (etac FalseE 1
                  ORELSE basic_res_tac 1
                  ORELSE (ares_tac hyps 1
                          APPEND typecheck_step_tac (tcset_of ctxt))));

val type_solver = Simplifier.mk_solver' "ZF typecheck" (fn ss =>
  type_solver_tac (Simplifier.the_context ss) (Simplifier.prems_of_ss ss));


(* concrete syntax *)

val TC_att = Attrib.add_del_args TC_add TC_del;

val typecheck_meth =
  Method.only_sectioned_args
    [Args.add -- Args.colon >> K (I, TC_add),
     Args.del -- Args.colon >> K (I, TC_del)]
  (fn ctxt => Method.SIMPLE_METHOD (CHANGED (typecheck_tac ctxt)));

val _ = OuterSyntax.add_parsers
  [OuterSyntax.improper_command "print_tcset" "print context of ZF typecheck" OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_tcset o Toplevel.context_of)))];


(* theory setup *)

val setup =
  Data.init #>
  Attrib.add_attributes [("TC", TC_att, "declaration of type-checking rule")] #>
  Method.add_methods [("typecheck", typecheck_meth, "ZF type-checking")] #>
  (fn thy => (change_simpset_of thy (fn ss => ss setSolver type_solver); thy));

end;
