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
end;

structure TypeCheck: TYPE_CHECK =
struct

(* datatype tcset *)

datatype tcset = TC of
 {rules: thm list,     (*the type-checking rules*)
  net: thm Net.net};   (*discrimination net of the same rules*)

fun add_rule ctxt th (tcs as TC {rules, net}) =
  if member Thm.eq_thm_prop rules th then
    (warning ("Ignoring duplicate type-checking rule\n" ^ Thm.string_of_thm ctxt th); tcs)
  else
    TC {rules = th :: rules, net = Net.insert_term (K false) (Thm.concl_of th, th) net};

fun del_rule ctxt th (tcs as TC {rules, net}) =
  if member Thm.eq_thm_prop rules th then
    TC {net = Net.delete_term Thm.eq_thm_prop (Thm.concl_of th, th) net,
      rules = remove Thm.eq_thm_prop th rules}
  else (warning ("No such type-checking rule\n" ^ Thm.string_of_thm ctxt th); tcs);


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
    Data.map (add_rule (Context.proof_of context) (Thm.trim_context thm)) context);

val TC_del =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (del_rule (Context.proof_of context) thm) context);

val tcset_of = Data.get o Context.Proof;

fun print_tcset ctxt =
  let val TC {rules, ...} = tcset_of ctxt in
    Pretty.writeln (Pretty.big_list "type-checking rules:"
      (map (Thm.pretty_thm_item ctxt) rules))
  end;


(* tactics *)

(*resolution using a net rather than rules*)
fun net_res_tac ctxt maxr net =
  SUBGOAL
    (fn (prem, i) =>
      let val rls = Net.unify_term net (Logic.strip_assums_concl prem)
      in
         if length rls <= maxr then resolve_tac ctxt rls i else no_tac
      end);

fun is_rigid_elem \<^Const_>\<open>Trueprop for \<open>\<^Const_>\<open>mem for a _\<close>\<close>\<close> = not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*)
fun test_assume_tac ctxt = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac ctxt i  else  eq_assume_tac i);

(*Type checking solves a:?A (a rigid, ?A maybe flexible).
  match_tac is too strict; would refuse to instantiate ?A*)
fun typecheck_step_tac ctxt =
  let val TC {net, ...} = tcset_of ctxt
  in FIRSTGOAL (test_assume_tac ctxt ORELSE' net_res_tac ctxt 3 net) end;

fun typecheck_tac ctxt = REPEAT (typecheck_step_tac ctxt);

(*Compile a term-net for speed*)
val basic_net =
  Tactic.build_net @{thms TrueI refl reflexive iff_refl ballI allI conjI impI};

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_solver_tac ctxt hyps = SELECT_GOAL
    (DEPTH_SOLVE (eresolve_tac ctxt @{thms FalseE} 1
                  ORELSE resolve_from_net_tac ctxt basic_net 1
                  ORELSE (ares_tac ctxt hyps 1
                          APPEND typecheck_step_tac ctxt)));

val type_solver =
  Simplifier.mk_solver "ZF typecheck" (fn ctxt =>
    type_solver_tac ctxt (Simplifier.prems_of ctxt));

val _ = Theory.setup (map_theory_simpset (fn ctxt => ctxt setSolver type_solver));


(* concrete syntax *)

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>TC\<close> (Attrib.add_del TC_add TC_del)
      "declaration of type-checking rule" #>
    Method.setup \<^binding>\<open>typecheck\<close>
      (Method.sections
        [Args.add -- Args.colon >> K (Method.modifier TC_add \<^here>),
         Args.del -- Args.colon >> K (Method.modifier TC_del \<^here>)]
        >> K (fn ctxt => SIMPLE_METHOD (CHANGED (typecheck_tac ctxt))))
      "ZF type-checking");

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_tcset\<close> "print context of ZF typecheck"
    (Scan.succeed (Toplevel.keep (print_tcset o Toplevel.context_of)));

end;
