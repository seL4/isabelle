(*  Title:      ZF/Tools/typechk.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Tactics for type checking -- from CTT.
*)

infix 4 addTCs delTCs;

signature BASIC_TYPE_CHECK =
sig
  type tcset
  val addTCs: tcset * thm list -> tcset
  val delTCs: tcset * thm list -> tcset
  val typecheck_tac: tcset -> tactic
  val type_solver_tac: tcset -> thm list -> int -> tactic
  val print_tc: tcset -> unit
  val print_tcset: theory -> unit
  val tcset_ref_of: theory -> tcset ref
  val tcset_of: theory -> tcset
  val tcset: unit -> tcset
  val AddTCs: thm list -> unit
  val DelTCs: thm list -> unit
  val TC_add_global: theory attribute
  val TC_del_global: theory attribute
  val TC_add_local: Proof.context attribute
  val TC_del_local: Proof.context attribute
  val Typecheck_tac: tactic
  val Type_solver_tac: thm list -> int -> tactic
end;

signature TYPE_CHECK =
sig
  include BASIC_TYPE_CHECK
  val setup: (theory -> theory) list
end;

structure TypeCheck: TYPE_CHECK =
struct

datatype tcset =
    TC of {rules: thm list,     (*the type-checking rules*)
           net: thm Net.net};   (*discrimination net of the same rules*)


val mem_thm = gen_mem eq_thm
and rem_thm = gen_rem eq_thm;

fun addTC (cs as TC{rules, net}, th) =
  if mem_thm (th, rules) then
         (warning ("Ignoring duplicate type-checking rule\n" ^
                   string_of_thm th);
          cs)
  else
      TC{rules  = th::rules,
         net = Net.insert_term ((concl_of th, th), net, K false)};


fun delTC (cs as TC{rules, net}, th) =
  if mem_thm (th, rules) then
      TC{net = Net.delete_term ((concl_of th, th), net, eq_thm),
         rules  = rem_thm (rules,th)}
  else (warning ("No such type-checking rule\n" ^ (string_of_thm th));
        cs);

val op addTCs = foldl addTC;
val op delTCs = foldl delTC;


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

fun typecheck_tac tcset = REPEAT (typecheck_step_tac tcset);

(*Compiles a term-net for speed*)
val basic_res_tac = net_resolve_tac [TrueI,refl,reflexive_thm,iff_refl,
                                     ballI,allI,conjI,impI];

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_solver_tac tcset hyps = SELECT_GOAL
    (DEPTH_SOLVE (etac FalseE 1
                  ORELSE basic_res_tac 1
                  ORELSE (ares_tac hyps 1
                          APPEND typecheck_step_tac tcset)));



fun merge_tc (TC{rules,net}, TC{rules=rules',net=net'}) =
    TC {rules = gen_union eq_thm (rules,rules'),
        net = Net.merge (net, net', eq_thm)};

(*print tcsets*)
fun print_tc (TC{rules,...}) =
    Pretty.writeln
       (Pretty.big_list "type-checking rules:" (map Display.pretty_thm rules));


(** global tcset **)

structure TypecheckingArgs =
  struct
  val name = "ZF/type-checker";
  type T = tcset ref;
  val empty = ref (TC{rules=[], net=Net.empty});
  fun copy (ref tc) = ref tc;
  val finish = I;
  val prep_ext = copy;
  fun merge (ref tc1, ref tc2) = ref (merge_tc (tc1, tc2));
  fun print _ (ref tc) = print_tc tc;
  end;

structure TypecheckingData = TheoryDataFun(TypecheckingArgs);

val print_tcset = TypecheckingData.print;
val tcset_ref_of_sg = TypecheckingData.get_sg;
val tcset_ref_of = TypecheckingData.get;


(* access global tcset *)

val tcset_of_sg = ! o tcset_ref_of_sg;
val tcset_of = tcset_of_sg o sign_of;

val tcset = tcset_of o Context.the_context;
val tcset_ref = tcset_ref_of_sg o sign_of o Context.the_context;


(* change global tcset *)

fun change_tcset f x = tcset_ref () := (f (tcset (), x));

val AddTCs = change_tcset (op addTCs);
val DelTCs = change_tcset (op delTCs);

fun Typecheck_tac st = typecheck_tac (tcset()) st;

fun Type_solver_tac hyps = type_solver_tac (tcset()) hyps;



(** local tcset **)

structure LocalTypecheckingArgs =
struct
  val name = TypecheckingArgs.name;
  type T = tcset;
  val init = tcset_of;
  fun print _ tcset = print_tc tcset;
end;

structure LocalTypecheckingData = ProofDataFun(LocalTypecheckingArgs);


(* attributes *)

fun global_att f (thy, th) =
  let val r = tcset_ref_of thy
  in r := f (! r, th); (thy, th) end;

fun local_att f (ctxt, th) = (LocalTypecheckingData.map (fn tcset => f (tcset, th)) ctxt, th);

val TC_add_global = global_att addTC;
val TC_del_global = global_att delTC;
val TC_add_local = local_att addTC;
val TC_del_local = local_att delTC;

val TC_attr =
 (Attrib.add_del_args TC_add_global TC_del_global,
  Attrib.add_del_args TC_add_local TC_del_local);


(* methods *)

fun TC_args x = Method.only_sectioned_args
  [Args.add -- Args.colon >> K (I, TC_add_local),
   Args.del -- Args.colon >> K (I, TC_del_local)] x;

fun typecheck ctxt =
  Method.SIMPLE_METHOD (CHANGED (typecheck_tac (LocalTypecheckingData.get ctxt)));



(** theory setup **)

val setup =
 [TypecheckingData.init, LocalTypecheckingData.init,
  Attrib.add_attributes [("TC", TC_attr, "declaration of typecheck rule")],
  Method.add_methods [("typecheck", TC_args typecheck, "ZF typecheck")]];


(** outer syntax **)

val print_tcsetP =
  OuterSyntax.improper_command "print_tcset" "print context of ZF type-checker"
    OuterSyntax.Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o (Toplevel.keep
      (Toplevel.node_case print_tcset (LocalTypecheckingData.print o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_tcsetP];


end;

structure BasicTypeCheck: BASIC_TYPE_CHECK = TypeCheck;
open BasicTypeCheck;
