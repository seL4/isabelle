(*  Title:      HOL/Tools/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by induction on types / set / functions.
*)

signature INDUCT_METHOD =
sig
  val setup: (theory -> theory) list
end;

structure InductMethod: INDUCT_METHOD =
struct


(* type induct_kind *)

datatype induct_kind = Type | Set | Function | Rule;

val kind_name =
  Args.$$$ "type" >> K Type ||
  Args.$$$ "set" >> K Set ||
  Args.$$$ "function" >> K Function ||
  Args.$$$ "rule" >> K Rule;

val kind = kind_name --| Args.$$$ ":";


(* induct_rule *)

fun kind_rule Type = (#induction oo DatatypePackage.datatype_info_err, Sign.intern_tycon)
  | kind_rule Set = ((#induct o #2) oo InductivePackage.get_inductive, Sign.intern_const)
  | kind_rule Function = (#induct oo RecdefPackage.get_recdef, Sign.intern_const)
  | kind_rule Rule = (PureThy.get_thm, K I);

fun induct_rule thy kind name =
  let val (ind_rule, intern) = kind_rule kind
  in ind_rule thy (intern (Theory.sign_of thy) name) end;


(* induct_tac *)

fun induct_tac thy insts opt_kind_name facts i state =
  let
    val (kind, name) =
      (case opt_kind_name of Some kind_name => kind_name | None =>
        (case try (#1 o Term.dest_Type o Term.type_of o #2 o hd) insts of
          Some name => (Type, name)
        | None => error "Unable to figure out induction rule"));
    val rule = Drule.incr_indexes_wrt [] [] [] [state] (induct_rule thy kind name);

    val cert = Thm.cterm_of (Sign.merge (pairself Thm.sign_of_thm (state, rule)));

    fun prep_inst ((P $ x), (Some Q, y)) = [(cert P, cert Q), (cert x, cert y)]
      | prep_inst ((_ $ x), (None, y)) = [(cert x, cert y)]
      | prep_inst _ = raise THM ("Malformed induction rule", 0, [rule]);

    val prep_insts = flat o map2 prep_inst;

    val inst_rule =
      if null insts then rule
      else Drule.cterm_instantiate (prep_insts
        (DatatypeAux.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of rule)), insts)) rule;
  in Method.rule_tac [inst_rule] facts i state end;


(* induct_method *)

val term = Scan.unless (Scan.lift kind) Args.local_term;
val inst = term -- term >> (apfst Some) || term >> pair None;

fun induct ctxt =
  Args.and_list inst -- Scan.option (Scan.lift (kind -- Args.name))
  >> (fn (is, k) => Method.METHOD (FINDGOAL o induct_tac (ProofContext.theory_of ctxt) is k));

fun induct_meth src ctxt = #2 (Method.syntax (induct ctxt) ctxt src);
val induct_method = ("induct", induct_meth, "induction on types, sets, functions etc.");


(* theory setup *)

val setup = [Method.add_methods [induct_method]];


end;
