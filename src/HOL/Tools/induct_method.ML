(*  Title:      HOL/Tools/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by induction on types / set / functions.

TODO:
  - induct vs. coinduct (!?);
  - use of 'function' (!?);
*)

signature INDUCT_METHOD =
sig
  val setup: (theory -> theory) list
end;

structure InductMethod: INDUCT_METHOD =
struct


(* type induct_kind *)

datatype induct_kind = Type | Set | Function;

val typeN = "type";
val setN = "set";
val functionN = "function";

val kind =
  (Args.$$$ typeN >> K Type || Args.$$$ setN >> K Set || Args.$$$ functionN >> K Function)
    --| Args.$$$ ":";


(* induct_tac *)

fun induct_rule thy Type name = #induction (DatatypePackage.datatype_info thy name)
  | induct_rule thy Set name = #induct (#2 (InductivePackage.get_inductive thy name))
  | induct_rule thy Function name = #induct (RecdefPackage.get_recdef thy name);


fun induct_tac thy xs opt_kind_name i state =
  let
    val (kind, name) =
      (case opt_kind_name of Some kind_name => kind_name | None =>
        (case try (#1 o Term.dest_Type o Term.type_of o hd) xs of
          Some name => (Type, name)
        | None => error "Unable to figure out induction rule"));
    val rule = Drule.incr_indexes_wrt [] [] [] [state] (induct_rule thy kind name);

    fun inst_rule () =
      let
        val cert = Thm.cterm_of (Sign.merge (pairself Thm.sign_of_thm (state, rule)));
        fun rule_var (_ $ x) = cert x
          | rule_var _ = raise THM ("Malformed induction rule", 0, [rule]);
        val rule_preds = DatatypeAux.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of rule));
      in Drule.cterm_instantiate (map rule_var rule_preds ~~ map cert xs) rule end;
  in Tactic.rtac (if null xs then rule else inst_rule ()) i state end;


(* induct_method *)

val term = Scan.unless (Scan.lift kind) Args.local_term;

fun induct ctxt =
  Scan.repeat term -- Scan.option (Scan.lift (kind -- Args.name))
  >> (fn (xs, k) => Method.METHOD0 (FIRSTGOAL (induct_tac (ProofContext.theory_of ctxt) xs k)));

fun induct_meth src ctxt = #2 (Method.syntax (induct ctxt) ctxt src);
val induct_method = ("induct", induct_meth, "induction on types / sets / functions");


(* theory setup *)

val setup = [Method.add_methods [induct_method]];


end;
