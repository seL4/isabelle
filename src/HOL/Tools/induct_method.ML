(*  Title:      HOL/Tools/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof methods for cases and induction on types / sets / functions.
*)

signature INDUCT_METHOD =
sig
  val setup: (theory -> theory) list
end;

structure InductMethod: INDUCT_METHOD =
struct


(** utils **)

(* vars_of *)

fun vars_of tm =        (*ordered left-to-right, preferring right!*)
  foldl_aterms (fn (ts, t as Var _) => t :: ts | (ts, _) => ts) ([], tm)
  |> Library.distinct |> rev;


(* kinds *)

datatype kind = Type | Set | Function | Rule;

fun intern_kind Type = Sign.intern_tycon
  | intern_kind Set = Sign.intern_const
  | intern_kind Function = Sign.intern_const
  | intern_kind Rule = K I;	(* FIXME !? *)



(** cases method **)

fun cases_rule Type = DatatypePackage.cases_of o Theory.sign_of
  | cases_rule Set = InductivePackage.cases_of o Theory.sign_of
  | cases_rule Function = (fn _ => error "No cases rule for recursive functions")
  | cases_rule Rule = PureThy.get_thm;

val cases_var = hd o vars_of o hd o Logic.strip_assums_hyp o Library.last_elem o Thm.prems_of;


fun cases_tac (None, None) ctxt =
      Method.rule_tac (case_split_thm :: InductivePackage.cases (ProofContext.sign_of ctxt))
  | cases_tac args ctxt =
      let
        val thy = ProofContext.theory_of ctxt;
        val sign = Theory.sign_of thy;
        val cert = Thm.cterm_of sign;

        val (kind, name) =
          (case args of
            (_, Some (kind, bname)) => (kind, intern_kind kind sign bname)
          | (Some t, _) =>
              (case try (#1 o Term.dest_Type o Term.type_of) t of
                Some name => (Type, name)
              | None => error "Need specific type to figure out cases rule")
          | _ => sys_error "cases_tac");
        val rule = cases_rule kind thy name;

        val inst_rule =
          (case #1 args of
            None => rule
          | Some t => Drule.cterm_instantiate [(cert (cases_var rule), cert t)] rule);
  in Method.rule_tac [inst_rule] end;

val cases_meth = Method.METHOD oo (FINDGOAL ooo cases_tac);



(** induct method **)

fun induct_rule Type = #induction oo DatatypePackage.datatype_info_err
  | induct_rule Set = (#induct o #2) oo InductivePackage.get_inductive
  | induct_rule Function = #induct oo RecdefPackage.get_recdef
  | induct_rule Rule = PureThy.get_thm;

fun induct_tac (insts, opt_kind_name) ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val sign = Theory.sign_of thy;
    val cert = Thm.cterm_of sign;

    val (kind, name) =
      (case opt_kind_name of
        Some (kind, bname) => (kind, intern_kind kind sign bname)
      | None =>
          (case try (#1 o Term.dest_Type o Term.type_of o Library.last_elem o hd) insts of
            Some name => (Type, name)
          | None => error "Unable to figure out induction rule"));
    val rule = induct_rule kind thy name;

    fun prep_inst (concl, ts) =
      let
        val xs = vars_of concl;
        val n = length xs - length ts;
      in
        if n < 0 then raise THM ("More arguments given than in induction rule", 0, [rule])
        else map cert (Library.drop (n, xs)) ~~ map cert ts
      end;

    val prep_insts = flat o map2 prep_inst;

    val inst_rule =
      if null insts then rule
      else Drule.cterm_instantiate (prep_insts
        (DatatypeAux.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of rule)), insts)) rule;
  in Method.rule_tac [inst_rule] end;

val induct_meth = Method.METHOD oo (FINDGOAL ooo induct_tac);



(** concrete syntax **)

local

val kind_name =
  Args.$$$ "type" >> K Type ||
  Args.$$$ "set" >> K Set ||
  Args.$$$ "function" >> K Function ||
  Args.$$$ "rule" >> K Rule;

val kind_spec = kind_name --| Args.$$$ ":";

val kind = Scan.lift (kind_spec -- Args.name);
val term = Scan.unless (Scan.lift (Scan.option (Args.$$$ "in") -- kind_spec)) Args.local_term;

fun argument is_empty arg = arg :-- (fn x =>
  Scan.option (if is_empty x then kind else Scan.lift (Args.$$$ "in") |-- kind));

in

fun cases_args f src ctxt =
  f (#2 (Method.syntax (argument is_none (Scan.option term)) src ctxt)) ctxt;

fun induct_args f src ctxt =
  f (#2 (Method.syntax (argument null (Args.and_list (Scan.repeat1 term))) src ctxt)) ctxt;

end;



(** theory setup **)

val setup =
 [Method.add_methods
  [("cases", cases_args cases_meth, "case analysis on types / sets"),
   ("induct", induct_args induct_meth, "induction on types / sets / functions")]];


end;
