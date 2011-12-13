(*  Title:      HOL/Tools/Quotient/quotient_def.ML
    Author:     Cezary Kaliszyk and Christian Urban

Definitions for constants on quotient types.
*)

signature QUOTIENT_DEF =
sig
  val quotient_def:
    (binding * typ option * mixfix) option * (Attrib.binding * (term * term)) ->
    local_theory -> Quotient_Info.quotconsts * local_theory

  val quotient_def_cmd:
    (binding * string option * mixfix) option * (Attrib.binding * (string * string)) ->
    local_theory -> Quotient_Info.quotconsts * local_theory

  val lift_raw_const: typ list -> (string * term * mixfix) -> local_theory ->
    Quotient_Info.quotconsts * local_theory
end;

structure Quotient_Def: QUOTIENT_DEF =
struct

(** Interface and Syntax Setup **)

(* The ML-interface for a quotient definition takes
   as argument:

    - an optional binding and mixfix annotation
    - attributes
    - the new constant as term
    - the rhs of the definition as term

   It stores the qconst_info in the quotconsts data slot.

   Restriction: At the moment the left- and right-hand
   side of the definition must be a constant.
*)
fun error_msg bind str =
  let
    val name = Binding.name_of bind
    val pos = Position.str_of (Binding.pos_of bind)
  in
    error ("Head of quotient_definition " ^
      quote str ^ " differs from declaration " ^ name ^ pos)
  end

fun gen_quotient_def prep_vars prep_term (raw_var, (attr, (lhs_raw, rhs_raw))) lthy =
  let
    val (vars, ctxt) = prep_vars (the_list raw_var) lthy
    val T_opt = (case vars of [(_, SOME T, _)] => SOME T | _ => NONE)
    val lhs = prep_term T_opt ctxt lhs_raw
    val rhs = prep_term NONE ctxt rhs_raw

    val (lhs_str, lhs_ty) = dest_Free lhs handle TERM _ => error "Constant already defined."
    val _ = if null (strip_abs_vars rhs) then () else error "The definiens cannot be an abstraction"
    val _ = if is_Const rhs then () else warning "The definiens is not a constant"

    val var =
      (case vars of 
        [] => (Binding.name lhs_str, NoSyn)
      | [(binding, _, mx)] =>
          if Variable.check_name binding = lhs_str then (binding, mx)
          else error_msg binding lhs_str
      | _ => raise Match)

    val absrep_trm = Quotient_Term.absrep_fun lthy Quotient_Term.AbsF (fastype_of rhs, lhs_ty) $ rhs
    val prop = Syntax.check_term lthy (Logic.mk_equals (lhs, absrep_trm))
    val (_, prop') = Local_Defs.cert_def lthy prop
    val (_, newrhs) = Local_Defs.abs_def prop'

    val ((trm, (_ , thm)), lthy') = Local_Theory.define (var, (attr, newrhs)) lthy

    (* data storage *)
    val qconst_data = {qconst = trm, rconst = rhs, def = thm}

    val lthy'' = lthy'
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi =>
          (case Quotient_Info.transform_quotconsts phi qconst_data of
            qcinfo as {qconst = Const (c, _), ...} =>
              Quotient_Info.update_quotconsts c qcinfo
          | _ => I));
  in
    (qconst_data, lthy'')
  end

fun check_term' cnstr ctxt =
  Syntax.check_term ctxt o (case cnstr of SOME T => Type.constraint T | _ => I)

fun read_term' cnstr ctxt =
  check_term' cnstr ctxt o tap (writeln o @{make_string}) o Syntax.parse_term ctxt

val quotient_def = gen_quotient_def Proof_Context.cert_vars check_term'
val quotient_def_cmd = gen_quotient_def Proof_Context.read_vars read_term'


(* a wrapper for automatically lifting a raw constant *)
fun lift_raw_const qtys (qconst_name, rconst, mx) ctxt =
  let
    val rty = fastype_of rconst
    val qty = Quotient_Term.derive_qtyp ctxt qtys rty
    val lhs = Free (qconst_name, qty)
  in
    quotient_def (SOME (Binding.name qconst_name, NONE, mx), (Attrib.empty_binding, (lhs, rconst))) ctxt
  end

(* parser and command *)
val quotdef_parser =
  Scan.option Parse_Spec.constdecl --
    Parse.!!! (Parse_Spec.opt_thm_name ":" -- (Parse.term --| Parse.$$$ "is" -- Parse.term))

val _ =
  Outer_Syntax.local_theory "quotient_definition"
    "definition for constants over the quotient type"
      Keyword.thy_decl (quotdef_parser >> (snd oo quotient_def_cmd))

end; (* structure *)
