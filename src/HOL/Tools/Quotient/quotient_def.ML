(*  Title:      HOL/Tools/Quotient/quotient_def.thy
    Author:     Cezary Kaliszyk and Christian Urban

Definitions for constants on quotient types.
*)

signature QUOTIENT_DEF =
sig
  val quotient_def: (binding option * mixfix) * (Attrib.binding * (term * term)) ->
    local_theory -> Quotient_Info.qconsts_info * local_theory

  val quotdef_cmd: (binding option * mixfix) * (Attrib.binding * (string * string)) ->
    local_theory -> Quotient_Info.qconsts_info * local_theory

  val lift_raw_const: typ list -> (string * term * mixfix) -> local_theory ->
    Quotient_Info.qconsts_info * local_theory
end;

structure Quotient_Def: QUOTIENT_DEF =
struct

open Quotient_Info;
open Quotient_Term;

(** Interface and Syntax Setup **)

(* The ML-interface for a quotient definition takes
   as argument:

    - an optional binding and mixfix annotation
    - attributes
    - the new constant as term
    - the rhs of the definition as term

   It stores the qconst_info in the qconsts data slot.

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

fun quotient_def ((optbind, mx), (attr, (lhs, rhs))) lthy =
let
  val (lhs_str, lhs_ty) = dest_Free lhs handle TERM _ => error "Constant already defined."
  val _ = if is_Const rhs then () else error "The definiens should be a constant"
  
  fun sanity_test NONE _ = true
    | sanity_test (SOME bind) str =
        if Name.of_binding bind = str then true
        else error_msg bind str

  val _ = sanity_test optbind lhs_str

  val qconst_bname = Binding.name lhs_str
  val absrep_trm = absrep_fun AbsF lthy (fastype_of rhs, lhs_ty) $ rhs
  val prop = Logic.mk_equals (lhs, Syntax.check_term lthy absrep_trm)
  val (_, prop') = Local_Defs.cert_def lthy prop
  val (_, newrhs) = Local_Defs.abs_def prop'

  val ((trm, (_ , thm)), lthy') = Local_Theory.define ((qconst_bname, mx), (attr, newrhs)) lthy

  (* data storage *)
  val qconst_data = {qconst = trm, rconst = rhs, def = thm}

  fun qcinfo phi = transform_qconsts phi qconst_data
  fun trans_name phi = (fst o dest_Const o #qconst) (qcinfo phi)
  val lthy'' = Local_Theory.declaration true
                 (fn phi => qconsts_update_gen (trans_name phi) (qcinfo phi)) lthy'
in
  (qconst_data, lthy'')
end

fun quotdef_cmd (decl, (attr, (lhs_str, rhs_str))) lthy =
let
  val lhs = Syntax.read_term lthy lhs_str
  val rhs = Syntax.read_term lthy rhs_str
  val lthy' = Variable.declare_term lhs lthy
  val lthy'' = Variable.declare_term rhs lthy'
in
  quotient_def (decl, (attr, (lhs, rhs))) lthy''
end

(* a wrapper for automatically lifting a raw constant *)
fun lift_raw_const qtys (qconst_name, rconst, mx) ctxt =
let
  val rty = fastype_of rconst
  val qty = derive_qtyp qtys rty ctxt
  val lhs = Free (qconst_name, qty)
in
  quotient_def ((NONE, mx), (Attrib.empty_binding, (lhs, rconst))) ctxt
end

(* parser and command *)
val quotdef_decl = (Parse.binding >> SOME) -- Parse.opt_mixfix' --| Parse.$$$ "where"

val quotdef_parser =
  Scan.optional quotdef_decl (NONE, NoSyn) -- 
    Parse.!!! (Parse_Spec.opt_thm_name ":" -- (Parse.term --| Parse.$$$ "is" -- Parse.term))

val _ =
  Outer_Syntax.local_theory "quotient_definition"
    "definition for constants over the quotient type"
      Keyword.thy_decl (quotdef_parser >> (snd oo quotdef_cmd))

end; (* structure *)
