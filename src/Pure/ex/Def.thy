(*  Title:      Pure/ex/Def.thy
    Author:     Makarius

Primitive constant definition, without fact definition;
automatic expansion via Simplifier (simproc).
*)

theory Def
  imports Pure
  keywords "def" :: thy_defn
begin

ML \<open>
signature DEF =
sig
  val get_def: Proof.context -> cterm -> thm option
  val def: (binding * typ option * mixfix) option ->
    (binding * typ option * mixfix) list -> term -> local_theory -> term * local_theory
  val def_cmd: (binding * string option * mixfix) option ->
    (binding * string option * mixfix) list -> string -> local_theory -> term * local_theory
end;

structure Def: DEF =
struct

(* context data *)

type def = {lhs: term, mk_eq: morphism -> thm};

val eq_def : def * def -> bool = op aconv o apply2 #lhs;

fun transform_def phi ({lhs, mk_eq}: def) =
  {lhs = Morphism.term phi lhs, mk_eq = Morphism.transform phi mk_eq};

structure Data = Generic_Data
(
  type T = def Item_Net.T;
  val empty : T = Item_Net.init eq_def (single o #lhs);
  val extend = I;
  val merge = Item_Net.merge;
);

fun declare_def lhs eq lthy =
  let
    val eq0 = Thm.trim_context eq;
    val def: def = {lhs = lhs, mk_eq = fn phi => Morphism.thm phi eq0};
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi => (Data.map o Item_Net.update) (transform_def phi def))
  end;

fun get_def ctxt ct =
  let
    val thy = Proof_Context.theory_of ctxt;
    val data = Data.get (Context.Proof ctxt);
    val t = Thm.term_of ct;
    fun match_def {lhs, mk_eq} =
      if Pattern.matches thy (lhs, t) then
        let
          val inst = Thm.match (Thm.cterm_of ctxt lhs, ct);
          val eq =
            Morphism.form mk_eq
            |> Thm.transfer thy
            |> Thm.instantiate inst;
        in SOME eq end
      else NONE;
  in Item_Net.retrieve_matching data t |> get_first match_def end;


(* simproc setup *)

val _ =
  (Theory.setup o Named_Target.theory_map)
    (Simplifier.define_simproc \<^binding>\<open>expand_def\<close>
      {lhss = [Free ("x", TFree ("'a", []))], proc = K get_def});


(* Isar command *)

fun gen_def prep_spec raw_var raw_params raw_spec lthy =
  let
    val ((vars, xs, get_pos, spec), _) = lthy
      |> prep_spec (the_list raw_var) raw_params [] raw_spec;
    val (((x, _), rhs), prove) = Local_Defs.derived_def lthy get_pos {conditional = false} spec;
    val _ = Name.reject_internal (x, []);
    val (b, mx) =
      (case (vars, xs) of
        ([], []) => (Binding.make (x, (case get_pos x of [] => Position.none | p :: _ => p)), NoSyn)
      | ([(b, _, mx)], [y]) =>
          if x = y then (b, mx)
          else
            error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote y ^
              Position.here (Binding.pos_of b)));
    val ((lhs, (_, eq)), lthy') = lthy
      |> Local_Theory.define_internal ((b, mx), (Binding.empty_atts, rhs));

    (*sanity check for original specification*)
    val _: thm = prove lthy' eq;
  in (lhs, declare_def lhs eq lthy') end;

val def = gen_def Specification.check_spec_open;
val def_cmd = gen_def Specification.read_spec_open;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>def\<close>
    "primitive constant definition, without fact definition"
    (Scan.option Parse_Spec.constdecl -- Parse.prop -- Parse.for_fixes
      >> (fn ((decl, spec), params) => #2 o def_cmd decl params spec));

end;
\<close>

end
