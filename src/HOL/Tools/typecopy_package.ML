(*  Title:      HOL/Tools/typecopy_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Introducing copies of types using trivial typedefs; datatype-like abstraction.
*)

signature TYPECOPY_PACKAGE =
sig
  type info = {
    vs: (string * sort) list,
    constr: string,
    typ: typ,
    inject: thm,
    proj: string * typ,
    proj_def: thm
  }
  val add_typecopy: bstring * string list -> typ -> (bstring * bstring) option
    -> theory -> (string * info) * theory
  val get_typecopies: theory -> string list
  val get_typecopy_info: theory -> string -> info option
  val interpretation: (string * info -> theory -> theory) -> theory -> theory
  val get_spec: theory -> string -> (string * sort) list * (string * typ list) list
  val get_eq: theory -> string -> thm
  val print_typecopies: theory -> unit
  val setup: theory -> theory
end;

structure TypecopyPackage: TYPECOPY_PACKAGE =
struct

(* theory data *)

type info = {
  vs: (string * sort) list,
  constr: string,
  typ: typ,
  inject: thm,
  proj: string * typ,
  proj_def: thm
};

structure TypecopyData = TheoryDataFun
(
  type T = info Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (K true);
);

fun print_typecopies thy =
  let
    val tab = TypecopyData.get thy;
    fun mk (tyco, { vs, constr, typ, proj = (proj, _), ... } : info) =
      (Pretty.block o Pretty.breaks) [
        Sign.pretty_typ thy (Type (tyco, map TFree vs)),
        Pretty.str "=",
        (Pretty.str o Sign.extern_const thy) constr,
        Sign.pretty_typ thy typ,
        Pretty.block [Pretty.str "(", (Pretty.str o Sign.extern_const thy) proj, Pretty.str  ")"]];
    in
      (Pretty.writeln o Pretty.block o Pretty.fbreaks)
        (Pretty.str "type copies:" :: map mk (Symtab.dest tab))
    end;

val get_typecopies = Symtab.keys o TypecopyData.get;
val get_typecopy_info = Symtab.lookup o TypecopyData.get;


(* interpretation *)

structure TypecopyInterpretation = InterpretationFun(type T = string val eq = op =);

fun interpretation interp = TypecopyInterpretation.interpretation
  (fn tyco => fn thy => interp (tyco, (the o get_typecopy_info thy) tyco) thy);


(* add a type copy *)

local

fun gen_add_typecopy prep_typ (raw_tyco, raw_vs) raw_ty constr_proj thy =
  let
    val ty = prep_typ thy raw_ty;
    val vs = AList.make (the_default HOLogic.typeS o AList.lookup (op =) (typ_tfrees ty)) raw_vs;
    val tac = Tactic.rtac UNIV_witness 1;
    fun add_info tyco ( { abs_type = ty_abs, rep_type = ty_rep, Abs_name = c_abs,
      Rep_name = c_rep, Abs_inject = inject,
      Abs_inverse = inverse, ... } : TypedefPackage.info ) thy =
        let
          val exists_thm =
            UNIV_I
            |> Drule.instantiate' [SOME (ctyp_of thy (Logic.varifyT ty_rep))] [];
          val inject' = inject OF [exists_thm, exists_thm];
          val proj_def = inverse OF [exists_thm];
          val info = {
            vs = vs,
            constr = c_abs,
            typ = ty_rep,
            inject = inject',
            proj = (c_rep, ty_abs --> ty_rep),
            proj_def = proj_def
          };
        in
          thy
          |> (TypecopyData.map o Symtab.update_new) (tyco, info)
          |> TypecopyInterpretation.data tyco
          |> pair (tyco, info)
        end
  in
    thy
    |> setmp TypedefPackage.quiet_mode true
        (TypedefPackage.add_typedef_i false (SOME raw_tyco) (raw_tyco, map fst vs, NoSyn)
          (HOLogic.mk_UNIV ty) (Option.map swap constr_proj)) tac
    |-> (fn (tyco, info) => add_info tyco info)
  end;

in

val add_typecopy = gen_add_typecopy Sign.certify_typ;

end;


(* equality function equation and datatype specification *)

fun get_eq thy tyco =
  (#inject o the o get_typecopy_info thy) tyco;

fun get_spec thy tyco =
  let
    val SOME { vs, constr, typ, ... } = get_typecopy_info thy tyco
  in (vs, [(constr, [typ])]) end;


(* interpretation for projection function code *)

fun add_project (_, {proj_def, ...} : info) = Code.add_default_func proj_def;

val setup = TypecopyInterpretation.init #> interpretation add_project;

end;
