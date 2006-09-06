(*  Title:      HOL/Tools/typecopy_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Introducing copies of types using trivial typedefs.
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
  type hook = string * info -> theory -> theory;
  val add_hook: hook -> theory -> theory;
  val typecopy_fun_extr: theory -> string * typ -> thm list option
  val typecopy_type_extr: theory -> string
    -> (((string * sort) list * (string * typ list) list) * tactic) option
  val print: theory -> unit
  val setup: theory -> theory
end;

structure TypecopyPackage: TYPECOPY_PACKAGE =
struct

(* theory context reference *)

val univ_witness = thm "Set.UNIV_witness"


(* theory data *)

type info = {
  vs: (string * sort) list,
  constr: string,
  typ: typ,
  inject: thm,
  proj: string * typ,
  proj_def: thm
};

type hook = string * info -> theory -> theory;

structure TypecopyData = TheoryDataFun
(struct
  val name = "HOL/typecopy_package";
  type T = info Symtab.table * (serial * hook) list;
  val empty = (Symtab.empty, []);
  val copy = I;
  val extend = I;
  fun merge _ ((tab1, hooks1), (tab2, hooks2) : T) =
    (Symtab.merge (K true) (tab1, tab2), AList.merge (op =) (K true) (hooks1, hooks2));
  fun print thy (tab, _) =
    let
      fun mk (tyco, { vs, constr, typ, proj = (proj, _), ... } : info) =
        (Pretty.block o Pretty.breaks) [
          Sign.pretty_typ thy (Type (tyco, map TFree vs)),
          Pretty.str "=",
          (Pretty.str o Sign.extern_const thy) constr,
          Sign.pretty_typ thy typ,
          Pretty.block [Pretty.str "(", (Pretty.str o Sign.extern_const thy) proj, Pretty.str  ")"]
        ];
    in
      (Pretty.writeln o Pretty.block o Pretty.fbreaks) (
        Pretty.str "type copies:"
        :: map mk (Symtab.dest tab)
      )
    end;
end);

val print = TypecopyData.print;
val get_typecopies = Symtab.keys o fst o TypecopyData.get;
val get_typecopy_info = Symtab.lookup o fst o TypecopyData.get;


(* hook management *)

fun add_hook hook =
  (TypecopyData.map o apsnd o cons) (serial (), hook);

fun invoke_hooks tyco_info thy =
  fold (fn (_, f) => f tyco_info) ((snd o TypecopyData.get) thy) thy;


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
          |> (TypecopyData.map o apfst o Symtab.update_new) (tyco, info)
          |> invoke_hooks (tyco, info)
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

end; (*local*)


(* theory setup *)

fun typecopy_type_extr thy tyco =
  case get_typecopy_info thy tyco
   of SOME { vs, constr, typ, inject, ... } => SOME ((vs, [(constr, [typ])]),
       (ALLGOALS o match_tac) [eq_reflection]
          THEN (ALLGOALS o match_tac) [inject])
    | NONE => NONE;

fun typecopy_fun_extr thy (c, ty) =
  case (fst o strip_type) ty
   of Type (tyco, _) :: _ =>
        (case get_typecopy_info thy tyco
          of SOME { proj_def, proj as (c', _), ... } =>
              if c = c' then SOME [proj_def] else NONE
           | NONE => NONE)
    | _ => NONE;

val setup =
  TypecopyData.init
  #> CodegenTheorems.add_fun_extr (these oo typecopy_fun_extr)
  #> CodegenTheorems.add_datatype_extr typecopy_type_extr;

end; (*struct*)
