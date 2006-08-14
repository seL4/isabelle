(*  Title:      Pure/Tools/codegen_consts.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Distinction of ad-hoc overloaded constants. Convenient data structures
for constants.
*)

signature CODEGEN_CONSTS =
sig
  type const = string * typ list (*type instantiations*)
  val const_ord: const * const -> order
  val eq_const: const * const -> bool
  structure Consttab: TABLE
  val typinst_of_typ: theory -> string * typ -> const
  val typ_of_typinst: theory -> const -> string * typ
  val find_norminst: theory -> const -> (string (*theory name*) * typ list) option
  val norminst_of_typ: theory -> string * typ -> const
  val class_of_classop: theory -> const -> class option
  val insts_of_classop: theory -> const -> const list
  val read_const: theory -> string -> const
  val read_const_typ: theory -> string -> string * typ
  val string_of_const: theory -> const -> string
  val string_of_const_typ: theory -> string * typ -> string
end;

structure CodegenConsts: CODEGEN_CONSTS =
struct


(* basic data structures *)

type const = string * typ list (*type instantiations*);
val const_ord = prod_ord fast_string_ord (list_ord Term.typ_ord);
val eq_const = is_equal o const_ord;

structure Consttab =
  TableFun(
    type key = string * typ list;
    val ord = const_ord;
  );


(* type instantiations and overloading *)

fun typinst_of_typ thy (c_ty as (c, ty)) =
  (*FIXME: better shift to defs.ML?*)
  (c, Consts.typargs (Sign.consts_of thy) c_ty);

fun typ_of_typinst thy (c_tys as (c, tys)) =
  (*FIXME: better shift to defs.ML?*)
  (c, Consts.instance (Sign.consts_of thy) c_tys);

fun find_norminst thy (c, tys) =
  (*FIXME: better shift to defs.ML?*)
  let
    val specs = Defs.specifications_of (Theory.defs_of thy) c;
  in
    get_first (fn (_, { lhs, module, ... }) => if forall (Sign.typ_instance thy)
      (tys ~~ lhs) then SOME (module, lhs) else NONE) specs
  end;

fun norminst_of_typ thy (c, ty) =
  let
    fun disciplined _ [(Type (tyco, _))] =
          [Type (tyco, map (fn v => TVar ((v, 0), Sign.defaultS thy))
            (Name.invents Name.context "'a" (Sign.arity_number thy tyco)))]
      | disciplined sort _ =
          [TVar (("'a", 0), sort)];
    fun ad_hoc c tys =
      case find_norminst thy (c, tys)
       of SOME (_, tys) => (c, tys)
        | NONE => typinst_of_typ thy (c, Sign.the_const_type thy c);
    val tyinsts = Consts.typargs (Sign.consts_of thy) (c, ty);
  in if c = "op =" then (c, disciplined (Sign.defaultS thy) tyinsts)
    (*the distinction on op = will finally disappear!*)
    else case AxClass.class_of_param thy c
     of SOME class => (c, disciplined [class] tyinsts)
      | _ => ad_hoc c tyinsts
  end;

fun class_of_classop thy (c_tys as (c, _)) =
  case AxClass.class_of_param thy c
   of NONE => NONE
    | SOME class => if is_some (find_norminst thy c_tys)
        then NONE
        else SOME class;

fun insts_of_classop thy (c_tys as (c, tys)) =
  case AxClass.class_of_param thy c
   of NONE => [c_tys]
    | SOME _ =>
        map (fn (_, { lhs, ... }) => (c, lhs))
          (Defs.specifications_of (Theory.defs_of thy) c);


(* reading constants as terms *)

fun read_const_typ thy raw_t =
  let
    val t = Sign.read_term thy raw_t
  in case try dest_Const t
   of SOME c_ty => c_ty
    | NONE => error ("not a constant: " ^ Sign.string_of_term thy t)
  end;

fun read_const thy =
  typinst_of_typ thy o read_const_typ thy;


(* printing constants *)

fun string_of_const thy (c, tys) =
  space_implode " " (Sign.extern_const thy c
    :: map (enclose "[" "]" o Sign.string_of_typ thy) tys);

fun string_of_const_typ thy (c, ty) =
  string_of_const thy (c, Consts.typargs (Sign.consts_of thy) (c, ty));

end;
