(*  Title:      Pure/Tools/codegen_consts.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Identifying constants by name plus normalized type instantantiation schemes.
Type normalization is compatible with overloading discipline and user-defined
ad-hoc overloading.  Convenient data structures for constants.
*)

signature CODEGEN_CONSTS =
sig
  type const = string * typ list (*type instantiations*)
  val const_ord: const * const -> order
  val eq_const: const * const -> bool
  structure Consttab: TABLE
  val inst_of_typ: theory -> string * typ -> const
  val typ_of_inst: theory -> const -> string * typ
  val norm: theory -> const -> const
  val norm_of_typ: theory -> string * typ -> const
  val find_def: theory -> const
    -> ((string (*theory name*) * thm) * typ list) option
  val instance_dict: theory -> class * string
    -> (string * sort) list * (string * typ) list
  val disc_typ_of_classop: theory -> const -> typ
  val disc_typ_of_const: theory -> (const -> typ) -> const -> typ
  val consts_of: theory -> term -> const list
  val read_const: theory -> string -> const
  val string_of_const: theory -> const -> string
  val raw_string_of_const: const -> string
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


(* type instantiations, overloading, dictionary values *)

fun inst_of_typ thy (c_ty as (c, ty)) =
  (c, Consts.typargs (Sign.consts_of thy) c_ty);

fun typ_of_inst thy (c_tys as (c, tys)) =
  (c, Consts.instance (Sign.consts_of thy) c_tys);

fun find_def thy (c, tys) =
  let
    val specs = Defs.specifications_of (Theory.defs_of thy) c;
    val typ_instance = case AxClass.class_of_param thy c
     of SOME _ => let
          fun instance_tycos (Type (tyco1, _), Type (tyco2, _)) = tyco1 = tyco2
            | instance_tycos (_ , TVar _) = true
            | instance_tycos ty_ty = Sign.typ_instance thy ty_ty;
        in instance_tycos end
      | NONE =>  Sign.typ_instance thy;
    fun get_def (_, { is_def, thyname, name, lhs, rhs }) =
      if is_def andalso forall typ_instance (tys ~~ lhs) then
        case try (Thm.get_axiom_i thy) name
         of SOME thm => SOME ((thyname, thm), lhs)
          | NONE => NONE
      else NONE
  in
    get_first get_def specs
  end;

fun mk_classop_typinst thy (c, tyco) =
  (c, [Type (tyco, map (fn v => TVar ((v, 0), Sign.defaultS thy (*for monotonicity*)))
    (Name.invents Name.context "'a" (Sign.arity_number thy tyco)))]);

fun norm thy (c, insts) =
  let
    fun disciplined _ [(Type (tyco, _))] =
          mk_classop_typinst thy (c, tyco)
      | disciplined sort _ =
          (c, [TVar (("'a", 0), sort)]);
    fun ad_hoc c tys =
      case find_def thy (c, tys)
       of SOME (_, tys) => (c, tys)
        | NONE => inst_of_typ thy (c, Sign.the_const_type thy c);
  in case AxClass.class_of_param thy c
     of SOME class => disciplined [class] insts
      | _ => ad_hoc c insts
  end;

fun norm_of_typ thy (c, ty) =
  norm thy (c, Consts.typargs (Sign.consts_of thy) (c, ty));

fun instance_dict thy (class, tyco) =
  let
    val (var, cs) = AxClass.params_of_class thy class;
    val sort_args = Name.names (Name.declare var Name.context) "'a"
      (Sign.arity_sorts thy tyco [class]);
    val ty_inst = Type (tyco, map TFree sort_args);
    val inst_signs = (map o apsnd o map_type_tfree) (K ty_inst) cs;
  in (sort_args, inst_signs) end;

fun disc_typ_of_classop thy (c, [ty]) = 
  let
    val class = (the o AxClass.class_of_param thy) c;
    val cs = case ty
     of TVar _ => snd (AxClass.params_of_class thy class)
      | TFree _ => snd (AxClass.params_of_class thy class)
      | Type (tyco, _) => snd (instance_dict thy (class, tyco));
  in
    (Logic.varifyT o the o AList.lookup (op =) cs) c
  end;

fun disc_typ_of_const thy f (const as (c, [ty])) =
      if (is_some o AxClass.class_of_param thy) c
      then disc_typ_of_classop thy const
      else f const
  | disc_typ_of_const thy f const = f const;

fun consts_of thy t =
  fold_aterms (fn Const c => cons (norm_of_typ thy c) | _ => I) t []


(* reading constants as terms *)

fun read_const_typ thy raw_t =
  let
    val t = Sign.read_term thy raw_t
  in case try dest_Const t
   of SOME c_ty => (typ_of_inst thy o norm_of_typ thy) c_ty
    | NONE => error ("Not a constant: " ^ Sign.string_of_term thy t)
  end;

fun read_const thy =
  norm_of_typ thy o read_const_typ thy;


(* printing constants *)

fun string_of_const thy (c, tys) =
  space_implode " " (Sign.extern_const thy c
    :: map (enclose "[" "]" o Sign.string_of_typ thy) tys);

fun raw_string_of_const (c, tys) =
  space_implode " " (c
    :: map (enclose "[" "]" o Display.raw_string_of_typ) tys);

fun string_of_const_typ thy (c, ty) =
  string_of_const thy (c, Consts.typargs (Sign.consts_of thy) (c, ty));

end;
