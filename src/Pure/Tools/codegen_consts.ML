(*  Title:      Pure/Tools/codegen_consts.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Identifying constants by name plus normalized type instantantiation schemes.
Convenient data structures for constants.  Auxiliary.
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
  val typ_sort_inst: Sorts.algebra -> typ * sort -> sort Vartab.table -> sort Vartab.table
  val typargs: theory -> string * typ -> typ list
  val find_def: theory -> const -> (string (*theory name*) * thm) option
  val consts_of: theory -> term -> const list
  val read_const: theory -> string -> const
  val string_of_const: theory -> const -> string
  val raw_string_of_const: const -> string
  val string_of_const_typ: theory -> string * typ -> string
  val string_of_typ: theory -> typ -> string
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

fun string_of_typ thy = setmp show_sorts true (Sign.string_of_typ thy);

fun inst_of_typ thy (c_ty as (c, ty)) =
  (c, Sign.const_typargs thy c_ty);

fun typ_of_inst thy (c_tys as (c, tys)) =
  (c, Sign.const_instance thy c_tys);

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
         of SOME thm => SOME (thyname, thm)
          | NONE => NONE
      else NONE
  in
    get_first get_def specs
  end;

fun norm thy (c, insts) =
  let
    fun disciplined class [ty as Type (tyco, _)] =
          let
            val sorts = Sorts.mg_domain (Sign.classes_of thy) tyco [class];
            val vs = Name.invents Name.context "'a" (length sorts);
          in
            (c, [Type (tyco, map (fn v => TVar ((v, 0), [])) vs)])
          end
      | disciplined class _ =
          (c, [TVar (("'a", 0), [class])]);
  in case AxClass.class_of_param thy c
   of SOME class => disciplined class insts
    | NONE => inst_of_typ thy (c, Sign.the_const_type thy c)
  end;

fun norm_of_typ thy (c, ty) =
  norm thy (c, Sign.const_typargs thy (c, ty));

fun consts_of thy t =
  fold_aterms (fn Const c => cons (norm_of_typ thy c) | _ => I) t []

fun typ_sort_inst algebra =
  let
    val inters = Sorts.inter_sort algebra;
    fun match _ [] = I
      | match (TVar (v, S)) S' = Vartab.map_default (v, []) (fn S'' => inters (S, inters (S', S'')))
      | match (Type (a, Ts)) S =
          fold2 match Ts (Sorts.mg_domain algebra a S)
  in uncurry match end;

fun typargs thy (c_ty as (c, ty)) =
  let
    val opt_class = AxClass.class_of_param thy c;
    val tys = Sign.const_typargs thy (c, ty);
  in case (opt_class, tys)
   of (SOME _, [Type (_, tys')]) => tys'
    | _ => tys
  end;


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


(* printing *)

fun string_of_const thy (c, tys) =
  space_implode " " (Sign.extern_const thy c
    :: map (enclose "[" "]" o Sign.string_of_typ thy) tys);

fun raw_string_of_const (c, tys) =
  space_implode " " (c
    :: map (enclose "[" "]" o Display.raw_string_of_typ) tys);

fun string_of_const_typ thy (c, ty) =
  string_of_const thy (c, Consts.typargs (Sign.consts_of thy) (c, ty));

end;
