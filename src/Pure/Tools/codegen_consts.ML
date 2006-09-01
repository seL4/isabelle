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
  val find_def: theory -> const
    -> ((string (*theory name*) * string (*definition name*)) * typ list) option
  val sortinsts: theory -> typ * typ -> (typ * sort) list
  val norminst_of_typ: theory -> string * typ -> const
  val class_of_classop: theory -> const -> class option
  val insts_of_classop: theory -> const -> const list
  val typ_of_classop: theory -> const -> typ
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
  (c, Consts.typargs (Sign.consts_of thy) c_ty);

fun typ_of_typinst thy (c_tys as (c, tys)) =
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
      | NONE =>  Sign.typ_instance thy
  in
    get_first (fn (_, { is_def, thyname, name, lhs, ... }) => if is_def
      andalso forall typ_instance (tys ~~ lhs)
      then SOME ((thyname, name), lhs) else NONE) specs
  end;

fun sortinsts thy (ty, ty_decl) =
  Vartab.empty
  |> Sign.typ_match thy (ty_decl, ty) 
  |> Vartab.dest
  |> map (fn (_, (sort, ty)) => (ty, sort));

fun mk_classop_typinst thy (c, tyco) =
  (c, [Type (tyco, map (fn v => TVar ((v, 0), Sign.defaultS thy (*for monotonicity*)))
    (Name.invents Name.context "'a" (Sign.arity_number thy tyco)))]);

fun norminst_of_typ thy (c, ty) =
  let
    fun disciplined _ [(Type (tyco, _))] =
          mk_classop_typinst thy (c, tyco)
      | disciplined sort _ =
          (c, [TVar (("'a", 0), sort)]);
    fun ad_hoc c tys =
      case find_def thy (c, tys)
       of SOME (_, tys) => (c, tys)
        | NONE => typinst_of_typ thy (c, Sign.the_const_type thy c);
    val tyinsts = Consts.typargs (Sign.consts_of thy) (c, ty);
  in if c = "op =" then disciplined (Sign.defaultS thy) tyinsts
    (*the distinction on op = will finally disappear!*)
    else case AxClass.class_of_param thy c
     of SOME class => disciplined [class] tyinsts
      | _ => ad_hoc c tyinsts
  end;

fun class_of_classop thy (c, [TVar _]) = 
      AxClass.class_of_param thy c
  | class_of_classop thy (c, [TFree _]) = 
      AxClass.class_of_param thy c
  | class_of_classop thy (c, _) = NONE;

fun insts_of_classop thy (c_tys as (c, tys)) =
  (*get rid of this finally*)
  case AxClass.class_of_param thy c
   of NONE => [c_tys]
    | SOME class => let
        val cs = maps (AxClass.params_of thy)
          (Graph.all_succs ((#classes o Sorts.rep_algebra o Sign.classes_of) thy) [class])
        fun add_tyco (tyco, classes) =
          if member (op = o apsnd fst) classes class
          then cons tyco else I;
        val tycos =
          Symtab.fold add_tyco
            ((#arities o Sorts.rep_algebra o Sign.classes_of) thy) [];
      in maps (fn c => map (fn tyco => mk_classop_typinst thy (c, tyco)) tycos) cs end;

fun typ_of_classop thy (c, [TVar _]) = 
      let
        val class = (the o AxClass.class_of_param thy) c;
        val (v, cs) = ClassPackage.the_consts_sign thy class
      in
        (Logic.varifyT o map_type_tfree (fn u as (w, _) => if w = v then TFree (v, [class]) else TFree u))
          ((the o AList.lookup (op =) cs) c)
      end
  | typ_of_classop thy (c, [TFree _]) = 
      let
        val class = (the o AxClass.class_of_param thy) c;
        val (v, cs) = ClassPackage.the_consts_sign thy class
      in
        (Logic.varifyT o map_type_tfree (fn u as (w, _) => if w = v then TFree (v, [class]) else TFree u))
          ((the o AList.lookup (op =) cs) c)
      end
  | typ_of_classop thy (c, [Type (tyco, _)]) =
      let
        val class = (the o AxClass.class_of_param thy) c;
        val (_, cs) = ClassPackage.the_inst_sign thy (class, tyco);
      in
        Logic.varifyT ((the o AList.lookup (op =) cs) c)
      end;


(* reading constants as terms *)

fun read_const_typ thy raw_t =
  let
    val t = Sign.read_term thy raw_t
  in case try dest_Const t
   of SOME c_ty => c_ty
    | NONE => error ("Not a constant: " ^ Sign.string_of_term thy t)
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
