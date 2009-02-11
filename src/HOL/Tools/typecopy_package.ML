(*  Title:      HOL/Tools/typecopy_package.ML
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
  val get_info: theory -> string -> info option
  val interpretation: (string -> theory -> theory) -> theory -> theory
  val add_typecopy_default_code: string -> theory -> theory
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
        Syntax.pretty_typ_global thy (Type (tyco, map TFree vs)),
        Pretty.str "=",
        (Pretty.str o Sign.extern_const thy) constr,
        Syntax.pretty_typ_global thy typ,
        Pretty.block [Pretty.str "(", (Pretty.str o Sign.extern_const thy) proj, Pretty.str  ")"]];
    in
      (Pretty.writeln o Pretty.block o Pretty.fbreaks)
        (Pretty.str "type copies:" :: map mk (Symtab.dest tab))
    end;

val get_typecopies = Symtab.keys o TypecopyData.get;
val get_info = Symtab.lookup o TypecopyData.get;


(* interpretation of type copies *)

structure TypecopyInterpretation = InterpretationFun(type T = string val eq = op =);
val interpretation = TypecopyInterpretation.interpretation;

fun add_typecopy (raw_tyco, raw_vs) raw_ty constr_proj thy =
  let
    val ty = Sign.certify_typ thy raw_ty;
    val vs =
      AList.make (the_default HOLogic.typeS o AList.lookup (op =) (Term.add_tfreesT ty [])) raw_vs;
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
    |> TypedefPackage.add_typedef false (SOME raw_tyco) (raw_tyco, map fst vs, NoSyn)
      (HOLogic.mk_UNIV ty) (Option.map swap constr_proj) tac
    |-> (fn (tyco, info) => add_info tyco info)
  end;


(* code generator setup *)

fun add_typecopy_default_code tyco thy =
  let
    val SOME { constr = constr_name, proj = (proj, _), proj_def = proj_eq, vs = raw_vs,
      typ = raw_ty_rep, ... } =  get_info thy tyco;
    val inst_meet = Sorts.meet_sort_typ (Sign.classes_of thy)
      (Logic.varifyT raw_ty_rep, [HOLogic.class_eq]) handle Sorts.CLASS_ERROR _ => I;
    val ty_inst = Logic.unvarifyT o inst_meet o Logic.varifyT;
    val vs = (map dest_TFree o snd o dest_Type o ty_inst)
      (Type (tyco, map TFree raw_vs));
    val ty_rep = ty_inst raw_ty_rep;
    val SOME { Rep_inject = proj_inject, ... } = TypedefPackage.get_info thy tyco;
    val ty_constr = Logic.unvarifyT (Sign.the_const_type thy constr_name);
    val constr = (constr_name, ty_constr)
    val ty = Type (tyco, map TFree vs);
    fun mk_eq ty t_x t_y = Const (@{const_name eq_class.eq}, ty --> ty --> HOLogic.boolT)
      $ t_x $ t_y;
    fun mk_proj t = Const (proj, ty --> ty_rep) $ t;
    val (t_x, t_y) = (Free ("x", ty), Free ("y", ty));
    val def_eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
      (mk_eq ty t_x t_y, HOLogic.mk_eq (mk_proj t_x, mk_proj t_y));
    fun mk_eq_refl thy = @{thm HOL.eq_refl}
      |> Thm.instantiate
         ([pairself (Thm.ctyp_of thy) (TVar (("'a", 0), @{sort eq}), Logic.varifyT ty)], [])
      |> AxClass.unoverload thy;
  in
    thy
    |> Code.add_datatype [constr]
    |> Code.add_eqn proj_eq
    |> TheoryTarget.instantiation ([tyco], vs, [HOLogic.class_eq])
    |> `(fn lthy => Syntax.check_term lthy def_eq)
    |-> (fn def_eq => Specification.definition
         (NONE, (Attrib.empty_binding, def_eq)))
    |-> (fn (_, (_, def_thm)) =>
       Class.prove_instantiation_exit_result Morphism.thm
         (fn _ => fn def_thm => Class.intro_classes_tac []
            THEN (Simplifier.rewrite_goals_tac
              (map Simpdata.mk_eq [def_thm, @{thm eq}, proj_inject]))
                THEN ALLGOALS (rtac @{thm refl})) def_thm)
    |-> (fn def_thm => Code.add_eqn def_thm)
    |> `(fn thy => mk_eq_refl thy)
    |-> (fn refl_thm => Code.add_nonlinear_eqn refl_thm)
  end;

val setup =
  TypecopyInterpretation.init
  #> interpretation add_typecopy_default_code

end;
