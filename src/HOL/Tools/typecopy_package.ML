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
  val get_info: theory -> string -> info option
  val interpretation: (string -> theory -> theory) -> theory -> theory
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
    |> TypedefPackage.add_typedef_i false (SOME raw_tyco) (raw_tyco, map fst vs, NoSyn)
      (HOLogic.mk_UNIV ty) (Option.map swap constr_proj) tac
    |-> (fn (tyco, info) => add_info tyco info)
  end;

in

val add_typecopy = gen_add_typecopy Sign.certify_typ;

end;


(* code generator setup *)

fun add_typecopy_spec tyco thy =
  let
    val SOME { constr, proj_def, inject, vs, ... } = get_info thy tyco;
    val vs' = (map o apsnd) (curry (Sorts.inter_sort (Sign.classes_of thy)) [HOLogic.class_eq]) vs;
    val ty = Logic.unvarifyT (Sign.the_const_type thy constr);
    fun add_def tyco lthy =
      let
        val ty = Type (tyco, map TFree vs');
        fun mk_side const_name = Const (const_name, ty --> ty --> HOLogic.boolT)
          $ Free ("x", ty) $ Free ("y", ty);
        val def = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (mk_side @{const_name eq_class.eq}, mk_side @{const_name "op ="}));
        val def' = Syntax.check_term lthy def;
        val ((_, (_, thm)), lthy') = Specification.definition
          (NONE, (Attrib.no_binding, def')) lthy;
        val ctxt_thy = ProofContext.init (ProofContext.theory_of lthy);
        val thm' = singleton (ProofContext.export lthy' ctxt_thy) thm;
      in (thm', lthy') end;
    fun tac thms = Class.intro_classes_tac []
      THEN ALLGOALS (ProofContext.fact_tac thms);
    fun add_eq_thm thy = 
      let
        val eq = inject
          |> Code_Unit.constrain_thm [HOLogic.class_eq]
          |> Simpdata.mk_eq
          |> MetaSimplifier.rewrite_rule [Thm.transfer thy @{thm equals_eq}];
      in Code.add_func eq thy end;
  in
    thy
    |> Code.add_datatype [(constr, ty)]
    |> Code.add_func proj_def
    |> TheoryTarget.instantiation ([tyco], vs', [HOLogic.class_eq])
    |> add_def tyco
    |-> (fn thm => Class.prove_instantiation_instance (K (tac [thm]))
    #> LocalTheory.exit
    #> ProofContext.theory_of
    #> Code.del_func thm
    #> add_eq_thm)
  end;

val setup =
  TypecopyInterpretation.init
  #> interpretation add_typecopy_spec

end;
