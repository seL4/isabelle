(*  Title:      HOL/Tools/typecopy.ML
    Author:     Florian Haftmann, TU Muenchen

Introducing copies of types using trivial typedefs; datatype-like abstraction.
*)

signature TYPECOPY =
sig
  type info = { vs: (string * sort) list, constr: string, typ: typ,
    inject: thm, proj: string * typ, proj_def: thm }
  val typecopy: binding * string list -> typ -> (binding * binding) option
    -> theory -> (string * info) * theory
  val get_info: theory -> string -> info option
  val interpretation: (string -> theory -> theory) -> theory -> theory
  val add_default_code: string -> theory -> theory
  val setup: theory -> theory
end;

structure Typecopy: TYPECOPY =
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

val get_info = Symtab.lookup o TypecopyData.get;


(* interpretation of type copies *)

structure TypecopyInterpretation = InterpretationFun(type T = string val eq = op =);
val interpretation = TypecopyInterpretation.interpretation;


(* introducing typecopies *)

fun typecopy (raw_tyco, raw_vs) raw_ty constr_proj thy =
  let
    val ty = Sign.certify_typ thy raw_ty;
    val vs =
      AList.make (the_default HOLogic.typeS o AList.lookup (op =) (Term.add_tfreesT ty [])) raw_vs;
    val tac = Tactic.rtac UNIV_witness 1;
    fun add_info tyco ( { abs_type = ty_abs, rep_type = ty_rep, Abs_name = c_abs,
      Rep_name = c_rep, Abs_inject = inject,
      Abs_inverse = inverse, ... } : Typedef.info ) thy =
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
    |> Typedef.add_typedef false (SOME raw_tyco) (raw_tyco, map fst vs, NoSyn)
      (HOLogic.mk_UNIV ty) (Option.map swap constr_proj) tac
    |-> (fn (tyco, info) => add_info tyco info)
  end;


(* default code setup *)

fun add_default_code tyco thy =
  let
    val SOME { constr = c, proj = (proj, _), proj_def = proj_eq, vs = vs,
      typ = ty_rep, ... } =  get_info thy tyco;
    val SOME { Rep_inject = proj_inject, ... } = Typedef.get_info thy tyco;
    val constr = (c, Logic.unvarifyT (Sign.the_const_type thy c));
    val ty = Type (tyco, map TFree vs);
    val proj = Const (proj, ty --> ty_rep);
    val (t_x, t_y) = (Free ("x", ty), Free ("y", ty));
    val eq_lhs = Const (@{const_name eq_class.eq}, ty --> ty --> HOLogic.boolT)
      $ t_x $ t_y;
    val eq_rhs = HOLogic.mk_eq (proj $ t_x, proj $ t_y);
    val eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq) (eq_lhs, eq_rhs);
    fun tac eq_thm = Class.intro_classes_tac []
      THEN (Simplifier.rewrite_goals_tac
        (map Simpdata.mk_eq [eq_thm, @{thm eq}, proj_inject]))
          THEN ALLGOALS (rtac @{thm refl});
    fun mk_eq_refl thy = @{thm HOL.eq_refl}
      |> Thm.instantiate
         ([pairself (Thm.ctyp_of thy) (TVar (("'a", 0), @{sort eq}), Logic.varifyT ty)], [])
      |> AxClass.unoverload thy;
  in
    thy
    |> Code.add_datatype [constr]
    |> Code.add_eqn proj_eq
    |> TheoryTarget.instantiation ([tyco], vs, [HOLogic.class_eq])
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition
         (NONE, (Attrib.empty_binding, eq)))
    |-> (fn (_, (_, eq_thm)) =>
       Class.prove_instantiation_exit_result Morphism.thm
         (fn _ => fn eq_thm => tac eq_thm) eq_thm)
    |-> (fn eq_thm => Code.add_eqn eq_thm)
    |> (fn thy => Code.add_nbe_eqn (mk_eq_refl thy) thy)
  end;

val setup =
  TypecopyInterpretation.init
  #> interpretation add_default_code

end;
