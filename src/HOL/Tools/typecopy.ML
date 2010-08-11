(*  Title:      HOL/Tools/typecopy.ML
    Author:     Florian Haftmann, TU Muenchen

Introducing copies of types using trivial typedefs; datatype-like abstraction.
*)

signature TYPECOPY =
sig
  type info = { vs: (string * sort) list, typ: typ, constr: string, proj: string,
    constr_inject: thm, proj_inject: thm, constr_proj: thm, proj_constr: thm }
  val typecopy: binding * (string * sort) list -> typ -> binding -> binding
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
  typ: typ,
  constr: string,
  proj: string,
  constr_inject: thm,
  proj_inject: thm,
  constr_proj: thm,
  proj_constr: thm
};

structure Typecopy_Data = Theory_Data
(
  type T = info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

val get_info = Symtab.lookup o Typecopy_Data.get;


(* interpretation of type copies *)

structure Typecopy_Interpretation = Interpretation(type T = string val eq = op =);
val interpretation = Typecopy_Interpretation.interpretation;


(* introducing typecopies *)

fun add_info tyco vs (({ rep_type, Abs_name, Rep_name, ...},
    { Abs_inject, Rep_inject, Abs_inverse, Rep_inverse, ... }) : Typedef.info) thy =
  let
    val exists_thm =
      UNIV_I
      |> Drule.instantiate' [SOME (ctyp_of thy (Logic.varifyT_global rep_type))] [];
    val constr_inject = Abs_inject OF [exists_thm, exists_thm];
    val proj_constr = Abs_inverse OF [exists_thm];
    val info = {
      vs = vs,
      typ = rep_type,
      constr = Abs_name,
      proj = Rep_name,
      constr_inject = constr_inject,
      proj_inject = Rep_inject,
      constr_proj = Rep_inverse,
      proj_constr = proj_constr
    };
  in
    thy
    |> (Typecopy_Data.map o Symtab.update_new) (tyco, info)
    |> Typecopy_Interpretation.data tyco
    |> pair (tyco, info)
  end

fun typecopy (raw_tyco, raw_vs) raw_ty constr proj thy =
  let
    val ty = Sign.certify_typ thy raw_ty;
    val ctxt = ProofContext.init_global thy |> Variable.declare_typ ty;
    val vs = map (ProofContext.check_tfree ctxt) raw_vs;
    val tac = Tactic.rtac UNIV_witness 1;
  in
    thy
    |> Typedef.add_typedef_global false (SOME raw_tyco) (raw_tyco, vs, NoSyn)
      (HOLogic.mk_UNIV ty) (SOME (proj, constr)) tac
    |-> (fn (tyco, info) => add_info tyco vs info)
  end;


(* default code setup *)

fun add_default_code tyco thy =
  let
    val SOME { vs, typ = ty_rep, constr = c, proj, proj_constr, proj_inject, ... } =
      get_info thy tyco;
    val constr = (c, Logic.unvarifyT_global (Sign.the_const_type thy c));
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
         ([pairself (Thm.ctyp_of thy) (TVar (("'a", 0), @{sort eq}), Logic.varifyT_global ty)], [])
      |> AxClass.unoverload thy;
  in
    thy
    |> Code.add_datatype [constr]
    |> Code.add_eqn proj_constr
    |> Class.instantiation ([tyco], vs, [HOLogic.class_eq])
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
  Typecopy_Interpretation.init
  #> interpretation add_default_code

end;
