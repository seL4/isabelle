(*  Title:      HOL/Tools/code_evaluation.ML
    Author:     Florian Haftmann, TU Muenchen

Evaluation and reconstruction of terms in ML.
*)

signature CODE_EVALUATION =
sig
  val dynamic_value: theory -> term -> term option
  val dynamic_value_strict: theory -> term -> term
  val dynamic_value_exn: theory -> term -> term Exn.result
  val static_value: theory -> string list -> typ list -> term -> term option
  val static_value_strict: theory -> string list -> typ list -> term -> term
  val static_value_exn: theory -> string list -> typ list -> term -> term Exn.result
  val dynamic_conv: theory -> conv
  val static_conv: theory -> string list -> typ list -> conv
  val put_term: (unit -> term) -> Proof.context -> Proof.context
  val tracing: string -> 'a -> 'a
  val setup: theory -> theory
end;

structure Code_Evaluation : CODE_EVALUATION =
struct

(** term_of instances **)

(* formal definition *)

fun add_term_of tyco raw_vs thy =
  let
    val vs = map (fn (v, _) => (v, @{sort typerep})) raw_vs;
    val ty = Type (tyco, map TFree vs);
    val lhs = Const (@{const_name term_of}, ty --> @{typ term})
      $ Free ("x", ty);
    val rhs = @{term "undefined :: term"};
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
    fun triv_name_of t = (fst o dest_Free o fst o strip_comb o fst
      o HOLogic.dest_eq o HOLogic.dest_Trueprop) t ^ "_triv";
  in
    thy
    |> Class.instantiation ([tyco], vs, @{sort term_of})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, ((Binding.name (triv_name_of eq), []), eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_term_of (tyco, (raw_vs, _)) thy =
  let
    val need_inst = not (can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of})
      andalso can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort typerep};
  in if need_inst then add_term_of tyco raw_vs thy else thy end;


(* code equations for datatypes *)

fun mk_term_of_eq thy ty (c, (_, tys)) =
  let
    val t = list_comb (Const (c, tys ---> ty),
      map Free (Name.invent_names Name.context "a" tys));
    val (arg, rhs) =
      pairself (Thm.cterm_of thy o Logic.unvarify_types_global o Logic.varify_global)
        (t,
          map_aterms (fn t as Free (_, ty) => HOLogic.mk_term_of ty t | t => t)
            (HOLogic.reflect_term t));
    val cty = Thm.ctyp_of thy ty;
  in
    @{thm term_of_anything}
    |> Drule.instantiate' [SOME cty] [SOME arg, SOME rhs]
    |> Thm.varifyT_global
  end;

fun add_term_of_code tyco raw_vs raw_cs thy =
  let
    val algebra = Sign.classes_of thy;
    val vs = map (fn (v, sort) =>
      (v, curry (Sorts.inter_sort algebra) @{sort typerep} sort)) raw_vs;
    val ty = Type (tyco, map TFree vs);
    val cs = (map o apsnd o apsnd o map o map_atyps)
      (fn TFree (v, _) => TFree (v, (the o AList.lookup (op =) vs) v)) raw_cs;
    val const = AxClass.param_of_inst thy (@{const_name term_of}, tyco);
    val eqs = map (mk_term_of_eq thy ty) cs;
 in
    thy
    |> Code.del_eqns const
    |> fold Code.add_eqn eqs
  end;

fun ensure_term_of_code (tyco, (raw_vs, cs)) thy =
  let
    val has_inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of};
  in if has_inst then add_term_of_code tyco raw_vs cs thy else thy end;


(* code equations for abstypes *)

fun mk_abs_term_of_eq thy ty abs ty_rep proj =
  let
    val arg = Var (("x", 0), ty);
    val rhs = Abs ("y", @{typ term}, HOLogic.reflect_term (Const (abs, ty_rep --> ty) $ Bound 0)) $
      (HOLogic.mk_term_of ty_rep (Const (proj, ty --> ty_rep) $ arg))
      |> Thm.cterm_of thy;
    val cty = Thm.ctyp_of thy ty;
  in
    @{thm term_of_anything}
    |> Drule.instantiate' [SOME cty] [SOME (Thm.cterm_of thy arg), SOME rhs]
    |> Thm.varifyT_global
  end;

fun add_abs_term_of_code tyco raw_vs abs raw_ty_rep proj thy =
  let
    val algebra = Sign.classes_of thy;
    val vs = map (fn (v, sort) =>
      (v, curry (Sorts.inter_sort algebra) @{sort typerep} sort)) raw_vs;
    val ty = Type (tyco, map TFree vs);
    val ty_rep = map_atyps
      (fn TFree (v, _) => TFree (v, (the o AList.lookup (op =) vs) v)) raw_ty_rep;
    val const = AxClass.param_of_inst thy (@{const_name term_of}, tyco);
    val eq = mk_abs_term_of_eq thy ty abs ty_rep proj;
 in
    thy
    |> Code.del_eqns const
    |> Code.add_eqn eq
  end;

fun ensure_abs_term_of_code (tyco, (raw_vs, ((abs, (_, ty)), (proj, _)))) thy =
  let
    val has_inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of};
  in if has_inst then add_abs_term_of_code tyco raw_vs abs ty proj thy else thy end;


(** termifying syntax **)

fun map_default f xs =
  let val ys = map f xs
  in if exists is_some ys
    then SOME (map2 the_default xs ys)
    else NONE
  end;

fun subst_termify_app (Const (@{const_name termify}, _), [t]) =
      if not (Term.has_abs t)
      then if fold_aterms (fn Const _ => I | _ => K false) t true
        then SOME (HOLogic.reflect_term t)
        else error "Cannot termify expression containing variables"
      else error "Cannot termify expression containing abstraction"
  | subst_termify_app (t, ts) = case map_default subst_termify ts
     of SOME ts' => SOME (list_comb (t, ts'))
      | NONE => NONE
and subst_termify (Abs (v, T, t)) = (case subst_termify t
     of SOME t' => SOME (Abs (v, T, t'))
      | NONE => NONE)
  | subst_termify t = subst_termify_app (strip_comb t) 

fun check_termify ctxt ts =
  the_default ts (map_default subst_termify ts);


(** evaluation **)

structure Evaluation = Proof_Data
(
  type T = unit -> term
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Evaluation"
);
val put_term = Evaluation.put;
val cookie = (Evaluation.get, put_term, "Code_Evaluation.put_term");

fun mk_term_of t = HOLogic.mk_term_of (fastype_of t) t;

fun term_of_const_for thy = AxClass.unoverload_const thy o dest_Const o HOLogic.term_of_const;

fun gen_dynamic_value dynamic_value thy t =
  dynamic_value cookie thy NONE I (mk_term_of t) [];

val dynamic_value = gen_dynamic_value Code_Runtime.dynamic_value;
val dynamic_value_strict = gen_dynamic_value Code_Runtime.dynamic_value_strict;
val dynamic_value_exn = gen_dynamic_value Code_Runtime.dynamic_value_exn;

fun gen_static_value static_value thy consts Ts =
  static_value cookie thy NONE I (union (op =) (map (term_of_const_for thy) Ts) consts)
  o mk_term_of;

val static_value = gen_static_value Code_Runtime.static_value;
val static_value_strict = gen_static_value Code_Runtime.static_value_strict;
val static_value_exn = gen_static_value Code_Runtime.static_value_exn;

fun certify_eval thy value conv ct =
  let
    val t = Thm.term_of ct;
    val T = fastype_of t;
    val mk_eq = Thm.mk_binop (Thm.cterm_of thy (Const ("==", T --> T --> propT)));
  in case value t
   of NONE => Thm.reflexive ct
    | SOME t' => conv (mk_eq ct (Thm.cterm_of thy t')) RS @{thm eq_eq_TrueD}
        handle THM _ =>
          error ("Failed to certify evaluation result of " ^ Syntax.string_of_term_global thy t)
  end;

fun dynamic_conv thy = certify_eval thy (dynamic_value thy)
  (Code_Runtime.dynamic_holds_conv thy);

fun static_conv thy consts Ts =
  let
    val eqs = "==" :: @{const_name HOL.eq} ::
      map (fn T => AxClass.unoverload_const thy (@{const_name HOL.equal}, T)) Ts;
        (*assumes particular code equations for "==" etc.*)
  in
    certify_eval thy (static_value thy consts Ts)
      (Code_Runtime.static_holds_conv thy (union (op =) eqs consts))
  end;


(** diagnostic **)

fun tracing s x = (Output.tracing s; x);


(** setup **)

val setup =
  Code.datatype_interpretation ensure_term_of
  #> Code.abstype_interpretation ensure_term_of
  #> Code.datatype_interpretation ensure_term_of_code
  #> Code.abstype_interpretation ensure_abs_term_of_code
  #> Context.theory_map (Syntax_Phases.term_check 0 "termify" check_termify)
  #> Value.add_evaluator ("code", dynamic_value_strict o Proof_Context.theory_of);

end;
