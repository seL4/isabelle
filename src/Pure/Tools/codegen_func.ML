(*  Title:      Pure/Tools/codegen_func.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Basic handling of defining equations ("func"s) for code generator framework.
*)

signature CODEGEN_FUNC =
sig
  val assert_rew: thm -> thm
  val mk_rew: thm -> thm
  val mk_func: thm -> thm
  val head_func: thm -> CodegenConsts.const * typ
  val bad_thm: string -> 'a
  val error_thm: (thm -> thm) -> thm -> thm
  val warning_thm: (thm -> thm) -> thm -> thm option

  val inst_thm: sort Vartab.table -> thm -> thm
  val expand_eta: int -> thm -> thm
  val rewrite_func: thm list -> thm -> thm
  val norm_args: thm list -> thm list 
  val norm_varnames: (string -> string) -> (string -> string) -> thm list -> thm list 
end;

structure CodegenFunc : CODEGEN_FUNC =
struct


(* auxiliary *)

exception BAD_THM of string;
fun bad_thm msg = raise BAD_THM msg;
fun error_thm f thm = f thm handle BAD_THM msg => error msg;
fun warning_thm f thm = SOME (f thm) handle BAD_THM msg
  => (warning msg; NONE);


(* making rewrite theorems *)

fun assert_rew thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (lhs, rhs) = (Logic.dest_equals o Thm.prop_of) thm
      handle TERM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm);
    fun vars_of t = fold_aterms
     (fn Var (v, _) => insert (op =) v
       | Free _ => bad_thm ("Illegal free variable in rewrite theorem\n"
           ^ Display.string_of_thm thm)
       | _ => I) t [];
    fun tvars_of t = fold_term_types
     (fn _ => fold_atyps (fn TVar (v, _) => insert (op =) v
                          | TFree _ => bad_thm 
      ("Illegal free type variable in rewrite theorem\n" ^ Display.string_of_thm thm))) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of lhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm ("Free variables on right hand side of rewrite theorem\n"
        ^ Display.string_of_thm thm);
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm ("Free type variables on right hand side of rewrite theorem\n"
        ^ Display.string_of_thm thm)
  in thm end;

fun mk_rew thm =
  let
    val thy = Thm.theory_of_thm thm;
    val ctxt = ProofContext.init thy;
  in
    thm
    |> LocalDefs.meta_rewrite_rule ctxt
    |> assert_rew
  end;


(* making defining equations *)

fun assert_func thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (head, args) = (strip_comb o fst o Logic.dest_equals
      o ObjectLogic.drop_judgment thy o Thm.plain_prop_of) thm;
    val _ = case head of Const _ => () | _ =>
      bad_thm ("Equation not headed by constant\n" ^ Display.string_of_thm thm);
    val _ =
      if has_duplicates (op =)
        ((fold o fold_aterms) (fn Var (v, _) => cons v
          | _ => I
        ) args [])
      then bad_thm ("Duplicated variables on left hand side of equation\n"
        ^ Display.string_of_thm thm)
      else ()
    fun check _ (Abs _) = bad_thm
          ("Abstraction on left hand side of equation\n"
            ^ Display.string_of_thm thm)
      | check 0 (Var _) = ()
      | check _ (Var _) = bad_thm
          ("Variable with application on left hand side of defining equation\n"
            ^ Display.string_of_thm thm)
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (_, ty)) = if n <> (length o fst o strip_type) ty
          then bad_thm
            ("Partially applied constant on left hand side of equation\n"
               ^ Display.string_of_thm thm)
          else ();
    val _ = map (check 0) args;
  in thm end;

val mk_func = assert_func o (*Conv.fconv_rule Drule.beta_eta_conversion o *)mk_rew;

fun head_func thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (Const (c_ty as (_, ty))) = (fst o strip_comb o fst o Logic.dest_equals
      o ObjectLogic.drop_judgment thy o Thm.plain_prop_of) thm;
    val const = CodegenConsts.const_of_cexpr thy c_ty;
  in (const, ty) end;


(* utilities *)

fun inst_thm tvars' thm =
  let
    val thy = Thm.theory_of_thm thm;
    val tvars = (Term.add_tvars o Thm.prop_of) thm [];
    fun mk_inst (tvar as (v, _)) = case Vartab.lookup tvars' v
     of SOME sort => SOME (pairself (Thm.ctyp_of thy o TVar) (tvar, (v, sort)))
      | NONE => NONE;
    val insts = map_filter mk_inst tvars;
  in Thm.instantiate (insts, []) thm end;

fun expand_eta k thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm;
    val (head, args) = strip_comb lhs;
    val l = if k = ~1
      then (length o fst o strip_abs) rhs
      else Int.max (0, k - length args);
    val used = Name.make_context (map (fst o fst) (Term.add_vars lhs []));
    fun get_name _ 0 used = ([], used)
      | get_name (Abs (v, ty, t)) k used =
          used
          |> Name.variants [v]
          ||>> get_name t (k - 1)
          |>> (fn ([v'], vs') => (v', ty) :: vs')
      | get_name t k used = 
          let
            val (tys, _) = (strip_type o fastype_of) t
          in case tys
           of [] => raise TERM ("expand_eta", [t])
            | ty :: _ =>
                used
                |> Name.variants [""]
                |-> (fn [v] => get_name (t $ Var ((v, 0), ty)) (k - 1)
                #>> (fn vs' => (v, ty) :: vs'))
          end;
    val (vs, _) = get_name rhs l used;
    val vs_refl = map (fn (v, ty) => Thm.reflexive (Thm.cterm_of thy (Var ((v, 0), ty)))) vs;
  in
    fold (fn refl => fn thm => Thm.combination thm refl) vs_refl thm
  end;

fun rewrite_func rewrites thm =
  let
    val rewrite = MetaSimplifier.rewrite false rewrites;
    val (ct_eq, [ct_lhs, ct_rhs]) = (Drule.strip_comb o Thm.cprop_of) thm;
    val Const ("==", _) = Thm.term_of ct_eq;
    val (ct_f, ct_args) = Drule.strip_comb ct_lhs;
    val rhs' = rewrite ct_rhs;
    val args' = map rewrite ct_args;
    val lhs' = Thm.symmetric (fold (fn th1 => fn th2 => Thm.combination th2 th1)
      args' (Thm.reflexive ct_f));
  in Thm.transitive (Thm.transitive lhs' thm) rhs' end;

fun norm_args thms =
  let
    val num_args_of = length o snd o strip_comb o fst o Logic.dest_equals;
    val k = fold (curry Int.max o num_args_of o Thm.plain_prop_of) thms 0;
  in
    thms
    |> map (expand_eta k)
    |> map (Conv.fconv_rule Drule.beta_eta_conversion)
  end;

fun canonical_tvars purify_tvar thm =
  let
    val ctyp = Thm.ctyp_of (Thm.theory_of_thm thm);
    fun tvars_subst_for thm = (fold_types o fold_atyps)
      (fn TVar (v_i as (v, _), sort) => let
            val v' = purify_tvar v
          in if v = v' then I
          else insert (op =) (v_i, (v', sort)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i, (v', sort)) (maxidx, acc) =
      let
        val ty = TVar (v_i, sort)
      in
        (maxidx + 1, (ctyp ty, ctyp (TVar ((v', maxidx), sort))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (tvars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars purify_var thm =
  let
    val cterm = Thm.cterm_of (Thm.theory_of_thm thm);
    fun vars_subst_for thm = fold_aterms
      (fn Var (v_i as (v, _), ty) => let
            val v' = purify_var v
          in if v = v' then I
          else insert (op =) (v_i, (v', ty)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i as (v, i), (v', ty)) (maxidx, acc) =
      let
        val t = Var (v_i, ty)
      in
        (maxidx + 1, (cterm t, cterm (Var ((v', maxidx), ty))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (vars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate ([], inst) thm end;

fun canonical_absvars purify_var thm =
  let
    val t = Thm.prop_of thm;
    val t' = Term.map_abs_vars purify_var t;
  in Thm.rename_boundvars t t' thm end;

fun norm_varnames purify_tvar purify_var thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_list
          |> f
          |> Conjunction.elim_list;
  in
    thms
    |> burrow_thms (canonical_tvars purify_tvar)
    |> map (canonical_vars purify_var)
    |> map (canonical_absvars purify_var)
    |> map Drule.zero_var_indexes
  end;

end;
