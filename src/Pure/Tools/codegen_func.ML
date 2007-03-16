(*  Title:      Pure/Tools/codegen_func.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Basic handling of defining equations ("func"s) for code generator framework.
*)

signature CODEGEN_FUNC =
sig
  val assert_rew: thm -> thm
  val mk_rew: thm -> thm list
  val assert_func: thm -> thm
  val mk_func: thm -> (CodegenConsts.const * thm) list
  val mk_head: thm -> CodegenConsts.const * thm
  val dest_func: thm -> (string * typ) * term list
  val typ_func: thm -> typ

  val inst_thm: sort Vartab.table -> thm -> thm
  val expand_eta: int -> thm -> thm
  val rewrite_func: thm list -> thm -> thm
  val norm_args: thm list -> thm list 
  val norm_varnames: (string -> string) -> (string -> string) -> thm list -> thm list 
end;

structure CodegenFunc : CODEGEN_FUNC =
struct

fun lift_thm_thy f thm = f (Thm.theory_of_thm thm) thm;

fun bad_thm msg thm =
  error (msg ^ ": " ^ string_of_thm thm);


(* making rewrite theorems *)

fun assert_rew thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (lhs, rhs) = (Logic.dest_equals o Thm.prop_of) thm;
    fun vars_of t = fold_aterms
     (fn Var (v, _) => insert (op =) v
       | Free _ => bad_thm "Illegal free variable in rewrite theorem" thm
       | _ => I) t [];
    fun tvars_of t = fold_term_types
     (fn _ => fold_atyps (fn TVar (v, _) => insert (op =) v
                          | TFree _ => bad_thm "Illegal free type variable in rewrite theorem" thm)) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of lhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm "Free variables on right hand side of rewrite theorems" thm
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm "Free type variables on right hand side of rewrite theorems" thm
  in thm end;

fun mk_rew thm =
  let
    val thy = Thm.theory_of_thm thm;
    val thms = (#mk o #mk_rews o snd o MetaSimplifier.rep_ss o Simplifier.simpset_of) thy thm;
  in
    map assert_rew thms
  end;


(* making defining equations *)

val typ_func = lift_thm_thy (fn thy => snd o dest_Const o fst o strip_comb
  o fst o Logic.dest_equals o ObjectLogic.drop_judgment thy o Drule.plain_prop_of);

val dest_func = lift_thm_thy (fn thy => apfst dest_Const o strip_comb
  o fst o Logic.dest_equals o ObjectLogic.drop_judgment thy o Drule.plain_prop_of
  o Drule.fconv_rule Drule.beta_eta_conversion);

val mk_head = lift_thm_thy (fn thy => fn thm =>
  ((CodegenConsts.norm_of_typ thy o fst o dest_func) thm, thm));

fun assert_func thm = case try dest_func thm
 of SOME (c_ty as (c, ty), args) =>
      let
        val thy = Thm.theory_of_thm thm;
        val _ =
          if has_duplicates (op =)
            ((fold o fold_aterms) (fn Var (v, _) => cons v
              | _ => I
            ) args [])
          then bad_thm "Repeated variables on left hand side of defining equation" thm
          else ()
        fun check _ (Abs _) = bad_thm
              "Abstraction on left hand side of defining equation" thm
          | check false (Var _) = bad_thm
              "Variable with application on left hand side of defining equation" thm
          | check _ (t1 $ t2) = (check false t1; check true t2)
          | check _ _ = ();
        val _ = map (check true) args;
      in thm end
  | NONE => bad_thm "Not a defining equation" thm;

val mk_func = map (mk_head o assert_func) o mk_rew;


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
    val (lhs, rhs) = (Logic.dest_equals o Drule.plain_prop_of) thm;
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
    val k = fold (curry Int.max o num_args_of o Drule.plain_prop_of) thms 0;
  in
    thms
    |> map (expand_eta k)
    |> map (Drule.fconv_rule Drule.beta_eta_conversion)
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
