(*  Title:      Pure/Tools/codegen_func.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Handling defining equations ("func"s) for code generator framework.
*)

signature CODEGEN_FUNC =
sig
  val check_rew: thm -> thm
  val mk_rew: thm -> thm list
  val check_func: thm -> (CodegenConsts.const * thm) option
  val mk_func: thm -> (CodegenConsts.const * thm) list
  val dest_func: thm -> (string * typ) * term list
  val mk_head: thm -> CodegenConsts.const * thm
  val typ_func: thm -> typ
  val legacy_mk_func: thm -> (CodegenConsts.const * thm) list
  val expand_eta: int -> thm -> thm
  val rewrite_func: thm list -> thm -> thm
  val get_prim_def_funcs: theory -> string * typ list -> thm list
end;

structure CodegenFunc : CODEGEN_FUNC =
struct

fun lift_thm_thy f thm = f (Thm.theory_of_thm thm) thm;

fun bad_thm msg thm =
  error (msg ^ ": " ^ string_of_thm thm);


(* making rewrite theorems *)

fun check_rew thm =
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
    map check_rew thms
  end;


(* making function theorems *)

val typ_func = lift_thm_thy (fn thy => snd o dest_Const o fst o strip_comb
  o fst o Logic.dest_equals o ObjectLogic.drop_judgment thy o Drule.plain_prop_of);

val dest_func = lift_thm_thy (fn thy => apfst dest_Const o strip_comb
  o fst o Logic.dest_equals o ObjectLogic.drop_judgment thy o Drule.plain_prop_of
  o Drule.fconv_rule Drule.beta_eta_conversion);

val mk_head = lift_thm_thy (fn thy => fn thm =>
  ((CodegenConsts.norm_of_typ thy o fst o dest_func) thm, thm));

fun gen_check_func strict_functyp thm = case try dest_func thm
 of SOME (c_ty as (c, ty), args) =>
      let
        val thy = Thm.theory_of_thm thm;
        val _ =
          if has_duplicates (op =)
            ((fold o fold_aterms) (fn Var (v, _) => cons v
              | _ => I
            ) args [])
          then bad_thm "Repeated variables on left hand side of function equation" thm
          else ()
        fun no_abs (Abs _) = bad_thm "Abstraction on left hand side of function equation" thm 
          | no_abs (t1 $ t2) = (no_abs t1; no_abs t2)
          | no_abs _ = ();
        val _ = map no_abs args;
        val is_classop = (is_some o AxClass.class_of_param thy) c;
        val const = CodegenConsts.norm_of_typ thy c_ty;
        val ty_decl = CodegenConsts.disc_typ_of_const thy
          (snd o CodegenConsts.typ_of_inst thy) const;
        val string_of_typ = setmp show_sorts true (Sign.string_of_typ thy);
        val error_warning = if strict_functyp
          then error
          else warning #> K NONE
      in if Sign.typ_equiv thy (ty_decl, ty)
        then SOME (const, thm)
        else (if is_classop
            then error_warning
          else if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
            then warning #> (K o SOME) (const, thm)
          else error_warning)
          ("Type\n" ^ string_of_typ ty
           ^ "\nof function theorem\n"
           ^ string_of_thm thm
           ^ "\nis strictly less general than declared function type\n"
           ^ string_of_typ ty_decl)
      end
  | NONE => bad_thm "Not a function equation" thm;

val check_func = gen_check_func true;
val legacy_check_func = gen_check_func false;

fun gen_mk_func check_func = map_filter check_func o mk_rew;
val mk_func = gen_mk_func check_func;
val legacy_mk_func = gen_mk_func legacy_check_func;


(* utilities *)

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

fun get_prim_def_funcs thy c =
  let
    fun constrain thm0 thm = case AxClass.class_of_param thy (fst c)
     of SOME _ =>
          let
            val ty_decl = CodegenConsts.disc_typ_of_classop thy c;
            val max = maxidx_of_typ ty_decl + 1;
            val thm = Thm.incr_indexes max thm;
            val ty = typ_func thm;
            val (env, _) = Sign.typ_unify thy (ty_decl, ty) (Vartab.empty, max);
            val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
              cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
          in Thm.instantiate (instT, []) thm end
      | NONE => thm
  in case CodegenConsts.find_def thy c
   of SOME ((_, thm), _) =>
        thm
        |> Thm.transfer thy
        |> try (map snd o mk_func)
        |> these
        |> map (constrain thm)
        |> map (expand_eta ~1)
    | NONE => []
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
  in
    Thm.transitive (Thm.transitive lhs' thm) rhs'
  end handle Bind => raise ERROR "rewrite_func"

end;
