(*  Title:      HOL/Nominal/nominal_fresh_fun.ML
    Authors:    Stefan Berghofer and Julien Narboux, TU Muenchen

Provides a tactic to generate fresh names and
a tactic to analyse instances of the fresh_fun.
*)

(* FIXME proper ML structure! *)

(* FIXME res_inst_tac mostly obsolete, cf. Subgoal.FOCUS *)

(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)
fun gen_res_inst_tac_term ctxt instf tyinst tinst elim th i st =
  let
    val cgoal = nth (cprems_of st) (i - 1);
    val maxidx = Thm.maxidx_of_cterm cgoal;
    val j = maxidx + 1;
    val tyinst' = map (apfst (Logic.incr_tvar j)) tyinst;
    val ps = Logic.strip_params (Thm.term_of cgoal);
    val Ts = map snd ps;
    val tinst' = map (fn (t, u) =>
      (head_of (Logic.incr_indexes ([], Ts, j) t),
       fold_rev Term.abs ps u)) tinst;
    val th' = instf
      (map (apsnd (Thm.ctyp_of ctxt)) tyinst')
      (map (apsnd (Thm.cterm_of ctxt)) tinst')
      (Thm.lift_rule cgoal th)
  in
    compose_tac ctxt (elim, th', Thm.nprems_of th) i st
  end handle General.Subscript => Seq.empty;
(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)

fun res_inst_tac_term ctxt =
  gen_res_inst_tac_term ctxt (fn instT => fn inst =>
    Thm.instantiate
     (TVars.make (map (apfst dest_TVar) instT),
      Vars.make (map (apfst dest_Var) inst)));

fun res_inst_tac_term' ctxt =
  gen_res_inst_tac_term ctxt
    (fn _ => fn inst => infer_instantiate ctxt (map (apfst (#1 o dest_Var)) inst)) [];

fun cut_inst_tac_term' ctxt tinst th =
  res_inst_tac_term' ctxt tinst false (Rule_Insts.make_elim_preserve ctxt th);

fun get_dyn_thm thy name atom_name =
  Global_Theory.get_thm thy name handle ERROR _ =>
    error ("The atom type "^atom_name^" is not defined.");

(* The theorems needed that are known at compile time. *)
val at_exists_fresh' = @{thm "at_exists_fresh'"};
val fresh_fun_app'   = @{thm "fresh_fun_app'"};
val fresh_prod       = @{thm "fresh_prod"};

(* A tactic to generate a name fresh for  all the free *)
(* variables and parameters of the goal                *)

fun generate_fresh_tac ctxt atom_name = SUBGOAL (fn (goal, _) =>
 let
   val thy = Proof_Context.theory_of ctxt;
(* the parsing function returns a qualified name, we get back the base name *)
   val atom_basename = Long_Name.base_name atom_name;
   val ps = Logic.strip_params goal;
   val Ts = rev (map snd ps);
   fun is_of_fs_name T = Sign.of_sort thy (T, [Sign.intern_class thy ("fs_"^atom_basename)]);
(* rebuild de bruijn indices *)
   val bvs = map_index (Bound o fst) ps;
(* select variables of the right class *)
   val vs = filter (fn t => is_of_fs_name (fastype_of1 (Ts, t)))
     (Misc_Legacy.term_frees goal @ bvs);
(* build the tuple *)
   val s = (Library.foldr1 (fn (v, s) =>
       HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s) vs)
     handle TERM _ => HOLogic.unit;
   val fs_name_thm = get_dyn_thm thy ("fs_"^atom_basename^"1") atom_basename;
   val at_name_inst_thm = get_dyn_thm thy ("at_"^atom_basename^"_inst") atom_basename;
   val exists_fresh' = at_name_inst_thm RS at_exists_fresh';
(* find the variable we want to instantiate *)
   val x = hd (Misc_Legacy.term_vars (Thm.prop_of exists_fresh'));
 in
   fn st =>
   (cut_inst_tac_term' ctxt [(x,s)] exists_fresh' 1 THEN
   resolve_tac ctxt [fs_name_thm] 1 THEN
   eresolve_tac ctxt [exE] 1) st
  handle List.Empty  => all_tac st (* if we collected no variables then we do nothing *)
 end) 1;

fun get_inner_fresh_fun (Bound j) = NONE
  | get_inner_fresh_fun (v as Free _) = NONE
  | get_inner_fresh_fun (v as Var _)  = NONE
  | get_inner_fresh_fun (Const _) = NONE
  | get_inner_fresh_fun (Abs (_, _, t)) = get_inner_fresh_fun t
  | get_inner_fresh_fun (Const (\<^const_name>\<open>Nominal.fresh_fun\<close>,
      Type(\<^type_name>\<open>fun\<close>,[Type (\<^type_name>\<open>fun\<close>,[Type (T,_),_]),_])) $ u) = SOME T
  | get_inner_fresh_fun (t $ u) =
     let val a = get_inner_fresh_fun u in
     if a = NONE then get_inner_fresh_fun t else a
     end;

(* This tactic generates a fresh name of the atom type *)
(* given by the innermost fresh_fun                    *)

fun generate_fresh_fun_tac ctxt = SUBGOAL (fn (goal, _) =>
  let
    val atom_name_opt = get_inner_fresh_fun goal;
  in
  case atom_name_opt of
    NONE => all_tac
  | SOME atom_name  => generate_fresh_tac ctxt atom_name
  end) 1;

(* Two substitution tactics which looks for the innermost occurrence in
   one assumption or in the conclusion *)

val search_fun = curry (Seq.flat o uncurry EqSubst.searchf_bt_unify_valid);
val search_fun_asm = EqSubst.skip_first_asm_occs_search EqSubst.searchf_bt_unify_valid;

fun subst_inner_tac ctxt = EqSubst.eqsubst_tac' ctxt search_fun;
fun subst_inner_asm_tac_aux i ctxt = EqSubst.eqsubst_asm_tac' ctxt search_fun_asm i;

(* A tactic to substitute in the first assumption
   which contains an occurrence. *)

fun subst_inner_asm_tac ctxt th =
  curry (curry (FIRST' (map uncurry (map uncurry (map subst_inner_asm_tac_aux
            (1 upto Thm.nprems_of th)))))) ctxt th;

fun fresh_fun_tac ctxt no_asm = SUBGOAL (fn (goal, i) =>
  (* Find the variable we instantiate *)
  let
    val thy = Proof_Context.theory_of ctxt;
    val abs_fresh = Global_Theory.get_thms thy "abs_fresh";
    val fresh_perm_app = Global_Theory.get_thms thy "fresh_perm_app";
    val simp_ctxt =
      ctxt addsimps (fresh_prod :: abs_fresh)
      addsimps fresh_perm_app;
    val x = hd (tl (Misc_Legacy.term_vars (Thm.prop_of exI)));
    val atom_name_opt = get_inner_fresh_fun goal;
    val n = length (Logic.strip_params goal);
    (* Here we rely on the fact that the variable introduced by generate_fresh_tac *)
    (* is the last one in the list, the inner one *)
  in
  case atom_name_opt of
    NONE => all_tac
  | SOME atom_name =>
  let
    val atom_basename = Long_Name.base_name atom_name;
    val pt_name_inst = get_dyn_thm thy ("pt_"^atom_basename^"_inst") atom_basename;
    val at_name_inst = get_dyn_thm thy ("at_"^atom_basename^"_inst") atom_basename;
    fun inst_fresh vars params i st =
   let val vars' = Misc_Legacy.term_vars (Thm.prop_of st);
   in case subtract (op =) vars vars' of
     [Var v] =>
      Seq.single
        (Thm.instantiate (TVars.empty,
          Vars.make [(v, Thm.cterm_of ctxt (fold_rev Term.abs params (Bound 0)))]) st)
    | _ => error "fresh_fun_simp: Too many variables, please report."
   end
  in
  ((fn st =>
  let
    val vars = Misc_Legacy.term_vars (Thm.prop_of st);
    val params = Logic.strip_params (nth (Thm.prems_of st) (i-1))
    (* The tactics which solve the subgoals generated
       by the conditionnal rewrite rule. *)
    val post_rewrite_tacs =
          [resolve_tac ctxt [pt_name_inst],
           resolve_tac ctxt [at_name_inst],
           TRY o SOLVED' (NominalPermeq.finite_guess_tac simp_ctxt),
           inst_fresh vars params THEN'
           (TRY o SOLVED' (NominalPermeq.fresh_guess_tac simp_ctxt)) THEN'
           (TRY o SOLVED' (asm_full_simp_tac simp_ctxt))]
  in
   ((if no_asm then no_tac else
    (subst_inner_asm_tac ctxt fresh_fun_app' i THEN (RANGE post_rewrite_tacs i)))
    ORELSE
    (subst_inner_tac ctxt fresh_fun_app' i THEN (RANGE post_rewrite_tacs i))) st
  end))
  end
  end)

