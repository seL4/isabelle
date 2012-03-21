(*  Title:      HOL/Nominal/nominal_fresh_fun.ML
    Authors:    Stefan Berghofer and Julien Narboux, TU Muenchen

Provides a tactic to generate fresh names and
a tactic to analyse instances of the fresh_fun.
*)

(* First some functions that should be in the library *)  (* FIXME really?? *)

(* FIXME proper ML structure *)

(* FIXME res_inst_tac mostly obsolete, cf. Subgoal.FOCUS *)

(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)
fun gen_res_inst_tac_term instf tyinst tinst elim th i st =
  let
    val thy = theory_of_thm st;
    val cgoal = nth (cprems_of st) (i - 1);
    val {maxidx, ...} = rep_cterm cgoal;
    val j = maxidx + 1;
    val tyinst' = map (apfst (Logic.incr_tvar j)) tyinst;
    val ps = Logic.strip_params (term_of cgoal);
    val Ts = map snd ps;
    val tinst' = map (fn (t, u) =>
      (head_of (Logic.incr_indexes (Ts, j) t),
       fold_rev Term.abs ps u)) tinst;
    val th' = instf
      (map (pairself (ctyp_of thy)) tyinst')
      (map (pairself (cterm_of thy)) tinst')
      (Thm.lift_rule cgoal th)
  in
    compose_tac (elim, th', nprems_of th) i st
  end handle General.Subscript => Seq.empty;
(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)

val res_inst_tac_term =
  gen_res_inst_tac_term (curry Thm.instantiate);

val res_inst_tac_term' =
  gen_res_inst_tac_term (K Drule.cterm_instantiate) [];

fun cut_inst_tac_term' tinst th =
  res_inst_tac_term' tinst false (Rule_Insts.make_elim_preserve th);

fun get_dyn_thm thy name atom_name =
  Global_Theory.get_thm thy name handle ERROR _ =>
    error ("The atom type "^atom_name^" is not defined.");

(* End of function waiting to be in the library :o) *)

(* The theorems needed that are known at compile time. *)
val at_exists_fresh' = @{thm "at_exists_fresh'"};
val fresh_fun_app'   = @{thm "fresh_fun_app'"};
val fresh_prod       = @{thm "fresh_prod"};

(* A tactic to generate a name fresh for  all the free *)
(* variables and parameters of the goal                *)

fun generate_fresh_tac atom_name i thm =
 let
   val thy = theory_of_thm thm;
(* the parsing function returns a qualified name, we get back the base name *)
   val atom_basename = Long_Name.base_name atom_name;
   val goal = nth (prems_of thm) (i - 1);
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
   val x = hd (Misc_Legacy.term_vars (prop_of exists_fresh'));
 in
   (cut_inst_tac_term' [(x,s)] exists_fresh' 1 THEN
   rtac fs_name_thm 1 THEN
   etac exE 1) thm
  handle List.Empty  => all_tac thm (* if we collected no variables then we do nothing *)
  end;

fun get_inner_fresh_fun (Bound j) = NONE
  | get_inner_fresh_fun (v as Free _) = NONE
  | get_inner_fresh_fun (v as Var _)  = NONE
  | get_inner_fresh_fun (Const _) = NONE
  | get_inner_fresh_fun (Abs (_, _, t)) = get_inner_fresh_fun t
  | get_inner_fresh_fun (Const ("Nominal.fresh_fun",Type("fun",[Type ("fun",[Type (T,_),_]),_])) $ u)
                           = SOME T
  | get_inner_fresh_fun (t $ u) =
     let val a = get_inner_fresh_fun u in
     if a = NONE then get_inner_fresh_fun t else a
     end;

(* This tactic generates a fresh name of the atom type *)
(* given by the innermost fresh_fun                    *)

fun generate_fresh_fun_tac i thm =
  let
    val goal = nth (prems_of thm) (i - 1);
    val atom_name_opt = get_inner_fresh_fun goal;
  in
  case atom_name_opt of
    NONE => all_tac thm
  | SOME atom_name  => generate_fresh_tac atom_name i thm
  end

(* Two substitution tactics which looks for the innermost occurence in
   one assumption or in the conclusion *)

val search_fun = curry (Seq.flat o uncurry EqSubst.searchf_bt_unify_valid);
val search_fun_asm = EqSubst.skip_first_asm_occs_search EqSubst.searchf_bt_unify_valid;

fun subst_inner_tac ctxt = EqSubst.eqsubst_tac' ctxt search_fun;
fun subst_inner_asm_tac_aux i ctxt = EqSubst.eqsubst_asm_tac' ctxt search_fun_asm i;

(* A tactic to substitute in the first assumption
   which contains an occurence. *)

fun subst_inner_asm_tac ctxt th =
  curry (curry (FIRST' (map uncurry (map uncurry (map subst_inner_asm_tac_aux
            (1 upto Thm.nprems_of th)))))) ctxt th;

fun fresh_fun_tac no_asm i thm =
  (* Find the variable we instantiate *)
  let
    val thy = theory_of_thm thm;
    val ctxt = Proof_Context.init_global thy;
    val ss = global_simpset_of thy;
    val abs_fresh = Global_Theory.get_thms thy "abs_fresh";
    val fresh_perm_app = Global_Theory.get_thms thy "fresh_perm_app";
    val ss' = ss addsimps fresh_prod::abs_fresh;
    val ss'' = ss' addsimps fresh_perm_app;
    val x = hd (tl (Misc_Legacy.term_vars (prop_of exI)));
    val goal = nth (prems_of thm) (i-1);
    val atom_name_opt = get_inner_fresh_fun goal;
    val n = length (Logic.strip_params goal);
    (* Here we rely on the fact that the variable introduced by generate_fresh_tac *)
    (* is the last one in the list, the inner one *)
  in
  case atom_name_opt of
    NONE => all_tac thm
  | SOME atom_name =>
  let
    val atom_basename = Long_Name.base_name atom_name;
    val pt_name_inst = get_dyn_thm thy ("pt_"^atom_basename^"_inst") atom_basename;
    val at_name_inst = get_dyn_thm thy ("at_"^atom_basename^"_inst") atom_basename;
    fun inst_fresh vars params i st =
   let val vars' = Misc_Legacy.term_vars (prop_of st);
       val thy = theory_of_thm st;
   in case subtract (op =) vars vars' of
     [x] =>
      Seq.single (Thm.instantiate ([],[(cterm_of thy x,cterm_of thy (fold_rev Term.abs params (Bound 0)))]) st)
    | _ => error "fresh_fun_simp: Too many variables, please report."
   end
  in
  ((fn st =>
  let
    val vars = Misc_Legacy.term_vars (prop_of st);
    val params = Logic.strip_params (nth (prems_of st) (i-1))
    (* The tactics which solve the subgoals generated
       by the conditionnal rewrite rule. *)
    val post_rewrite_tacs =
          [rtac pt_name_inst,
           rtac at_name_inst,
           TRY o SOLVED' (NominalPermeq.finite_guess_tac ss''),
           inst_fresh vars params THEN'
           (TRY o SOLVED' (NominalPermeq.fresh_guess_tac ss'')) THEN'
           (TRY o SOLVED' (asm_full_simp_tac ss''))]
  in
   ((if no_asm then no_tac else
    (subst_inner_asm_tac ctxt fresh_fun_app' i THEN (RANGE post_rewrite_tacs i)))
    ORELSE
    (subst_inner_tac ctxt fresh_fun_app' i THEN (RANGE post_rewrite_tacs i))) st
  end)) thm

  end
  end

(* syntax for options, given "(no_asm)" will give back true, without
   gives back false *)
val options_syntax =
    (Args.parens (Args.$$$ "no_asm") >> (K true)) ||
     (Scan.succeed false);

fun setup_generate_fresh x =
  (Args.goal_spec -- Args.type_name true >>
    (fn (quant, s) => K (SIMPLE_METHOD'' quant (generate_fresh_tac s)))) x;

fun setup_fresh_fun_simp x =
  (Scan.lift options_syntax >> (fn b => K (SIMPLE_METHOD' (fresh_fun_tac b)))) x;

