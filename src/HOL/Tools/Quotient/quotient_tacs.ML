(*  Title:      HOL/Tools/Quotient/quotient_tacs.ML
    Author:     Cezary Kaliszyk and Christian Urban

Tactics for solving goal arising from lifting theorems to quotient
types.
*)

signature QUOTIENT_TACS =
sig
  val regularize_tac: Proof.context -> int -> tactic
  val injection_tac: Proof.context -> int -> tactic
  val all_injection_tac: Proof.context -> int -> tactic
  val clean_tac: Proof.context -> int -> tactic

  val descend_procedure_tac: Proof.context -> thm list -> int -> tactic
  val descend_tac: Proof.context -> thm list -> int -> tactic
  val partiality_descend_procedure_tac: Proof.context -> thm list -> int -> tactic
  val partiality_descend_tac: Proof.context -> thm list -> int -> tactic


  val lift_procedure_tac: Proof.context -> thm list -> thm -> int -> tactic
  val lift_tac: Proof.context -> thm list -> thm list -> int -> tactic

  val lifted: Proof.context -> typ list -> thm list -> thm -> thm
  val lifted_attrib: attribute
end;

structure Quotient_Tacs: QUOTIENT_TACS =
struct

(** various helper fuctions **)

(* Since HOL_basic_ss is too "big" for us, we *)
(* need to set up our own minimal simpset.    *)
fun mk_minimal_simpset ctxt =
  empty_simpset ctxt
  |> Simplifier.set_subgoaler asm_simp_tac
  |> Simplifier.set_mksimps (mksimps [])

(* composition of two theorems, used in maps *)
fun OF1 thm1 thm2 = thm2 RS thm1

fun atomize_thm ctxt thm =
  let
    val thm' = Thm.legacy_freezeT (Thm.forall_intr_vars thm) (* FIXME/TODO: is this proper Isar-technology? no! *)
    val thm'' = Object_Logic.atomize ctxt (Thm.cprop_of thm')
  in
    @{thm equal_elim_rule1} OF [thm'', thm']
  end



(*** Regularize Tactic ***)

(** solvers for equivp and quotient assumptions **)

fun equiv_tac ctxt =
  REPEAT_ALL_NEW (resolve_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>quot_equiv\<close>)))

val equiv_solver = mk_solver "Equivalence goal solver" equiv_tac

fun quotient_tac ctxt =
  (REPEAT_ALL_NEW (FIRST'
    [resolve_tac ctxt @{thms identity_quotient3},
     resolve_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>quot_thm\<close>))]))

val quotient_solver = mk_solver "Quotient goal solver" quotient_tac

fun solve_quotient_assm ctxt thm =
  case Seq.pull (quotient_tac ctxt 1 thm) of
    SOME (t, _) => t
  | _ => error "Solve_quotient_assm failed. Possibly a quotient theorem is missing."


fun get_match_inst thy pat trm =
  let
    val univ = Unify.matchers (Context.Theory thy) [(pat, trm)]
    val SOME (env, _) = Seq.pull univ           (* raises Bind, if no unifier *) (* FIXME fragile *)
    val tenv = Vartab.dest (Envir.term_env env)
    val tyenv = Vartab.dest (Envir.type_env env)
    fun prep_ty (x, (S, ty)) = ((x, S), Thm.global_ctyp_of thy ty)
    fun prep_trm (x, (T, t)) = ((x, T), Thm.global_cterm_of thy t)
  in
    (TVars.make (map prep_ty tyenv), Vars.make (map prep_trm tenv))
  end

(* Calculates the instantiations for the lemmas:

      ball_reg_eqv_range and bex_reg_eqv_range

   Since the left-hand-side contains a non-pattern '?P (f ?x)'
   we rely on unification/instantiation to check whether the
   theorem applies and return NONE if it doesn't.
*)
fun calculate_inst ctxt ball_bex_thm redex R1 R2 =
  let
    val thy = Proof_Context.theory_of ctxt
    fun get_lhs thm = fst (Logic.dest_equals (Thm.concl_of thm))
    val ty_inst = map (SOME o Thm.ctyp_of ctxt) [domain_type (fastype_of R2)]
    val trm_inst = map (SOME o Thm.cterm_of ctxt) [R2, R1]
  in
    (case try (Thm.instantiate' ty_inst trm_inst) ball_bex_thm of
      NONE => NONE
    | SOME thm' =>
        (case try (get_match_inst thy (get_lhs thm')) (Thm.term_of redex) of
          NONE => NONE
        | SOME inst2 => try (Drule.instantiate_normalize inst2) thm'))
  end

fun ball_bex_range_simproc ctxt redex =
  (case Thm.term_of redex of
    (Const (\<^const_name>\<open>Ball\<close>, _) $ (Const (\<^const_name>\<open>Respects\<close>, _) $
      (Const (\<^const_name>\<open>rel_fun\<close>, _) $ R1 $ R2)) $ _) =>
        calculate_inst ctxt @{thm ball_reg_eqv_range[THEN eq_reflection]} redex R1 R2

  | (Const (\<^const_name>\<open>Bex\<close>, _) $ (Const (\<^const_name>\<open>Respects\<close>, _) $
      (Const (\<^const_name>\<open>rel_fun\<close>, _) $ R1 $ R2)) $ _) =>
        calculate_inst ctxt @{thm bex_reg_eqv_range[THEN eq_reflection]} redex R1 R2

  | _ => NONE)

(* Regularize works as follows:

  0. preliminary simplification step according to
     ball_reg_eqv bex_reg_eqv babs_reg_eqv ball_reg_eqv_range bex_reg_eqv_range

  1. eliminating simple Ball/Bex instances (ball_reg_right bex_reg_left)

  2. monos

  3. commutation rules for ball and bex (ball_all_comm bex_ex_comm)

  4. then rel-equalities, which need to be instantiated with 'eq_imp_rel'
     to avoid loops

  5. then simplification like 0

  finally jump back to 1
*)

fun reflp_get ctxt =
  map_filter (fn th => if Thm.no_prems th then SOME (OF1 @{thm equivp_reflp} th) else NONE
    handle THM _ => NONE) (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>quot_equiv\<close>))

val eq_imp_rel = @{lemma "equivp R \<Longrightarrow> a = b \<longrightarrow> R a b" by (simp add: equivp_reflp)}

fun eq_imp_rel_get ctxt =
  map (OF1 eq_imp_rel) (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>quot_equiv\<close>))

val regularize_simproc =
  Simplifier.make_simproc \<^context> "regularize"
    {lhss = [\<^term>\<open>Ball (Respects (R1 ===> R2)) P\<close>, \<^term>\<open>Bex (Respects (R1 ===> R2)) P\<close>],
     proc = K ball_bex_range_simproc};

fun regularize_tac ctxt =
  let
    val simpset =
      mk_minimal_simpset ctxt
      addsimps @{thms ball_reg_eqv bex_reg_eqv babs_reg_eqv babs_simp}
      addsimprocs [regularize_simproc]
      addSolver equiv_solver addSolver quotient_solver
    val eq_eqvs = eq_imp_rel_get ctxt
  in
    simp_tac simpset THEN'
    TRY o REPEAT_ALL_NEW (CHANGED o FIRST'
      [resolve_tac ctxt @{thms ball_reg_right bex_reg_left bex1_bexeq_reg},
       resolve_tac ctxt (Inductive.get_monos ctxt),
       resolve_tac ctxt @{thms ball_all_comm bex_ex_comm},
       resolve_tac ctxt eq_eqvs,
       simp_tac simpset])
  end



(*** Injection Tactic ***)

(* Looks for Quot_True assumptions, and in case its parameter
   is an application, it returns the function and the argument.
*)
fun find_qt_asm asms =
  let
    fun find_fun trm =
      (case trm of
        (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Quot_True\<close>, _) $ _)) => true
      | _ => false)
  in
     (case find_first find_fun asms of
       SOME (_ $ (_ $ (f $ a))) => SOME (f, a)
     | _ => NONE)
  end

fun quot_true_simple_conv ctxt fnctn ctrm =
  (case Thm.term_of ctrm of
    (Const (\<^const_name>\<open>Quot_True\<close>, _) $ x) =>
      let
        val fx = fnctn x;
        val cx = Thm.cterm_of ctxt x;
        val cfx = Thm.cterm_of ctxt fx;
        val cxt = Thm.ctyp_of ctxt (fastype_of x);
        val cfxt = Thm.ctyp_of ctxt (fastype_of fx);
        val thm = Thm.instantiate' [SOME cxt, SOME cfxt] [SOME cx, SOME cfx] @{thm QT_imp}
      in
        Conv.rewr_conv thm ctrm
      end)

fun quot_true_conv ctxt fnctn ctrm =
  (case Thm.term_of ctrm of
    (Const (\<^const_name>\<open>Quot_True\<close>, _) $ _) =>
      quot_true_simple_conv ctxt fnctn ctrm
  | _ $ _ => Conv.comb_conv (quot_true_conv ctxt fnctn) ctrm
  | Abs _ => Conv.abs_conv (fn (_, ctxt) => quot_true_conv ctxt fnctn) ctxt ctrm
  | _ => Conv.all_conv ctrm)

fun quot_true_tac ctxt fnctn =
  CONVERSION
    ((Conv.params_conv ~1 (fn ctxt =>
        (Conv.prems_conv ~1 (quot_true_conv ctxt fnctn)))) ctxt)

fun dest_comb (f $ a) = (f, a)
fun dest_bcomb ((_ $ l) $ r) = (l, r)

fun unlam t =
  (case t of
    Abs _ => snd (Term.dest_abs_global t)
  | _ => unlam (Abs("", domain_type (fastype_of t), (incr_boundvars 1 t) $ (Bound 0))))

val bare_concl = HOLogic.dest_Trueprop o Logic.strip_assums_concl

(* We apply apply_rsp only in case if the type needs lifting.
   This is the case if the type of the data in the Quot_True
   assumption is different from the corresponding type in the goal.
*)
val apply_rsp_tac =
  Subgoal.FOCUS (fn {concl, asms, context = ctxt,...} =>
    let
      val bare_concl = HOLogic.dest_Trueprop (Thm.term_of concl)
      val qt_asm = find_qt_asm (map Thm.term_of asms)
    in
      case (bare_concl, qt_asm) of
        (R2 $ (f $ x) $ (g $ y), SOME (qt_fun, qt_arg)) =>
          if fastype_of qt_fun = fastype_of f
          then no_tac
          else
            let
              val ty_x = fastype_of x
              val ty_b = fastype_of qt_arg
              val ty_f = range_type (fastype_of f)
              val ty_inst = map (SOME o Thm.ctyp_of ctxt) [ty_x, ty_b, ty_f]
              val t_inst = map (SOME o Thm.cterm_of ctxt) [R2, f, g, x, y];
              val inst_thm = Thm.instantiate' ty_inst
                ([NONE, NONE, NONE] @ t_inst) @{thm apply_rspQ3}
            in
              (resolve_tac ctxt [inst_thm] THEN' SOLVED' (quotient_tac ctxt)) 1
            end
      | _ => no_tac
    end)

(* Instantiates and applies 'equals_rsp'. Since the theorem is
   complex we rely on instantiation to tell us if it applies
*)
fun equals_rsp_tac R ctxt =
  case try (Thm.cterm_of ctxt) R of (* There can be loose bounds in R *)  (* FIXME fragile *)
    SOME ctm =>
      let
        val ty = domain_type (fastype_of R)
      in
        case try (Thm.instantiate' [SOME (Thm.ctyp_of ctxt ty)]
            [SOME (Thm.cterm_of ctxt R)]) @{thm equals_rsp} of
          SOME thm => resolve_tac ctxt [thm] THEN' quotient_tac ctxt
        | NONE => K no_tac
      end
  | _ => K no_tac

fun rep_abs_rsp_tac ctxt =
  SUBGOAL (fn (goal, i) =>
    (case try bare_concl goal of
      SOME (rel $ _ $ (rep $ (abs $ _))) =>
        (let
          val (ty_a, ty_b) = dest_funT (fastype_of abs);
          val ty_inst = map (SOME o Thm.ctyp_of ctxt) [ty_a, ty_b];
        in
          case try (map (SOME o Thm.cterm_of ctxt)) [rel, abs, rep] of
            SOME t_inst =>
              (case try (Thm.instantiate' ty_inst t_inst) @{thm rep_abs_rsp} of
                SOME inst_thm => (resolve_tac ctxt [inst_thm] THEN' quotient_tac ctxt) i
              | NONE => no_tac)
          | NONE => no_tac
        end
        handle TERM _ => no_tac)
    | _ => no_tac))


(* Injection means to prove that the regularized theorem implies
   the abs/rep injected one.

   The deterministic part:
    - remove lambdas from both sides
    - prove Ball/Bex/Babs equalities using ball_rsp, bex_rsp, babs_rsp
    - prove Ball/Bex relations using rel_funI
    - reflexivity of equality
    - prove equality of relations using equals_rsp
    - use user-supplied RSP theorems
    - solve 'relation of relations' goals using quot_rel_rsp
    - remove rep_abs from the right side
      (Lambdas under respects may have left us some assumptions)

   Then in order:
    - split applications of lifted type (apply_rsp)
    - split applications of non-lifted type (cong_tac)
    - apply extentionality
    - assumption
    - reflexivity of the relation
*)
fun injection_match_tac ctxt = SUBGOAL (fn (goal, i) =>
  (case bare_concl goal of
      (* (R1 ===> R2) (%x...) (%x...) ----> [|R1 x y|] ==> R2 (...x) (...y) *)
    (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _) $ (Abs _) $ (Abs _)
        => resolve_tac ctxt @{thms rel_funI} THEN' quot_true_tac ctxt unlam

      (* (op =) (Ball...) (Ball...) ----> (op =) (...) (...) *)
  | (Const (\<^const_name>\<open>HOL.eq\<close>,_) $
      (Const(\<^const_name>\<open>Ball\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _) $
      (Const(\<^const_name>\<open>Ball\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _))
        => resolve_tac ctxt @{thms ball_rsp} THEN' dresolve_tac ctxt @{thms QT_all}

      (* (R1 ===> op =) (Ball...) (Ball...) ----> [|R1 x y|] ==> (Ball...x) = (Ball...y) *)
  | (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _) $
      (Const(\<^const_name>\<open>Ball\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _) $
      (Const(\<^const_name>\<open>Ball\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _)
        => resolve_tac ctxt @{thms rel_funI} THEN' quot_true_tac ctxt unlam

      (* (op =) (Bex...) (Bex...) ----> (op =) (...) (...) *)
  | Const (\<^const_name>\<open>HOL.eq\<close>,_) $
      (Const(\<^const_name>\<open>Bex\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _) $
      (Const(\<^const_name>\<open>Bex\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _)
        => resolve_tac ctxt @{thms bex_rsp} THEN' dresolve_tac ctxt @{thms QT_ex}

      (* (R1 ===> op =) (Bex...) (Bex...) ----> [|R1 x y|] ==> (Bex...x) = (Bex...y) *)
  | (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _) $
      (Const(\<^const_name>\<open>Bex\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _) $
      (Const(\<^const_name>\<open>Bex\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _)
        => resolve_tac ctxt @{thms rel_funI} THEN' quot_true_tac ctxt unlam

  | (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _) $
      (Const(\<^const_name>\<open>Bex1_rel\<close>,_) $ _) $ (Const(\<^const_name>\<open>Bex1_rel\<close>,_) $ _)
        => resolve_tac ctxt @{thms bex1_rel_rsp} THEN' quotient_tac ctxt

  | (_ $
      (Const(\<^const_name>\<open>Babs\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _) $
      (Const(\<^const_name>\<open>Babs\<close>,_) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ _) $ _))
        => resolve_tac ctxt @{thms babs_rsp} THEN' quotient_tac ctxt

  | Const (\<^const_name>\<open>HOL.eq\<close>,_) $ (R $ _ $ _) $ (_ $ _ $ _) =>
     (resolve_tac ctxt @{thms refl} ORELSE'
      (equals_rsp_tac R ctxt THEN' RANGE [
         quot_true_tac ctxt (fst o dest_bcomb), quot_true_tac ctxt (snd o dest_bcomb)]))

      (* reflexivity of operators arising from Cong_tac *)
  | Const (\<^const_name>\<open>HOL.eq\<close>,_) $ _ $ _ => resolve_tac ctxt @{thms refl}

     (* respectfulness of constants; in particular of a simple relation *)
  | _ $ (Const _) $ (Const _)  (* rel_fun, list_rel, etc but not equality *)
      => resolve_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>quot_respect\<close>))
          THEN_ALL_NEW quotient_tac ctxt

      (* R (...) (Rep (Abs ...)) ----> R (...) (...) *)
      (* observe map_fun *)
  | _ $ _ $ _
      => (resolve_tac ctxt @{thms quot_rel_rsp} THEN_ALL_NEW quotient_tac ctxt)
         ORELSE' rep_abs_rsp_tac ctxt

  | _ => K no_tac) i)

fun injection_step_tac ctxt rel_refl =
  FIRST' [
    injection_match_tac ctxt,

    (* R (t $ ...) (t' $ ...) ----> apply_rsp   provided type of t needs lifting *)
    apply_rsp_tac ctxt THEN'
                 RANGE [quot_true_tac ctxt (fst o dest_comb), quot_true_tac ctxt (snd o dest_comb)],

    (* (op =) (t $ ...) (t' $ ...) ----> Cong   provided type of t does not need lifting *)
    (* merge with previous tactic *)
    Cong_Tac.cong_tac ctxt @{thm cong} THEN'
                 RANGE [quot_true_tac ctxt (fst o dest_comb), quot_true_tac ctxt (snd o dest_comb)],

    (* resolving with R x y assumptions *)
    assume_tac ctxt,

    (* (op =) (%x...) (%y...) ----> (op =) (...) (...) *)
    resolve_tac ctxt @{thms ext} THEN' quot_true_tac ctxt unlam,

    (* reflexivity of the basic relations *)
    (* R ... ... *)
    resolve_tac ctxt rel_refl]

fun injection_tac ctxt =
  let
    val rel_refl = reflp_get ctxt
  in
    injection_step_tac ctxt rel_refl
  end

fun all_injection_tac ctxt =
  REPEAT_ALL_NEW (injection_tac ctxt)



(*** Cleaning of the Theorem ***)

(* expands all map_funs, except in front of the (bound) variables listed in xs *)
fun map_fun_simple_conv xs ctrm =
  (case Thm.term_of ctrm of
    ((Const (\<^const_name>\<open>map_fun\<close>, _) $ _ $ _) $ h $ _) =>
        if member (op=) xs h
        then Conv.all_conv ctrm
        else Conv.rewr_conv @{thm map_fun_apply [THEN eq_reflection]} ctrm
  | _ => Conv.all_conv ctrm)

fun map_fun_conv xs ctxt ctrm =
  (case Thm.term_of ctrm of
    _ $ _ =>
      (Conv.comb_conv (map_fun_conv xs ctxt) then_conv
        map_fun_simple_conv xs) ctrm
  | Abs _ => Conv.abs_conv (fn (x, ctxt) => map_fun_conv (Thm.term_of x :: xs) ctxt) ctxt ctrm
  | _ => Conv.all_conv ctrm)

fun map_fun_tac ctxt = CONVERSION (map_fun_conv [] ctxt)

(* custom matching functions *)
fun mk_abs u i t =
  if incr_boundvars i u aconv t then Bound i
  else
    case t of
      t1 $ t2 => mk_abs u i t1 $ mk_abs u i t2
    | Abs (s, T, t') => Abs (s, T, mk_abs u (i + 1) t')
    | Bound j => if i = j then error "make_inst" else t
    | _ => t

fun make_inst lhs t =
  let
    val _ $ (Abs (_, _, (_ $ ((f as Var (_, Type ("fun", [T, _]))) $ u)))) = lhs;
    val _ $ (Abs (_, _, (_ $ g))) = t;
  in
    (f, Abs ("x", T, mk_abs u 0 g))
  end

fun make_inst_id lhs t =
  let
    val _ $ (Abs (_, _, (f as Var (_, Type ("fun", [T, _]))) $ u)) = lhs;
    val _ $ (Abs (_, _, g)) = t;
  in
    (f, Abs ("x", T, mk_abs u 0 g))
  end

(* Simplifies a redex using the 'lambda_prs' theorem.
   First instantiates the types and known subterms.
   Then solves the quotient assumptions to get Rep2 and Abs1
   Finally instantiates the function f using make_inst
   If Rep2 is an identity then the pattern is simpler and
   make_inst_id is used
*)
fun lambda_prs_simple_conv ctxt ctrm =
  (case Thm.term_of ctrm of
    (Const (\<^const_name>\<open>map_fun\<close>, _) $ r1 $ a2) $ (Abs _) =>
      let
        val (ty_b, ty_a) = dest_funT (fastype_of r1)
        val (ty_c, ty_d) = dest_funT (fastype_of a2)
        val tyinst = map (SOME o Thm.ctyp_of ctxt) [ty_a, ty_b, ty_c, ty_d]
        val tinst = [NONE, NONE, SOME (Thm.cterm_of ctxt r1), NONE, SOME (Thm.cterm_of ctxt a2)]
        val thm1 = Thm.instantiate' tyinst tinst @{thm lambda_prs[THEN eq_reflection]}
        val thm2 = solve_quotient_assm ctxt (solve_quotient_assm ctxt thm1)
        val thm3 = rewrite_rule ctxt @{thms id_apply[THEN eq_reflection]} thm2
        val (insp, inst) =
          if ty_c = ty_d
          then make_inst_id (Thm.term_of (Thm.lhs_of thm3)) (Thm.term_of ctrm)
          else make_inst (Thm.term_of (Thm.lhs_of thm3)) (Thm.term_of ctrm)
        val thm4 =
          Drule.instantiate_normalize
            (TVars.empty, Vars.make [(dest_Var insp, Thm.cterm_of ctxt inst)]) thm3
      in
        Conv.rewr_conv thm4 ctrm
      end
  | _ => Conv.all_conv ctrm)

fun lambda_prs_conv ctxt = Conv.top_conv lambda_prs_simple_conv ctxt
fun lambda_prs_tac ctxt = CONVERSION (lambda_prs_conv ctxt)


(* Cleaning consists of:

  1. unfolding of ---> in front of everything, except
     bound variables (this prevents lambda_prs from
     becoming stuck)

  2. simplification with lambda_prs

  3. simplification with:

      - Quotient_abs_rep Quotient_rel_rep
        babs_prs all_prs ex_prs ex1_prs

      - id_simps and preservation lemmas and

      - symmetric versions of the definitions
        (that is definitions of quotient constants
         are folded)

  4. test for refl
*)
fun clean_tac ctxt =
  let
    val thy =  Proof_Context.theory_of ctxt
    val defs = map (Thm.symmetric o #def) (Quotient_Info.dest_quotconsts_global thy)
    val prs = rev (Named_Theorems.get ctxt \<^named_theorems>\<open>quot_preserve\<close>)
    val ids = rev (Named_Theorems.get ctxt \<^named_theorems>\<open>id_simps\<close>)
    val thms =
      @{thms Quotient3_abs_rep Quotient3_rel_rep babs_prs all_prs ex_prs ex1_prs} @ ids @ prs @ defs

    val simpset = (mk_minimal_simpset ctxt) addsimps thms addSolver quotient_solver
  in
    EVERY' [
      map_fun_tac ctxt,
      lambda_prs_tac ctxt,
      simp_tac simpset,
      TRY o resolve_tac ctxt [refl]]
  end


(* Tactic for Generalising Free Variables in a Goal *)

fun inst_spec ctrm =
  Thm.instantiate' [SOME (Thm.ctyp_of_cterm ctrm)] [NONE, SOME ctrm] @{thm spec}

fun inst_spec_tac ctxt ctrms =
  EVERY' (map (dresolve_tac ctxt o single o inst_spec) ctrms)

fun all_list xs trm =
  fold (fn (x, T) => fn t' => HOLogic.mk_all (x, T, t')) xs trm

fun apply_under_Trueprop f =
  HOLogic.dest_Trueprop #> f #> HOLogic.mk_Trueprop

fun gen_frees_tac ctxt =
  SUBGOAL (fn (concl, i) =>
    let
      val vrs = Term.add_frees concl []
      val cvrs = map (Thm.cterm_of ctxt o Free) vrs
      val concl' = apply_under_Trueprop (all_list vrs) concl
      val goal = Logic.mk_implies (concl', concl)
      val rule = Goal.prove ctxt [] [] goal
        (K (EVERY1 [inst_spec_tac ctxt (rev cvrs), assume_tac ctxt]))
    in
      resolve_tac ctxt [rule] i
    end)


(** The General Shape of the Lifting Procedure **)

(* - A is the original raw theorem
   - B is the regularized theorem
   - C is the rep/abs injected version of B
   - D is the lifted theorem

   - 1st prem is the regularization step
   - 2nd prem is the rep/abs injection step
   - 3rd prem is the cleaning part

   the Quot_True premise in 2nd records the lifted theorem
*)
val procedure_thm =
  @{lemma  "\<lbrakk>A;
              A \<longrightarrow> B;
              Quot_True D \<Longrightarrow> B = C;
              C = D\<rbrakk> \<Longrightarrow> D"
      by (simp add: Quot_True_def)}

(* in case of partial equivalence relations, this form of the 
   procedure theorem results in solvable proof obligations 
*)
val partiality_procedure_thm =
  @{lemma  "[|B; 
              Quot_True D ==> B = C;
              C = D|] ==> D"
      by (simp add: Quot_True_def)}

fun lift_match_error ctxt msg rtrm qtrm =
  let
    val rtrm_str = Syntax.string_of_term ctxt rtrm
    val qtrm_str = Syntax.string_of_term ctxt qtrm
    val msg = cat_lines [enclose "[" "]" msg, "The quotient theorem", qtrm_str,
      "", "does not match with original theorem", rtrm_str]
  in
    error msg
  end

fun procedure_inst ctxt rtrm qtrm =
  let
    val rtrm' = HOLogic.dest_Trueprop rtrm
    val qtrm' = HOLogic.dest_Trueprop qtrm
    val reg_goal = Quotient_Term.regularize_trm_chk ctxt (rtrm', qtrm')
      handle Quotient_Term.LIFT_MATCH msg => lift_match_error ctxt msg rtrm qtrm
    val inj_goal = Quotient_Term.inj_repabs_trm_chk ctxt (reg_goal, qtrm')
      handle Quotient_Term.LIFT_MATCH msg => lift_match_error ctxt msg rtrm qtrm
  in
    Thm.instantiate' []
      [SOME (Thm.cterm_of ctxt rtrm'),
       SOME (Thm.cterm_of ctxt reg_goal),
       NONE,
       SOME (Thm.cterm_of ctxt inj_goal)] procedure_thm
  end


(* Since we use Ball and Bex during the lifting and descending,
   we cannot deal with lemmas containing them, unless we unfold
   them by default. *)

val default_unfolds = @{thms Ball_def Bex_def}


(** descending as tactic **)

fun descend_procedure_tac ctxt simps =
  let
    val simpset = (mk_minimal_simpset ctxt) addsimps (simps @ default_unfolds)
  in
    full_simp_tac simpset
    THEN' Object_Logic.full_atomize_tac ctxt
    THEN' gen_frees_tac ctxt
    THEN' SUBGOAL (fn (goal, i) =>
      let
        val qtys = map #qtyp (Quotient_Info.dest_quotients ctxt)
        val rtrm = Quotient_Term.derive_rtrm ctxt qtys goal
        val rule = procedure_inst ctxt rtrm  goal
      in
        resolve_tac ctxt [rule] i
      end)
  end

fun descend_tac ctxt simps =
  let
    val mk_tac_raw =
      descend_procedure_tac ctxt simps
      THEN' RANGE
        [Object_Logic.rulify_tac ctxt THEN' (K all_tac),
         regularize_tac ctxt,
         all_injection_tac ctxt,
         clean_tac ctxt]
  in
    Goal.conjunction_tac THEN_ALL_NEW mk_tac_raw
  end


(** descending for partial equivalence relations **)

fun partiality_procedure_inst ctxt rtrm qtrm =
  let
    val rtrm' = HOLogic.dest_Trueprop rtrm
    val qtrm' = HOLogic.dest_Trueprop qtrm
    val reg_goal = Quotient_Term.regularize_trm_chk ctxt (rtrm', qtrm')
      handle Quotient_Term.LIFT_MATCH msg => lift_match_error ctxt msg rtrm qtrm
    val inj_goal = Quotient_Term.inj_repabs_trm_chk ctxt (reg_goal, qtrm')
      handle Quotient_Term.LIFT_MATCH msg => lift_match_error ctxt msg rtrm qtrm
  in
    Thm.instantiate' []
      [SOME (Thm.cterm_of ctxt reg_goal),
       NONE,
       SOME (Thm.cterm_of ctxt inj_goal)] partiality_procedure_thm
  end


fun partiality_descend_procedure_tac ctxt simps =
  let
    val simpset = (mk_minimal_simpset ctxt) addsimps (simps @ default_unfolds)
  in
    full_simp_tac simpset
    THEN' Object_Logic.full_atomize_tac ctxt
    THEN' gen_frees_tac ctxt
    THEN' SUBGOAL (fn (goal, i) =>
      let
        val qtys = map #qtyp (Quotient_Info.dest_quotients ctxt)
        val rtrm = Quotient_Term.derive_rtrm ctxt qtys goal
        val rule = partiality_procedure_inst ctxt rtrm  goal
      in
        resolve_tac ctxt [rule] i
      end)
  end

fun partiality_descend_tac ctxt simps =
  let
    val mk_tac_raw =
      partiality_descend_procedure_tac ctxt simps
      THEN' RANGE
        [Object_Logic.rulify_tac ctxt THEN' (K all_tac),
         all_injection_tac ctxt,
         clean_tac ctxt]
  in
    Goal.conjunction_tac THEN_ALL_NEW mk_tac_raw
  end



(** lifting as a tactic **)


(* the tactic leaves three subgoals to be proved *)
fun lift_procedure_tac ctxt simps rthm =
  let
    val simpset = (mk_minimal_simpset ctxt) addsimps (simps @ default_unfolds)
  in
    full_simp_tac simpset
    THEN' Object_Logic.full_atomize_tac ctxt
    THEN' gen_frees_tac ctxt
    THEN' SUBGOAL (fn (goal, i) =>
      let
        (* full_atomize_tac contracts eta redexes,
           so we do it also in the original theorem *)
        val rthm' =
          rthm |> full_simplify simpset
               |> Drule.eta_contraction_rule
               |> Thm.forall_intr_frees
               |> atomize_thm ctxt

        val rule = procedure_inst ctxt (Thm.prop_of rthm') goal
      in
        (resolve_tac ctxt [rule] THEN' resolve_tac ctxt [rthm']) i
      end)
  end

fun lift_single_tac ctxt simps rthm =
  lift_procedure_tac ctxt simps rthm
  THEN' RANGE
    [ regularize_tac ctxt,
      all_injection_tac ctxt,
      clean_tac ctxt ]

fun lift_tac ctxt simps rthms =
  Goal.conjunction_tac
  THEN' RANGE (map (lift_single_tac ctxt simps) rthms)


(* automated lifting with pre-simplification of the theorems;
   for internal usage *)
fun lifted ctxt qtys simps rthm =
  let
    val ((_, [rthm']), ctxt') = Variable.import true [rthm] ctxt
    val goal = Quotient_Term.derive_qtrm ctxt' qtys (Thm.prop_of rthm')
  in
    Goal.prove ctxt' [] [] goal
      (K (HEADGOAL (lift_single_tac ctxt' simps rthm')))
    |> singleton (Proof_Context.export ctxt' ctxt)
  end


(* lifting as an attribute *)

val lifted_attrib = Thm.rule_attribute [] (fn context =>
  let
    val ctxt = Context.proof_of context
    val qtys = map #qtyp (Quotient_Info.dest_quotients ctxt)
  in
    lifted ctxt qtys []
  end)

end; (* structure *)
