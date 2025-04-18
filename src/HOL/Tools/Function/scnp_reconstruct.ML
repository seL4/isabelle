(*  Title:       HOL/Tools/Function/scnp_reconstruct.ML
    Author:      Armin Heller, TU Muenchen
    Author:      Alexander Krauss, TU Muenchen

Proof reconstruction for SCNP termination.
*)

signature SCNP_RECONSTRUCT =
sig
  val sizechange_tac : Proof.context -> tactic -> tactic

  val decomp_scnp_tac : ScnpSolve.label list -> Proof.context -> tactic

  datatype multiset_setup =
    Multiset of
    {
     msetT : typ -> typ,
     mk_mset : typ -> term list -> term,
     mset_regroup_conv : Proof.context -> int list -> conv,
     mset_member_tac : Proof.context -> int -> int -> tactic,
     mset_nonempty_tac : Proof.context -> int -> tactic,
     mset_pwleq_tac : Proof.context -> int -> tactic,
     set_of_simps : thm list,
     smsI' : thm,
     wmsI2'' : thm,
     wmsI1 : thm,
     reduction_pair : thm
    }

  val multiset_setup : multiset_setup -> theory -> theory
end

structure ScnpReconstruct : SCNP_RECONSTRUCT =
struct

val PROFILE = Function_Common.PROFILE

open ScnpSolve

val natT = HOLogic.natT
val nat_pairT = HOLogic.mk_prodT (natT, natT)


(* Theory dependencies *)

datatype multiset_setup =
  Multiset of
  {
   msetT : typ -> typ,
   mk_mset : typ -> term list -> term,
   mset_regroup_conv : Proof.context -> int list -> conv,
   mset_member_tac : Proof.context -> int -> int -> tactic,
   mset_nonempty_tac : Proof.context -> int -> tactic,
   mset_pwleq_tac : Proof.context -> int -> tactic,
   set_of_simps : thm list,
   smsI' : thm,
   wmsI2'' : thm,
   wmsI1 : thm,
   reduction_pair : thm
  }

structure Multiset_Setup = Theory_Data
(
  type T = multiset_setup option
  val empty = NONE
  val merge = merge_options
)

val multiset_setup = Multiset_Setup.put o SOME

fun undef _ = error "undef"

fun get_multiset_setup ctxt = Multiset_Setup.get (Proof_Context.theory_of ctxt)
  |> the_default (Multiset
    { msetT = undef, mk_mset=undef,
      mset_regroup_conv=undef, mset_member_tac = undef,
      mset_nonempty_tac = undef, mset_pwleq_tac = undef,
      set_of_simps = [],reduction_pair = refl,
      smsI'=refl, wmsI2''=refl, wmsI1=refl })

fun order_rpair _ MAX = @{thm max_rpair_set}
  | order_rpair msrp MS  = msrp
  | order_rpair _ MIN = @{thm min_rpair_set}

fun ord_intros_max true = (@{thm smax_emptyI}, @{thm smax_insertI})
  | ord_intros_max false = (@{thm wmax_emptyI}, @{thm wmax_insertI})

fun ord_intros_min true = (@{thm smin_emptyI}, @{thm smin_insertI})
  | ord_intros_min false = (@{thm wmin_emptyI}, @{thm wmin_insertI})

fun gen_probl D cs =
  let
    val n = Termination.get_num_points D
    val arity = length o Termination.get_measures D
    fun measure p i = nth (Termination.get_measures D p) i

    fun mk_graph c =
      let
        val (_, p, _, q, _, _) = Termination.dest_call D c

        fun add_edge i j =
          case Termination.get_descent D c (measure p i) (measure q j)
           of SOME (Termination.Less _) => cons (i, GTR, j)
            | SOME (Termination.LessEq _) => cons (i, GEQ, j)
            | _ => I

        val edges =
          fold_product add_edge (0 upto arity p - 1) (0 upto arity q - 1) []
      in
        G (p, q, edges)
      end
  in
    GP (map_range arity n, map mk_graph cs)
  end

(* General reduction pair application *)
fun rem_inv_img ctxt =
  resolve_tac ctxt @{thms subsetI} 1
  THEN eresolve_tac ctxt @{thms CollectE} 1
  THEN REPEAT (eresolve_tac ctxt @{thms exE} 1)
  THEN Local_Defs.unfold0_tac ctxt @{thms inv_image_def}
  THEN resolve_tac ctxt @{thms CollectI} 1
  THEN eresolve_tac ctxt @{thms conjE} 1
  THEN eresolve_tac ctxt @{thms ssubst} 1
  THEN Local_Defs.unfold0_tac ctxt @{thms split_conv triv_forall_equality sum.case}


(* Sets *)

val setT = HOLogic.mk_setT

fun set_member_tac ctxt m i =
  if m = 0 then resolve_tac ctxt @{thms insertI1} i
  else resolve_tac ctxt @{thms insertI2} i THEN set_member_tac ctxt (m - 1) i

fun set_nonempty_tac ctxt = resolve_tac ctxt @{thms insert_not_empty}

fun set_finite_tac ctxt i =
  resolve_tac ctxt @{thms finite.emptyI} i
  ORELSE (resolve_tac ctxt @{thms finite.insertI} i THEN (fn st => set_finite_tac ctxt i st))


(* Reconstruction *)

fun reconstruct_tac ctxt D cs (GP (_, gs)) certificate =
  let
    val Multiset
          { msetT, mk_mset,
            mset_regroup_conv, mset_pwleq_tac, set_of_simps,
            smsI', wmsI2'', wmsI1, reduction_pair=ms_rp, ...}
        = get_multiset_setup ctxt

    fun measure_fn p = nth (Termination.get_measures D p)

    fun get_desc_thm cidx m1 m2 bStrict =
      (case Termination.get_descent D (nth cs cidx) m1 m2 of
        SOME (Termination.Less thm) =>
          if bStrict then thm
          else (thm COMP (Thm.lift_rule (Thm.cprop_of thm) @{thm less_imp_le}))
      | SOME (Termination.LessEq (thm, _))  =>
          if not bStrict then thm
          else raise Fail "get_desc_thm"
      | _ => raise Fail "get_desc_thm")

    val (label, lev, sl, covering) = certificate

    fun prove_lev strict g =
      let
        val G (p, q, _) = nth gs g

        fun less_proof strict (j, b) (i, a) =
          let
            val tag_flag = b < a orelse (not strict andalso b <= a)

            val stored_thm =
              get_desc_thm g (measure_fn p i) (measure_fn q j)
                             (not tag_flag)
              |> Conv.fconv_rule (Thm.beta_conversion true)

            val rule =
              if strict
              then if b < a then @{thm pair_lessI2} else @{thm pair_lessI1}
              else if b <= a then @{thm pair_leqI2} else @{thm pair_leqI1}
          in
            resolve_tac ctxt [rule] 1 THEN PRIMITIVE (Thm.elim_implies stored_thm)
            THEN (if tag_flag then Arith_Data.arith_tac ctxt 1 else all_tac)
          end

        fun steps_tac MAX strict lq lp =
              let
                val (empty, step) = ord_intros_max strict
              in
                if length lq = 0
                then resolve_tac ctxt [empty] 1 THEN set_finite_tac ctxt 1
                     THEN (if strict then set_nonempty_tac ctxt 1 else all_tac)
                else
                  let
                    val (j, b) :: rest = lq
                    val (i, a) = the (covering g strict j)
                    fun choose xs = set_member_tac ctxt (find_index (curry op = (i, a)) xs) 1
                    val solve_tac = choose lp THEN less_proof strict (j, b) (i, a)
                  in
                    resolve_tac ctxt [step] 1 THEN solve_tac THEN steps_tac MAX strict rest lp
                  end
              end
          | steps_tac MIN strict lq lp =
              let
                val (empty, step) = ord_intros_min strict
              in
                if length lp = 0
                then resolve_tac ctxt [empty] 1
                     THEN (if strict then set_nonempty_tac ctxt 1 else all_tac)
                else
                  let
                    val (i, a) :: rest = lp
                    val (j, b) = the (covering g strict i)
                    fun choose xs = set_member_tac ctxt (find_index (curry op = (j, b)) xs) 1
                    val solve_tac = choose lq THEN less_proof strict (j, b) (i, a)
                  in
                    resolve_tac ctxt [step] 1 THEN solve_tac THEN steps_tac MIN strict lq rest
                  end
              end
          | steps_tac MS strict lq lp =
              let
                fun get_str_cover (j, b) =
                  if is_some (covering g true j) then SOME (j, b) else NONE
                fun get_wk_cover (j, b) = the (covering g false j)

                val qs = subtract (op =) (map_filter get_str_cover lq) lq
                val ps = map get_wk_cover qs

                fun indices xs ys = map (fn y => find_index (curry op = y) xs) ys
                val iqs = indices lq qs
                val ips = indices lp ps

                local open Conv in
                fun t_conv a C =
                  params_conv ~1 (K ((concl_conv ~1 o arg_conv o arg1_conv o a) C)) ctxt
                val goal_rewrite =
                    t_conv arg1_conv (mset_regroup_conv ctxt iqs)
                    then_conv t_conv arg_conv (mset_regroup_conv ctxt ips)
                end
              in
                CONVERSION goal_rewrite 1
                THEN (if strict then resolve_tac ctxt [smsI'] 1
                      else if qs = lq then resolve_tac ctxt [wmsI2''] 1
                      else resolve_tac ctxt [wmsI1] 1)
                THEN mset_pwleq_tac ctxt 1
                THEN EVERY (map2 (less_proof false) qs ps)
                THEN (if strict orelse qs <> lq
                      then Local_Defs.unfold0_tac ctxt set_of_simps
                           THEN steps_tac MAX true
                           (subtract (op =) qs lq) (subtract (op =) ps lp)
                      else all_tac)
              end
      in
        rem_inv_img ctxt
        THEN steps_tac label strict (nth lev q) (nth lev p)
      end

    val (mk_set, setT) = if label = MS then (mk_mset, msetT) else (HOLogic.mk_set, setT)

    fun tag_pair p (i, tag) =
      HOLogic.pair_const natT natT $
        (measure_fn p i $ Bound 0) $ HOLogic.mk_number natT tag

    fun pt_lev (p, lm) =
      Abs ("x", Termination.get_types D p, mk_set nat_pairT (map (tag_pair p) lm))

    val level_mapping =
      map_index pt_lev lev
        |> Termination.mk_sumcases D (setT nat_pairT)
        |> Thm.cterm_of ctxt
    in
      PROFILE "Proof Reconstruction"
        (CONVERSION (Conv.arg_conv (Conv.arg_conv (Function_Lib.regroup_union_conv ctxt sl))) 1
         THEN (resolve_tac ctxt @{thms reduction_pair_lemma} 1)
         THEN (resolve_tac ctxt @{thms rp_inv_image_rp} 1)
         THEN (resolve_tac ctxt [order_rpair ms_rp label] 1)
         THEN PRIMITIVE (Thm.instantiate' [] [SOME level_mapping])
         THEN unfold_tac ctxt @{thms rp_inv_image_def}
         THEN Local_Defs.unfold0_tac ctxt @{thms split_conv fst_conv snd_conv}
         THEN REPEAT (SOMEGOAL (resolve_tac ctxt [@{thm Un_least}, @{thm empty_subsetI}]))
         THEN EVERY (map (prove_lev true) sl)
         THEN EVERY (map (prove_lev false) (subtract (op =) sl (0 upto length cs - 1))))
    end


fun single_scnp_tac use_tags orders ctxt D = Termination.CALLS (fn (cs, i) =>
  let
    val ms_configured = is_some (Multiset_Setup.get (Proof_Context.theory_of ctxt))
    val orders' =
      if ms_configured then orders
      else filter_out (curry op = MS) orders
    val gp = gen_probl D cs
    val certificate = generate_certificate use_tags orders' gp
  in
    (case certificate of
      NONE => no_tac
    | SOME cert =>
        SELECT_GOAL (reconstruct_tac ctxt D cs gp cert) i
        THEN TRY (resolve_tac ctxt @{thms wf_on_bot} i))
  end)

fun gen_decomp_scnp_tac orders autom_tac ctxt =
  Termination.TERMINATION ctxt autom_tac (fn D =>
    let
      val decompose = Termination.decompose_tac ctxt D
      val scnp_full = single_scnp_tac true orders ctxt D
    in
      REPEAT_ALL_NEW (scnp_full ORELSE' decompose)
    end)

fun gen_sizechange_tac orders autom_tac ctxt =
  TRY (Function_Common.termination_rule_tac ctxt 1)
  THEN TRY (Termination.wf_union_tac ctxt)
  THEN (resolve_tac ctxt @{thms wf_on_bot} 1 ORELSE gen_decomp_scnp_tac orders autom_tac ctxt 1)

fun sizechange_tac ctxt autom_tac =
  gen_sizechange_tac [MAX, MS, MIN] autom_tac ctxt

fun decomp_scnp_tac orders ctxt =
  let
    val extra_simps = Named_Theorems.get ctxt \<^named_theorems>\<open>termination_simp\<close>
    val autom_tac = auto_tac (ctxt addsimps extra_simps)
  in
     gen_sizechange_tac orders autom_tac ctxt
  end


(* Method setup *)

val orders =
  Scan.repeat1
    ((Args.$$$ "max" >> K MAX) ||
     (Args.$$$ "min" >> K MIN) ||
     (Args.$$$ "ms" >> K MS))
  || Scan.succeed [MAX, MS, MIN]

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>size_change\<close>
      (Scan.lift orders --| Method.sections clasimp_modifiers >>
        (fn orders => SIMPLE_METHOD o decomp_scnp_tac orders))
      "termination prover with graph decomposition and the NP subset of size change termination")

end
