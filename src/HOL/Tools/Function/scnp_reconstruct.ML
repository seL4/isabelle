(*  Title:       HOL/Tools/Function/scnp_reconstruct.ML
    Author:      Armin Heller, TU Muenchen
    Author:      Alexander Krauss, TU Muenchen

Proof reconstruction for SCNP
*)

signature SCNP_RECONSTRUCT =
sig

  val sizechange_tac : Proof.context -> tactic -> tactic

  val decomp_scnp : ScnpSolve.label list -> Proof.context -> Proof.method

  val setup : theory -> theory

  datatype multiset_setup =
    Multiset of
    {
     msetT : typ -> typ,
     mk_mset : typ -> term list -> term,
     mset_regroup_conv : int list -> conv,
     mset_member_tac : int -> int -> tactic,
     mset_nonempty_tac : int -> tactic,
     mset_pwleq_tac : int -> tactic,
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

val PROFILE = FundefCommon.PROFILE
fun TRACE x = if ! FundefCommon.profile then tracing x else ()

open ScnpSolve

val natT = HOLogic.natT
val nat_pairT = HOLogic.mk_prodT (natT, natT)

(* Theory dependencies *)

datatype multiset_setup =
  Multiset of
  {
   msetT : typ -> typ,
   mk_mset : typ -> term list -> term,
   mset_regroup_conv : int list -> conv,
   mset_member_tac : int -> int -> tactic,
   mset_nonempty_tac : int -> tactic,
   mset_pwleq_tac : int -> tactic,
   set_of_simps : thm list,
   smsI' : thm,
   wmsI2'' : thm,
   wmsI1 : thm,
   reduction_pair : thm
  }

structure MultisetSetup = TheoryDataFun
(
  type T = multiset_setup option
  val empty = NONE
  val copy = I;
  val extend = I;
  fun merge _ (v1, v2) = if is_some v2 then v2 else v1
)

val multiset_setup = MultisetSetup.put o SOME

fun undef x = error "undef"
fun get_multiset_setup thy = MultisetSetup.get thy
  |> the_default (Multiset
{ msetT = undef, mk_mset=undef,
  mset_regroup_conv=undef, mset_member_tac = undef,
  mset_nonempty_tac = undef, mset_pwleq_tac = undef,
  set_of_simps = [],reduction_pair = refl,
  smsI'=refl, wmsI2''=refl, wmsI1=refl })

fun order_rpair _ MAX = @{thm max_rpair_set}
  | order_rpair msrp MS  = msrp
  | order_rpair _ MIN = @{thm min_rpair_set}

fun ord_intros_max true =
    (@{thm smax_emptyI}, @{thm smax_insertI})
  | ord_intros_max false =
    (@{thm wmax_emptyI}, @{thm wmax_insertI})
fun ord_intros_min true =
    (@{thm smin_emptyI}, @{thm smin_insertI})
  | ord_intros_min false =
    (@{thm wmin_emptyI}, @{thm wmin_insertI})

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
    GP (map arity (0 upto n - 1), map mk_graph cs)
  end

(* General reduction pair application *)
fun rem_inv_img ctxt =
  let
    val unfold_tac = LocalDefs.unfold_tac ctxt
  in
    rtac @{thm subsetI} 1
    THEN etac @{thm CollectE} 1
    THEN REPEAT (etac @{thm exE} 1)
    THEN unfold_tac @{thms inv_image_def}
    THEN rtac @{thm CollectI} 1
    THEN etac @{thm conjE} 1
    THEN etac @{thm ssubst} 1
    THEN unfold_tac (@{thms split_conv} @ @{thms triv_forall_equality}
                     @ @{thms sum.cases})
  end

(* Sets *)

val setT = HOLogic.mk_setT

fun set_member_tac m i =
  if m = 0 then rtac @{thm insertI1} i
  else rtac @{thm insertI2} i THEN set_member_tac (m - 1) i

val set_nonempty_tac = rtac @{thm insert_not_empty}

fun set_finite_tac i =
  rtac @{thm finite.emptyI} i
  ORELSE (rtac @{thm finite.insertI} i THEN (fn st => set_finite_tac i st))


(* Reconstruction *)

fun reconstruct_tac ctxt D cs (gp as GP (_, gs)) certificate =
  let
    val thy = ProofContext.theory_of ctxt
    val Multiset
          { msetT, mk_mset,
            mset_regroup_conv, mset_member_tac,
            mset_nonempty_tac, mset_pwleq_tac, set_of_simps,
            smsI', wmsI2'', wmsI1, reduction_pair=ms_rp } 
        = get_multiset_setup thy

    fun measure_fn p = nth (Termination.get_measures D p)

    fun get_desc_thm cidx m1 m2 bStrict =
      case Termination.get_descent D (nth cs cidx) m1 m2
       of SOME (Termination.Less thm) =>
          if bStrict then thm
          else (thm COMP (Thm.lift_rule (cprop_of thm) @{thm less_imp_le}))
        | SOME (Termination.LessEq (thm, _))  =>
          if not bStrict then thm
          else sys_error "get_desc_thm"
        | _ => sys_error "get_desc_thm"

    val (label, lev, sl, covering) = certificate

    fun prove_lev strict g =
      let
        val G (p, q, el) = nth gs g

        fun less_proof strict (j, b) (i, a) =
          let
            val tag_flag = b < a orelse (not strict andalso b <= a)

            val stored_thm =
              get_desc_thm g (measure_fn p i) (measure_fn q j)
                             (not tag_flag)
              |> Conv.fconv_rule (Thm.beta_conversion true)

            val rule = if strict
              then if b < a then @{thm pair_lessI2} else @{thm pair_lessI1}
              else if b <= a then @{thm pair_leqI2} else @{thm pair_leqI1}
          in
            rtac rule 1 THEN PRIMITIVE (Thm.elim_implies stored_thm)
            THEN (if tag_flag then Arith_Data.verbose_arith_tac ctxt 1 else all_tac)
          end

        fun steps_tac MAX strict lq lp =
          let
            val (empty, step) = ord_intros_max strict
          in
            if length lq = 0
            then rtac empty 1 THEN set_finite_tac 1
                 THEN (if strict then set_nonempty_tac 1 else all_tac)
            else
              let
                val (j, b) :: rest = lq
                val (i, a) = the (covering g strict j)
                fun choose xs = set_member_tac (Library.find_index (curry op = (i, a)) xs) 1
                val solve_tac = choose lp THEN less_proof strict (j, b) (i, a)
              in
                rtac step 1 THEN solve_tac THEN steps_tac MAX strict rest lp
              end
          end
          | steps_tac MIN strict lq lp =
          let
            val (empty, step) = ord_intros_min strict
          in
            if length lp = 0
            then rtac empty 1
                 THEN (if strict then set_nonempty_tac 1 else all_tac)
            else
              let
                val (i, a) :: rest = lp
                val (j, b) = the (covering g strict i)
                fun choose xs = set_member_tac (Library.find_index (curry op = (j, b)) xs) 1
                val solve_tac = choose lq THEN less_proof strict (j, b) (i, a)
              in
                rtac step 1 THEN solve_tac THEN steps_tac MIN strict lq rest
              end
          end
          | steps_tac MS strict lq lp =
          let
            fun get_str_cover (j, b) =
              if is_some (covering g true j) then SOME (j, b) else NONE
            fun get_wk_cover (j, b) = the (covering g false j)

            val qs = lq \\ map_filter get_str_cover lq
            val ps = map get_wk_cover qs

            fun indices xs ys = map (fn y => Library.find_index (curry op = y) xs) ys
            val iqs = indices lq qs
            val ips = indices lp ps

            local open Conv in
            fun t_conv a C =
              params_conv ~1 (K ((concl_conv ~1 o arg_conv o arg1_conv o a) C)) ctxt
            val goal_rewrite =
                t_conv arg1_conv (mset_regroup_conv iqs)
                then_conv t_conv arg_conv (mset_regroup_conv ips)
            end
          in
            CONVERSION goal_rewrite 1
            THEN (if strict then rtac smsI' 1
                  else if qs = lq then rtac wmsI2'' 1
                  else rtac wmsI1 1)
            THEN mset_pwleq_tac 1
            THEN EVERY (map2 (less_proof false) qs ps)
            THEN (if strict orelse qs <> lq
                  then LocalDefs.unfold_tac ctxt set_of_simps
                       THEN steps_tac MAX true (lq \\ qs) (lp \\ ps)
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

    fun pt_lev (p, lm) = Abs ("x", Termination.get_types D p,
                           mk_set nat_pairT (map (tag_pair p) lm))

    val level_mapping =
      map_index pt_lev lev
        |> Termination.mk_sumcases D (setT nat_pairT)
        |> cterm_of thy
    in
      PROFILE "Proof Reconstruction"
        (CONVERSION (Conv.arg_conv (Conv.arg_conv (FundefLib.regroup_union_conv sl))) 1
         THEN (rtac @{thm reduction_pair_lemma} 1)
         THEN (rtac @{thm rp_inv_image_rp} 1)
         THEN (rtac (order_rpair ms_rp label) 1)
         THEN PRIMITIVE (instantiate' [] [SOME level_mapping])
         THEN unfold_tac @{thms rp_inv_image_def} (simpset_of ctxt)
         THEN LocalDefs.unfold_tac ctxt
           (@{thms split_conv} @ @{thms fst_conv} @ @{thms snd_conv})
         THEN REPEAT (SOMEGOAL (resolve_tac [@{thm Un_least}, @{thm empty_subsetI}]))
         THEN EVERY (map (prove_lev true) sl)
         THEN EVERY (map (prove_lev false) ((0 upto length cs - 1) \\ sl)))
    end



local open Termination in
fun print_cell (SOME (Less _)) = "<"
  | print_cell (SOME (LessEq _)) = "\<le>"
  | print_cell (SOME (None _)) = "-"
  | print_cell (SOME (False _)) = "-"
  | print_cell (NONE) = "?"

fun print_error ctxt D = CALLS (fn (cs, i) =>
  let
    val np = get_num_points D
    val ms = map (get_measures D) (0 upto np - 1)
    val tys = map (get_types D) (0 upto np - 1)
    fun index xs = (1 upto length xs) ~~ xs
    fun outp s t f xs = map (fn (x, y) => s ^ Int.toString x ^ t ^ f y ^ "\n") xs
    val ims = index (map index ms)
    val _ = tracing (concat (outp "fn #" ":\n" (concat o outp "\tmeasure #" ": " (Syntax.string_of_term ctxt)) ims))
    fun print_call (k, c) =
      let
        val (_, p, _, q, _, _) = dest_call D c
        val _ = tracing ("call table for call #" ^ Int.toString k ^ ": fn " ^ 
                                Int.toString (p + 1) ^ " ~> fn " ^ Int.toString (q + 1))
        val caller_ms = nth ms p
        val callee_ms = nth ms q
        val entries = map (fn x => map (pair x) (callee_ms)) (caller_ms)
        fun print_ln (i : int, l) = concat (Int.toString i :: "   " :: map (enclose " " " " o print_cell o (uncurry (get_descent D c))) l)
        val _ = tracing (concat (Int.toString (p + 1) ^ "|" ^ Int.toString (q + 1) ^ 
                                        " " :: map (enclose " " " " o Int.toString) (1 upto length callee_ms)) ^ "\n" 
                                ^ cat_lines (map print_ln ((1 upto (length entries)) ~~ entries)))
      in
        true
      end
    fun list_call (k, c) =
      let
        val (_, p, _, q, _, _) = dest_call D c
        val _ = tracing ("call #" ^ (Int.toString k) ^ ": fn " ^
                                Int.toString (p + 1) ^ " ~> fn " ^ Int.toString (q + 1) ^ "\n" ^ 
                                (Syntax.string_of_term ctxt c))
      in true end
    val _ = forall list_call ((1 upto length cs) ~~ cs)
    val _ = forall print_call ((1 upto length cs) ~~ cs)
  in
    all_tac
  end)
end


fun single_scnp_tac use_tags orders ctxt cont err_cont D = Termination.CALLS (fn (cs, i) =>
  let
    val ms_configured = is_some (MultisetSetup.get (ProofContext.theory_of ctxt))
    val orders' = if ms_configured then orders
                  else filter_out (curry op = MS) orders
    val gp = gen_probl D cs
(*    val _ = TRACE ("SCNP instance: " ^ makestring gp)*)
    val certificate = generate_certificate use_tags orders' gp
(*    val _ = TRACE ("Certificate: " ^ makestring certificate)*)

  in
    case certificate
     of NONE => err_cont D i
      | SOME cert =>
          SELECT_GOAL (reconstruct_tac ctxt D cs gp cert) i
          THEN (rtac @{thm wf_empty} i ORELSE cont D i)
  end)

fun gen_decomp_scnp_tac orders autom_tac ctxt err_cont =
  let
    open Termination
    val derive_diag = Descent.derive_diag ctxt autom_tac
    val derive_all = Descent.derive_all ctxt autom_tac
    val decompose = Decompose.decompose_tac ctxt autom_tac
    val scnp_no_tags = single_scnp_tac false orders ctxt
    val scnp_full = single_scnp_tac true orders ctxt

    fun first_round c e =
        derive_diag (REPEAT scnp_no_tags c e)

    val second_round =
        REPEAT (fn c => fn e => decompose (scnp_no_tags c c) e)

    val third_round =
        derive_all oo
        REPEAT (fn c => fn e =>
          scnp_full (decompose c c) e)

    fun Then s1 s2 c e = s1 (s2 c c) (s2 c e)

    val strategy = Then (Then first_round second_round) third_round

  in
    TERMINATION ctxt (strategy err_cont err_cont)
  end

fun gen_sizechange_tac orders autom_tac ctxt err_cont =
  TRY (FundefCommon.apply_termination_rule ctxt 1)
  THEN TRY (Termination.wf_union_tac ctxt)
  THEN
   (rtac @{thm wf_empty} 1
    ORELSE gen_decomp_scnp_tac orders autom_tac ctxt err_cont 1)

fun sizechange_tac ctxt autom_tac =
  gen_sizechange_tac [MAX, MS, MIN] autom_tac ctxt (K (K all_tac))

fun decomp_scnp orders ctxt =
  let
    val extra_simps = FundefCommon.Termination_Simps.get ctxt
    val autom_tac = auto_tac (clasimpset_of ctxt addsimps2 extra_simps)
  in
    SIMPLE_METHOD
      (gen_sizechange_tac orders autom_tac ctxt (print_error ctxt))
  end


(* Method setup *)

val orders =
  Scan.repeat1
    ((Args.$$$ "max" >> K MAX) ||
     (Args.$$$ "min" >> K MIN) ||
     (Args.$$$ "ms" >> K MS))
  || Scan.succeed [MAX, MS, MIN]

val setup = Method.setup @{binding sizechange}
  (Scan.lift orders --| Method.sections clasimp_modifiers >> decomp_scnp)
  "termination prover with graph decomposition and the NP subset of size change termination"

end
