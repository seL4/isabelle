(*  Title:      HOL/HOLCF/Tools/Domain/domain_take_proofs.ML
    Author:     Brian Huffman

Defines take functions for the given domain equation
and proves related theorems.
*)

signature DOMAIN_TAKE_PROOFS =
sig
  type iso_info =
    {
      absT : typ,
      repT : typ,
      abs_const : term,
      rep_const : term,
      abs_inverse : thm,
      rep_inverse : thm
    }
  type take_info =
    {
      take_consts : term list,
      take_defs : thm list,
      chain_take_thms : thm list,
      take_0_thms : thm list,
      take_Suc_thms : thm list,
      deflation_take_thms : thm list,
      take_strict_thms : thm list,
      finite_consts : term list,
      finite_defs : thm list
    }
  type take_induct_info =
    {
      take_consts         : term list,
      take_defs           : thm list,
      chain_take_thms     : thm list,
      take_0_thms         : thm list,
      take_Suc_thms       : thm list,
      deflation_take_thms : thm list,
      take_strict_thms    : thm list,
      finite_consts       : term list,
      finite_defs         : thm list,
      lub_take_thms       : thm list,
      reach_thms          : thm list,
      take_lemma_thms     : thm list,
      is_finite           : bool,
      take_induct_thms    : thm list
    }
  val define_take_functions :
    (binding * iso_info) list -> theory -> take_info * theory

  val add_lub_take_theorems :
    (binding * iso_info) list -> take_info -> thm list ->
    theory -> take_induct_info * theory

  val map_of_typ :
    theory -> (typ * term) list -> typ -> term

  val add_rec_type : (string * bool list) -> theory -> theory
  val get_rec_tab : theory -> (bool list) Symtab.table
  val add_deflation_thm : thm -> theory -> theory
  val get_deflation_thms : theory -> thm list
  val map_ID_add : attribute
  val get_map_ID_thms : theory -> thm list
  val setup : theory -> theory
end

structure Domain_Take_Proofs : DOMAIN_TAKE_PROOFS =
struct

type iso_info =
  {
    absT : typ,
    repT : typ,
    abs_const : term,
    rep_const : term,
    abs_inverse : thm,
    rep_inverse : thm
  }

type take_info =
  { take_consts : term list,
    take_defs : thm list,
    chain_take_thms : thm list,
    take_0_thms : thm list,
    take_Suc_thms : thm list,
    deflation_take_thms : thm list,
    take_strict_thms : thm list,
    finite_consts : term list,
    finite_defs : thm list
  }

type take_induct_info =
  {
    take_consts         : term list,
    take_defs           : thm list,
    chain_take_thms     : thm list,
    take_0_thms         : thm list,
    take_Suc_thms       : thm list,
    deflation_take_thms : thm list,
    take_strict_thms    : thm list,
    finite_consts       : term list,
    finite_defs         : thm list,
    lub_take_thms       : thm list,
    reach_thms          : thm list,
    take_lemma_thms     : thm list,
    is_finite           : bool,
    take_induct_thms    : thm list
  }

val beta_ss =
  HOL_basic_ss addsimps @{thms simp_thms} addsimprocs [@{simproc beta_cfun_proc}]

(******************************************************************************)
(******************************** theory data *********************************)
(******************************************************************************)

structure Rec_Data = Theory_Data
(
  (* list indicates which type arguments allow indirect recursion *)
  type T = (bool list) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

structure DeflMapData = Named_Thms
(
  val name = @{binding domain_deflation}
  val description = "theorems like deflation a ==> deflation (foo_map$a)"
)

structure Map_Id_Data = Named_Thms
(
  val name = @{binding domain_map_ID}
  val description = "theorems like foo_map$ID = ID"
)

fun add_rec_type (tname, bs) =
    Rec_Data.map (Symtab.insert (K true) (tname, bs))

fun add_deflation_thm thm =
    Context.theory_map (DeflMapData.add_thm thm)

val get_rec_tab = Rec_Data.get
fun get_deflation_thms thy = DeflMapData.get (Proof_Context.init_global thy)

val map_ID_add = Map_Id_Data.add
val get_map_ID_thms = Map_Id_Data.get o Proof_Context.init_global

val setup = DeflMapData.setup #> Map_Id_Data.setup

(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)

open HOLCF_Library

infixr 6 ->>
infix -->>
infix 9 `

fun mk_deflation t =
  Const (@{const_name deflation}, Term.fastype_of t --> boolT) $ t

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))

(******************************************************************************)
(****************************** isomorphism info ******************************)
(******************************************************************************)

fun deflation_abs_rep (info : iso_info) : thm =
  let
    val abs_iso = #abs_inverse info
    val rep_iso = #rep_inverse info
    val thm = @{thm deflation_abs_rep} OF [abs_iso, rep_iso]
  in
    Drule.zero_var_indexes thm
  end

(******************************************************************************)
(********************* building map functions over types **********************)
(******************************************************************************)

fun map_of_typ (thy : theory) (sub : (typ * term) list) (T : typ) : term =
  let
    val thms = get_map_ID_thms thy
    val rules = map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) thms
    val rules' = map (apfst mk_ID) sub @ map swap rules
  in
    mk_ID T
    |> Pattern.rewrite_term thy rules' []
    |> Pattern.rewrite_term thy rules []
  end

(******************************************************************************)
(********************* declaring definitions and theorems *********************)
(******************************************************************************)

fun add_qualified_def name (dbind, eqn) =
    yield_singleton (Global_Theory.add_defs false)
     ((Binding.qualified true name dbind, eqn), [])

fun add_qualified_thm name (dbind, thm) =
    yield_singleton Global_Theory.add_thms
      ((Binding.qualified true name dbind, thm), [])

fun add_qualified_simp_thm name (dbind, thm) =
    yield_singleton Global_Theory.add_thms
      ((Binding.qualified true name dbind, thm), [Simplifier.simp_add])

(******************************************************************************)
(************************** defining take functions ***************************)
(******************************************************************************)

fun define_take_functions
    (spec : (binding * iso_info) list)
    (thy : theory) =
  let

    (* retrieve components of spec *)
    val dbinds = map fst spec
    val iso_infos = map snd spec
    val dom_eqns = map (fn x => (#absT x, #repT x)) iso_infos
    val rep_abs_consts = map (fn x => (#rep_const x, #abs_const x)) iso_infos

    fun mk_projs []      _ = []
      | mk_projs (x::[]) t = [(x, t)]
      | mk_projs (x::xs) t = (x, mk_fst t) :: mk_projs xs (mk_snd t)

    fun mk_cfcomp2 ((rep_const, abs_const), f) =
        mk_cfcomp (abs_const, mk_cfcomp (f, rep_const))

    (* define take functional *)
    val newTs : typ list = map fst dom_eqns
    val copy_arg_type = mk_tupleT (map (fn T => T ->> T) newTs)
    val copy_arg = Free ("f", copy_arg_type)
    val copy_args = map snd (mk_projs dbinds copy_arg)
    fun one_copy_rhs (rep_abs, (_, rhsT)) =
      let
        val body = map_of_typ thy (newTs ~~ copy_args) rhsT
      in
        mk_cfcomp2 (rep_abs, body)
      end
    val take_functional =
        big_lambda copy_arg
          (mk_tuple (map one_copy_rhs (rep_abs_consts ~~ dom_eqns)))
    val take_rhss =
      let
        val n = Free ("n", HOLogic.natT)
        val rhs = mk_iterate (n, take_functional)
      in
        map (lambda n o snd) (mk_projs dbinds rhs)
      end

    (* define take constants *)
    fun define_take_const ((dbind, take_rhs), (lhsT, _)) thy =
      let
        val take_type = HOLogic.natT --> lhsT ->> lhsT
        val take_bind = Binding.suffix_name "_take" dbind
        val (take_const, thy) =
          Sign.declare_const_global ((take_bind, take_type), NoSyn) thy
        val take_eqn = Logic.mk_equals (take_const, take_rhs)
        val (take_def_thm, thy) =
            add_qualified_def "take_def" (dbind, take_eqn) thy
      in ((take_const, take_def_thm), thy) end
    val ((take_consts, take_defs), thy) = thy
      |> fold_map define_take_const (dbinds ~~ take_rhss ~~ dom_eqns)
      |>> ListPair.unzip

    (* prove chain_take lemmas *)
    fun prove_chain_take (take_const, dbind) thy =
      let
        val goal = mk_trp (mk_chain take_const)
        val rules = take_defs @ @{thms chain_iterate ch2ch_fst ch2ch_snd}
        val tac = simp_tac (HOL_basic_ss addsimps rules) 1
        val thm = Goal.prove_global thy [] [] goal (K tac)
      in
        add_qualified_simp_thm "chain_take" (dbind, thm) thy
      end
    val (chain_take_thms, thy) =
      fold_map prove_chain_take (take_consts ~~ dbinds) thy

    (* prove take_0 lemmas *)
    fun prove_take_0 ((take_const, dbind), (lhsT, _)) thy =
      let
        val lhs = take_const $ @{term "0::nat"}
        val goal = mk_eqs (lhs, mk_bottom (lhsT ->> lhsT))
        val rules = take_defs @ @{thms iterate_0 fst_strict snd_strict}
        val tac = simp_tac (HOL_basic_ss addsimps rules) 1
        val take_0_thm = Goal.prove_global thy [] [] goal (K tac)
      in
        add_qualified_simp_thm "take_0" (dbind, take_0_thm) thy
      end
    val (take_0_thms, thy) =
      fold_map prove_take_0 (take_consts ~~ dbinds ~~ dom_eqns) thy

    (* prove take_Suc lemmas *)
    val n = Free ("n", natT)
    val take_is = map (fn t => t $ n) take_consts
    fun prove_take_Suc
          (((take_const, rep_abs), dbind), (_, rhsT)) thy =
      let
        val lhs = take_const $ (@{term Suc} $ n)
        val body = map_of_typ thy (newTs ~~ take_is) rhsT
        val rhs = mk_cfcomp2 (rep_abs, body)
        val goal = mk_eqs (lhs, rhs)
        val simps = @{thms iterate_Suc fst_conv snd_conv}
        val rules = take_defs @ simps
        val tac = simp_tac (beta_ss addsimps rules) 1
        val take_Suc_thm = Goal.prove_global thy [] [] goal (K tac)
      in
        add_qualified_thm "take_Suc" (dbind, take_Suc_thm) thy
      end
    val (take_Suc_thms, thy) =
      fold_map prove_take_Suc
        (take_consts ~~ rep_abs_consts ~~ dbinds ~~ dom_eqns) thy

    (* prove deflation theorems for take functions *)
    val deflation_abs_rep_thms = map deflation_abs_rep iso_infos
    val deflation_take_thm =
      let
        val n = Free ("n", natT)
        fun mk_goal take_const = mk_deflation (take_const $ n)
        val goal = mk_trp (foldr1 mk_conj (map mk_goal take_consts))
        val bottom_rules =
          take_0_thms @ @{thms deflation_bottom simp_thms}
        val deflation_rules =
          @{thms conjI deflation_ID}
          @ deflation_abs_rep_thms
          @ get_deflation_thms thy
      in
        Goal.prove_global thy [] [] goal (fn _ =>
         EVERY
          [rtac @{thm nat.induct} 1,
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           asm_simp_tac (HOL_basic_ss addsimps take_Suc_thms) 1,
           REPEAT (etac @{thm conjE} 1
                   ORELSE resolve_tac deflation_rules 1
                   ORELSE atac 1)])
      end
    fun conjuncts [] _ = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1}
          val thmR = thm RS @{thm conjunct2}
        in (n, thmL):: conjuncts ns thmR end
    val (deflation_take_thms, thy) =
      fold_map (add_qualified_thm "deflation_take")
        (map (apsnd Drule.zero_var_indexes)
          (conjuncts dbinds deflation_take_thm)) thy

    (* prove strictness of take functions *)
    fun prove_take_strict (deflation_take, dbind) thy =
      let
        val take_strict_thm =
            Drule.zero_var_indexes
              (@{thm deflation_strict} OF [deflation_take])
      in
        add_qualified_simp_thm "take_strict" (dbind, take_strict_thm) thy
      end
    val (take_strict_thms, thy) =
      fold_map prove_take_strict
        (deflation_take_thms ~~ dbinds) thy

    (* prove take/take rules *)
    fun prove_take_take ((chain_take, deflation_take), dbind) thy =
      let
        val take_take_thm =
            Drule.zero_var_indexes
              (@{thm deflation_chain_min} OF [chain_take, deflation_take])
      in
        add_qualified_thm "take_take" (dbind, take_take_thm) thy
      end
    val (_, thy) =
      fold_map prove_take_take
        (chain_take_thms ~~ deflation_take_thms ~~ dbinds) thy

    (* prove take_below rules *)
    fun prove_take_below (deflation_take, dbind) thy =
      let
        val take_below_thm =
            Drule.zero_var_indexes
              (@{thm deflation.below} OF [deflation_take])
      in
        add_qualified_thm "take_below" (dbind, take_below_thm) thy
      end
    val (_, thy) =
      fold_map prove_take_below
        (deflation_take_thms ~~ dbinds) thy

    (* define finiteness predicates *)
    fun define_finite_const ((dbind, take_const), (lhsT, _)) thy =
      let
        val finite_type = lhsT --> boolT
        val finite_bind = Binding.suffix_name "_finite" dbind
        val (finite_const, thy) =
          Sign.declare_const_global ((finite_bind, finite_type), NoSyn) thy
        val x = Free ("x", lhsT)
        val n = Free ("n", natT)
        val finite_rhs =
          lambda x (HOLogic.exists_const natT $
            (lambda n (mk_eq (mk_capply (take_const $ n, x), x))))
        val finite_eqn = Logic.mk_equals (finite_const, finite_rhs)
        val (finite_def_thm, thy) =
            add_qualified_def "finite_def" (dbind, finite_eqn) thy
      in ((finite_const, finite_def_thm), thy) end
    val ((finite_consts, finite_defs), thy) = thy
      |> fold_map define_finite_const (dbinds ~~ take_consts ~~ dom_eqns)
      |>> ListPair.unzip

    val result =
      {
        take_consts = take_consts,
        take_defs = take_defs,
        chain_take_thms = chain_take_thms,
        take_0_thms = take_0_thms,
        take_Suc_thms = take_Suc_thms,
        deflation_take_thms = deflation_take_thms,
        take_strict_thms = take_strict_thms,
        finite_consts = finite_consts,
        finite_defs = finite_defs
      }

  in
    (result, thy)
  end

fun prove_finite_take_induct
    (spec : (binding * iso_info) list)
    (take_info : take_info)
    (lub_take_thms : thm list)
    (thy : theory) =
  let
    val dbinds = map fst spec
    val iso_infos = map snd spec
    val absTs = map #absT iso_infos
    val {take_consts, ...} = take_info
    val {chain_take_thms, take_0_thms, take_Suc_thms, ...} = take_info
    val {finite_consts, finite_defs, ...} = take_info

    val decisive_lemma =
      let
        fun iso_locale (info : iso_info) =
            @{thm iso.intro} OF [#abs_inverse info, #rep_inverse info]
        val iso_locale_thms = map iso_locale iso_infos
        val decisive_abs_rep_thms =
            map (fn x => @{thm decisive_abs_rep} OF [x]) iso_locale_thms
        val n = Free ("n", @{typ nat})
        fun mk_decisive t =
            Const (@{const_name decisive}, fastype_of t --> boolT) $ t
        fun f take_const = mk_decisive (take_const $ n)
        val goal = mk_trp (foldr1 mk_conj (map f take_consts))
        val rules0 = @{thm decisive_bottom} :: take_0_thms
        val rules1 =
            take_Suc_thms @ decisive_abs_rep_thms
            @ @{thms decisive_ID decisive_ssum_map decisive_sprod_map}
        val tac = EVERY [
            rtac @{thm nat.induct} 1,
            simp_tac (HOL_ss addsimps rules0) 1,
            asm_simp_tac (HOL_ss addsimps rules1) 1]
      in Goal.prove_global thy [] [] goal (K tac) end
    fun conjuncts 1 thm = [thm]
      | conjuncts n thm = let
          val thmL = thm RS @{thm conjunct1}
          val thmR = thm RS @{thm conjunct2}
        in thmL :: conjuncts (n-1) thmR end
    val decisive_thms = conjuncts (length spec) decisive_lemma

    fun prove_finite_thm (absT, finite_const) =
      let
        val goal = mk_trp (finite_const $ Free ("x", absT))
        val tac =
            EVERY [
            rewrite_goals_tac finite_defs,
            rtac @{thm lub_ID_finite} 1,
            resolve_tac chain_take_thms 1,
            resolve_tac lub_take_thms 1,
            resolve_tac decisive_thms 1]
      in
        Goal.prove_global thy [] [] goal (K tac)
      end
    val finite_thms =
        map prove_finite_thm (absTs ~~ finite_consts)

    fun prove_take_induct ((ch_take, lub_take), decisive) =
        Drule.export_without_context
          (@{thm lub_ID_finite_take_induct} OF [ch_take, lub_take, decisive])
    val take_induct_thms =
        map prove_take_induct
          (chain_take_thms ~~ lub_take_thms ~~ decisive_thms)

    val thy = thy
        |> fold (snd oo add_qualified_thm "finite")
            (dbinds ~~ finite_thms)
        |> fold (snd oo add_qualified_thm "take_induct")
            (dbinds ~~ take_induct_thms)
  in
    ((finite_thms, take_induct_thms), thy)
  end

fun add_lub_take_theorems
    (spec : (binding * iso_info) list)
    (take_info : take_info)
    (lub_take_thms : thm list)
    (thy : theory) =
  let

    (* retrieve components of spec *)
    val dbinds = map fst spec
    val iso_infos = map snd spec
    val absTs = map #absT iso_infos
    val repTs = map #repT iso_infos
    val {chain_take_thms, ...} = take_info

    (* prove take lemmas *)
    fun prove_take_lemma ((chain_take, lub_take), dbind) thy =
      let
        val take_lemma =
            Drule.export_without_context
              (@{thm lub_ID_take_lemma} OF [chain_take, lub_take])
      in
        add_qualified_thm "take_lemma" (dbind, take_lemma) thy
      end
    val (take_lemma_thms, thy) =
      fold_map prove_take_lemma
        (chain_take_thms ~~ lub_take_thms ~~ dbinds) thy

    (* prove reach lemmas *)
    fun prove_reach_lemma ((chain_take, lub_take), dbind) thy =
      let
        val thm =
            Drule.zero_var_indexes
              (@{thm lub_ID_reach} OF [chain_take, lub_take])
      in
        add_qualified_thm "reach" (dbind, thm) thy
      end
    val (reach_thms, thy) =
      fold_map prove_reach_lemma
        (chain_take_thms ~~ lub_take_thms ~~ dbinds) thy

    (* test for finiteness of domain definitions *)
    local
      val types = [@{type_name ssum}, @{type_name sprod}]
      fun finite d T = if member (op =) absTs T then d else finite' d T
      and finite' d (Type (c, Ts)) =
          let val d' = d andalso member (op =) types c
          in forall (finite d') Ts end
        | finite' _ _ = true
    in
      val is_finite = forall (finite true) repTs
    end

    val ((_, take_induct_thms), thy) =
      if is_finite
      then
        let
          val ((finites, take_inducts), thy) =
              prove_finite_take_induct spec take_info lub_take_thms thy
        in
          ((SOME finites, take_inducts), thy)
        end
      else
        let
          fun prove_take_induct (chain_take, lub_take) =
              Drule.zero_var_indexes
                (@{thm lub_ID_take_induct} OF [chain_take, lub_take])
          val take_inducts =
              map prove_take_induct (chain_take_thms ~~ lub_take_thms)
          val thy = fold (snd oo add_qualified_thm "take_induct")
                         (dbinds ~~ take_inducts) thy
        in
          ((NONE, take_inducts), thy)
        end

    val result =
      {
        take_consts         = #take_consts take_info,
        take_defs           = #take_defs take_info,
        chain_take_thms     = #chain_take_thms take_info,
        take_0_thms         = #take_0_thms take_info,
        take_Suc_thms       = #take_Suc_thms take_info,
        deflation_take_thms = #deflation_take_thms take_info,
        take_strict_thms    = #take_strict_thms take_info,
        finite_consts       = #finite_consts take_info,
        finite_defs         = #finite_defs take_info,
        lub_take_thms       = lub_take_thms,
        reach_thms          = reach_thms,
        take_lemma_thms     = take_lemma_thms,
        is_finite           = is_finite,
        take_induct_thms    = take_induct_thms
      }
  in
    (result, thy)
  end

end
