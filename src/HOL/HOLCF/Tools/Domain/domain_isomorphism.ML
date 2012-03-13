(*  Title:      HOL/HOLCF/Tools/Domain/domain_isomorphism.ML
    Author:     Brian Huffman

Defines new types satisfying the given domain equations.
*)

signature DOMAIN_ISOMORPHISM =
sig
  val domain_isomorphism :
      (string list * binding * mixfix * typ
       * (binding * binding) option) list ->
      theory ->
      (Domain_Take_Proofs.iso_info list
       * Domain_Take_Proofs.take_induct_info) * theory

  val define_map_functions :
      (binding * Domain_Take_Proofs.iso_info) list ->
      theory ->
      {
        map_consts : term list,
        map_apply_thms : thm list,
        map_unfold_thms : thm list,
        map_cont_thm : thm,
        deflation_map_thms : thm list
      }
      * theory

  val domain_isomorphism_cmd :
    (string list * binding * mixfix * string * (binding * binding) option) list
      -> theory -> theory

  val setup : theory -> theory
end

structure Domain_Isomorphism : DOMAIN_ISOMORPHISM =
struct

val beta_ss =
  HOL_basic_ss addsimps @{thms simp_thms} addsimprocs [@{simproc beta_cfun_proc}]

fun is_cpo thy T = Sign.of_sort thy (T, @{sort cpo})

(******************************************************************************)
(******************************** theory data *********************************)
(******************************************************************************)

structure RepData = Named_Thms
(
  val name = @{binding domain_defl_simps}
  val description = "theorems like DEFL('a t) = t_defl$DEFL('a)"
)

structure IsodeflData = Named_Thms
(
  val name = @{binding domain_isodefl}
  val description = "theorems like isodefl d t ==> isodefl (foo_map$d) (foo_defl$t)"
)

val setup = RepData.setup #> IsodeflData.setup


(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)

open HOLCF_Library

infixr 6 ->>
infixr -->>

val udomT = @{typ udom}
val deflT = @{typ "udom defl"}
val udeflT = @{typ "udom u defl"}

fun mk_DEFL T =
  Const (@{const_name defl}, Term.itselfT T --> deflT) $ Logic.mk_type T

fun dest_DEFL (Const (@{const_name defl}, _) $ t) = Logic.dest_type t
  | dest_DEFL t = raise TERM ("dest_DEFL", [t])

fun mk_LIFTDEFL T =
  Const (@{const_name liftdefl}, Term.itselfT T --> udeflT) $ Logic.mk_type T

fun dest_LIFTDEFL (Const (@{const_name liftdefl}, _) $ t) = Logic.dest_type t
  | dest_LIFTDEFL t = raise TERM ("dest_LIFTDEFL", [t])

fun mk_u_defl t = mk_capply (@{const "u_defl"}, t)

fun emb_const T = Const (@{const_name emb}, T ->> udomT)
fun prj_const T = Const (@{const_name prj}, udomT ->> T)
fun coerce_const (T, U) = mk_cfcomp (prj_const U, emb_const T)

fun isodefl_const T =
  Const (@{const_name isodefl}, (T ->> T) --> deflT --> HOLogic.boolT)

fun isodefl'_const T =
  Const (@{const_name isodefl'}, (T ->> T) --> udeflT --> HOLogic.boolT)

fun mk_deflation t =
  Const (@{const_name deflation}, Term.fastype_of t --> boolT) $ t

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t)

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))

(******************************************************************************)
(****************************** isomorphism info ******************************)
(******************************************************************************)

fun deflation_abs_rep (info : Domain_Take_Proofs.iso_info) : thm =
  let
    val abs_iso = #abs_inverse info
    val rep_iso = #rep_inverse info
    val thm = @{thm deflation_abs_rep} OF [abs_iso, rep_iso]
  in
    Drule.zero_var_indexes thm
  end

(******************************************************************************)
(*************** fixed-point definitions and unfolding theorems ***************)
(******************************************************************************)

fun mk_projs []      _ = []
  | mk_projs (x::[]) t = [(x, t)]
  | mk_projs (x::xs) t = (x, mk_fst t) :: mk_projs xs (mk_snd t)

fun add_fixdefs
    (spec : (binding * term) list)
    (thy : theory) : (thm list * thm list * thm) * theory =
  let
    val binds = map fst spec
    val (lhss, rhss) = ListPair.unzip (map (dest_eqs o snd) spec)
    val functional = lambda_tuple lhss (mk_tuple rhss)
    val fixpoint = mk_fix (mk_cabs functional)

    (* project components of fixpoint *)
    val projs = mk_projs lhss fixpoint

    (* convert parameters to lambda abstractions *)
    fun mk_eqn (lhs, rhs) =
        case lhs of
          Const (@{const_name Rep_cfun}, _) $ f $ (x as Free _) =>
            mk_eqn (f, big_lambda x rhs)
        | f $ Const (@{const_name TYPE}, T) =>
            mk_eqn (f, Abs ("t", T, rhs))
        | Const _ => Logic.mk_equals (lhs, rhs)
        | _ => raise TERM ("lhs not of correct form", [lhs, rhs])
    val eqns = map mk_eqn projs

    (* register constant definitions *)
    val (fixdef_thms, thy) =
      (Global_Theory.add_defs false o map Thm.no_attributes)
        (map Thm.def_binding binds ~~ eqns) thy

    (* prove applied version of definitions *)
    fun prove_proj (lhs, rhs) =
      let
        val tac = rewrite_goals_tac fixdef_thms THEN (simp_tac beta_ss) 1
        val goal = Logic.mk_equals (lhs, rhs)
      in Goal.prove_global thy [] [] goal (K tac) end
    val proj_thms = map prove_proj projs

    (* mk_tuple lhss == fixpoint *)
    fun pair_equalI (thm1, thm2) = @{thm Pair_equalI} OF [thm1, thm2]
    val tuple_fixdef_thm = foldr1 pair_equalI proj_thms

    val cont_thm =
      let
        val prop = mk_trp (mk_cont functional)
        val rules = Cont2ContData.get (Proof_Context.init_global thy)
        val tac = REPEAT_ALL_NEW (match_tac rules) 1
      in
        Goal.prove_global thy [] [] prop (K tac)
      end

    val tuple_unfold_thm =
      (@{thm def_cont_fix_eq} OF [tuple_fixdef_thm, cont_thm])
      |> Local_Defs.unfold (Proof_Context.init_global thy) @{thms split_conv}

    fun mk_unfold_thms [] _ = []
      | mk_unfold_thms (n::[]) thm = [(n, thm)]
      | mk_unfold_thms (n::ns) thm = let
          val thmL = thm RS @{thm Pair_eqD1}
          val thmR = thm RS @{thm Pair_eqD2}
        in (n, thmL) :: mk_unfold_thms ns thmR end
    val unfold_binds = map (Binding.suffix_name "_unfold") binds

    (* register unfold theorems *)
    val (unfold_thms, thy) =
      (Global_Theory.add_thms o map (Thm.no_attributes o apsnd Drule.zero_var_indexes))
        (mk_unfold_thms unfold_binds tuple_unfold_thm) thy
  in
    ((proj_thms, unfold_thms, cont_thm), thy)
  end


(******************************************************************************)
(****************** deflation combinators and map functions *******************)
(******************************************************************************)

fun defl_of_typ
    (thy : theory)
    (tab1 : (typ * term) list)
    (tab2 : (typ * term) list)
    (T : typ) : term =
  let
    val defl_simps = RepData.get (Proof_Context.init_global thy)
    val rules = map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) defl_simps
    val rules' = map (apfst mk_DEFL) tab1 @ map (apfst mk_LIFTDEFL) tab2
    fun proc1 t =
      (case dest_DEFL t of
        TFree (a, _) => SOME (Free ("d" ^ Library.unprefix "'" a, deflT))
      | _ => NONE) handle TERM _ => NONE
    fun proc2 t =
      (case dest_LIFTDEFL t of
        TFree (a, _) => SOME (Free ("p" ^ Library.unprefix "'" a, udeflT))
      | _ => NONE) handle TERM _ => NONE
  in
    Pattern.rewrite_term thy (rules @ rules') [proc1, proc2] (mk_DEFL T)
  end

(******************************************************************************)
(********************* declaring definitions and theorems *********************)
(******************************************************************************)

fun define_const
    (bind : binding, rhs : term)
    (thy : theory)
    : (term * thm) * theory =
  let
    val typ = Term.fastype_of rhs
    val (const, thy) = Sign.declare_const_global ((bind, typ), NoSyn) thy
    val eqn = Logic.mk_equals (const, rhs)
    val def = Thm.no_attributes (Thm.def_binding bind, eqn)
    val (def_thm, thy) = yield_singleton (Global_Theory.add_defs false) def thy
  in
    ((const, def_thm), thy)
  end

fun add_qualified_thm name (dbind, thm) =
    yield_singleton Global_Theory.add_thms
      ((Binding.qualified true name dbind, thm), [])

(******************************************************************************)
(*************************** defining map functions ***************************)
(******************************************************************************)

fun define_map_functions
    (spec : (binding * Domain_Take_Proofs.iso_info) list)
    (thy : theory) =
  let

    (* retrieve components of spec *)
    val dbinds = map fst spec
    val iso_infos = map snd spec
    val dom_eqns = map (fn x => (#absT x, #repT x)) iso_infos
    val rep_abs_consts = map (fn x => (#rep_const x, #abs_const x)) iso_infos

    fun mapT (T as Type (_, Ts)) =
        (map (fn T => T ->> T) (filter (is_cpo thy) Ts)) -->> (T ->> T)
      | mapT T = T ->> T

    (* declare map functions *)
    fun declare_map_const (tbind, (lhsT, _)) thy =
      let
        val map_type = mapT lhsT
        val map_bind = Binding.suffix_name "_map" tbind
      in
        Sign.declare_const_global ((map_bind, map_type), NoSyn) thy
      end
    val (map_consts, thy) = thy |>
      fold_map declare_map_const (dbinds ~~ dom_eqns)

    (* defining equations for map functions *)
    local
      fun unprime a = Library.unprefix "'" a
      fun mapvar T = Free (unprime (fst (dest_TFree T)), T ->> T)
      fun map_lhs (map_const, lhsT) =
          (lhsT, list_ccomb (map_const, map mapvar (filter (is_cpo thy) (snd (dest_Type lhsT)))))
      val tab1 = map map_lhs (map_consts ~~ map fst dom_eqns)
      val Ts = (snd o dest_Type o fst o hd) dom_eqns
      val tab = (Ts ~~ map mapvar Ts) @ tab1
      fun mk_map_spec (((rep_const, abs_const), _), (lhsT, rhsT)) =
        let
          val lhs = Domain_Take_Proofs.map_of_typ thy tab lhsT
          val body = Domain_Take_Proofs.map_of_typ thy tab rhsT
          val rhs = mk_cfcomp (abs_const, mk_cfcomp (body, rep_const))
        in mk_eqs (lhs, rhs) end
    in
      val map_specs =
          map mk_map_spec (rep_abs_consts ~~ map_consts ~~ dom_eqns)
    end

    (* register recursive definition of map functions *)
    val map_binds = map (Binding.suffix_name "_map") dbinds
    val ((map_apply_thms, map_unfold_thms, map_cont_thm), thy) =
      add_fixdefs (map_binds ~~ map_specs) thy

    (* prove deflation theorems for map functions *)
    val deflation_abs_rep_thms = map deflation_abs_rep iso_infos
    val deflation_map_thm =
      let
        fun unprime a = Library.unprefix "'" a
        fun mk_f T = Free (unprime (fst (dest_TFree T)), T ->> T)
        fun mk_assm T = mk_trp (mk_deflation (mk_f T))
        fun mk_goal (map_const, (lhsT, _)) =
          let
            val (_, Ts) = dest_Type lhsT
            val map_term = list_ccomb (map_const, map mk_f (filter (is_cpo thy) Ts))
          in mk_deflation map_term end
        val assms = (map mk_assm o filter (is_cpo thy) o snd o dest_Type o fst o hd) dom_eqns
        val goals = map mk_goal (map_consts ~~ dom_eqns)
        val goal = mk_trp (foldr1 HOLogic.mk_conj goals)
        val adm_rules =
          @{thms adm_conj adm_subst [OF _ adm_deflation]
                 cont2cont_fst cont2cont_snd cont_id}
        val bottom_rules =
          @{thms fst_strict snd_strict deflation_bottom simp_thms}
        val tuple_rules =
          @{thms split_def fst_conv snd_conv}
        val deflation_rules =
          @{thms conjI deflation_ID}
          @ deflation_abs_rep_thms
          @ Domain_Take_Proofs.get_deflation_thms thy
      in
        Goal.prove_global thy [] assms goal (fn {prems, ...} =>
         EVERY
          [rewrite_goals_tac map_apply_thms,
           rtac (map_cont_thm RS @{thm cont_fix_ind}) 1,
           REPEAT (resolve_tac adm_rules 1),
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           simp_tac (HOL_basic_ss addsimps tuple_rules) 1,
           REPEAT (etac @{thm conjE} 1),
           REPEAT (resolve_tac (deflation_rules @ prems) 1 ORELSE atac 1)])
      end
    fun conjuncts [] _ = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1}
          val thmR = thm RS @{thm conjunct2}
        in (n, thmL):: conjuncts ns thmR end
    val deflation_map_binds = dbinds |>
        map (Binding.prefix_name "deflation_" o Binding.suffix_name "_map")
    val (deflation_map_thms, thy) = thy |>
      (Global_Theory.add_thms o map (Thm.no_attributes o apsnd Drule.zero_var_indexes))
        (conjuncts deflation_map_binds deflation_map_thm)

    (* register indirect recursion in theory data *)
    local
      fun register_map (dname, args) =
        Domain_Take_Proofs.add_rec_type (dname, args)
      val dnames = map (fst o dest_Type o fst) dom_eqns
      fun args (T, _) = case T of Type (_, Ts) => map (is_cpo thy) Ts | _ => []
      val argss = map args dom_eqns
    in
      val thy =
          fold register_map (dnames ~~ argss) thy
    end

    (* register deflation theorems *)
    val thy = fold Domain_Take_Proofs.add_deflation_thm deflation_map_thms thy

    val result =
      {
        map_consts = map_consts,
        map_apply_thms = map_apply_thms,
        map_unfold_thms = map_unfold_thms,
        map_cont_thm = map_cont_thm,
        deflation_map_thms = deflation_map_thms
      }
  in
    (result, thy)
  end

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun read_typ thy str sorts =
  let
    val ctxt = Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) sorts
    val T = Syntax.read_typ ctxt str
  in (T, Term.add_tfreesT T sorts) end

fun cert_typ sign raw_T sorts =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T)
      handle TYPE (msg, _, _) => error msg
    val sorts' = Term.add_tfreesT T sorts
    val _ =
      case duplicates (op =) (map fst sorts') of
        [] => ()
      | dups => error ("Inconsistent sort constraints for " ^ commas dups)
  in (T, sorts') end

fun gen_domain_isomorphism
    (prep_typ: theory -> 'a -> (string * sort) list -> typ * (string * sort) list)
    (doms_raw: (string list * binding * mixfix * 'a * (binding * binding) option) list)
    (thy: theory)
    : (Domain_Take_Proofs.iso_info list
       * Domain_Take_Proofs.take_induct_info) * theory =
  let
    val _ = Theory.requires thy "Domain" "domain isomorphisms"

    (* this theory is used just for parsing *)
    val tmp_thy = thy |>
      Theory.copy |>
      Sign.add_types_global (map (fn (tvs, tbind, mx, _, _) =>
        (tbind, length tvs, mx)) doms_raw)

    fun prep_dom thy (vs, t, mx, typ_raw, morphs) sorts =
      let val (typ, sorts') = prep_typ thy typ_raw sorts
      in ((vs, t, mx, typ, morphs), sorts') end

    val (doms : (string list * binding * mixfix * typ * (binding * binding) option) list,
         sorts : (string * sort) list) =
      fold_map (prep_dom tmp_thy) doms_raw []

    (* lookup function for sorts of type variables *)
    fun the_sort v = the (AList.lookup (op =) sorts v)

    (* declare arities in temporary theory *)
    val tmp_thy =
      let
        fun arity (vs, tbind, _, _, _) =
          (Sign.full_name thy tbind, map the_sort vs, @{sort "domain"})
      in
        fold AxClass.axiomatize_arity (map arity doms) tmp_thy
      end

    (* check bifiniteness of right-hand sides *)
    fun check_rhs (_, _, _, rhs, _) =
      if Sign.of_sort tmp_thy (rhs, @{sort "domain"}) then ()
      else error ("Type not of sort domain: " ^
        quote (Syntax.string_of_typ_global tmp_thy rhs))
    val _ = map check_rhs doms

    (* domain equations *)
    fun mk_dom_eqn (vs, tbind, _, rhs, _) =
      let fun arg v = TFree (v, the_sort v)
      in (Type (Sign.full_name tmp_thy tbind, map arg vs), rhs) end
    val dom_eqns = map mk_dom_eqn doms

    (* check for valid type parameters *)
    val (tyvars, _, _, _, _) = hd doms
    val _ = map (fn (tvs, tname, _, _, _) =>
      let val full_tname = Sign.full_name tmp_thy tname
      in
        (case duplicates (op =) tvs of
          [] =>
            if eq_set (op =) (tyvars, tvs) then (full_tname, tvs)
            else error ("Mutually recursive domains must have same type parameters")
        | dups => error ("Duplicate parameter(s) for domain " ^ Binding.print tname ^
            " : " ^ commas dups))
      end) doms
    val dbinds = map (fn (_, dbind, _, _, _) => dbind) doms
    val morphs = map (fn (_, _, _, _, morphs) => morphs) doms

    (* determine deflation combinator arguments *)
    val lhsTs : typ list = map fst dom_eqns
    val defl_rec = Free ("t", mk_tupleT (map (K deflT) lhsTs))
    val defl_recs = mk_projs lhsTs defl_rec
    val defl_recs' = map (apsnd mk_u_defl) defl_recs
    fun defl_body (_, _, _, rhsT, _) =
      defl_of_typ tmp_thy defl_recs defl_recs' rhsT
    val functional = Term.lambda defl_rec (mk_tuple (map defl_body doms))

    val tfrees = map fst (Term.add_tfrees functional [])
    val frees = map fst (Term.add_frees functional [])
    fun get_defl_flags (vs, _, _, _, _) =
      let
        fun argT v = TFree (v, the_sort v)
        fun mk_d v = "d" ^ Library.unprefix "'" v
        fun mk_p v = "p" ^ Library.unprefix "'" v
        val args = maps (fn v => [(mk_d v, mk_DEFL (argT v)), (mk_p v, mk_LIFTDEFL (argT v))]) vs
        val typeTs = map argT (filter (member (op =) tfrees) vs)
        val defl_args = map snd (filter (member (op =) frees o fst) args)
      in
        (typeTs, defl_args)
      end
    val defl_flagss = map get_defl_flags doms

    (* declare deflation combinator constants *)
    fun declare_defl_const ((typeTs, defl_args), (_, tbind, _, _, _)) thy =
      let
        val defl_bind = Binding.suffix_name "_defl" tbind
        val defl_type =
          map Term.itselfT typeTs ---> map fastype_of defl_args -->> deflT
      in
        Sign.declare_const_global ((defl_bind, defl_type), NoSyn) thy
      end
    val (defl_consts, thy) =
      fold_map declare_defl_const (defl_flagss ~~ doms) thy

    (* defining equations for type combinators *)
    fun mk_defl_term (defl_const, (typeTs, defl_args)) =
      let
        val type_args = map Logic.mk_type typeTs
      in
        list_ccomb (list_comb (defl_const, type_args), defl_args)
      end
    val defl_terms = map mk_defl_term (defl_consts ~~ defl_flagss)
    val defl_tab = map fst dom_eqns ~~ defl_terms
    val defl_tab' = map fst dom_eqns ~~ map mk_u_defl defl_terms
    fun mk_defl_spec (lhsT, rhsT) =
      mk_eqs (defl_of_typ tmp_thy defl_tab defl_tab' lhsT,
              defl_of_typ tmp_thy defl_tab defl_tab' rhsT)
    val defl_specs = map mk_defl_spec dom_eqns

    (* register recursive definition of deflation combinators *)
    val defl_binds = map (Binding.suffix_name "_defl") dbinds
    val ((defl_apply_thms, defl_unfold_thms, defl_cont_thm), thy) =
      add_fixdefs (defl_binds ~~ defl_specs) thy

    (* define types using deflation combinators *)
    fun make_repdef ((vs, tbind, mx, _, _), defl) thy =
      let
        val spec = (tbind, map (rpair dummyS) vs, mx)
        val ((_, _, _, {DEFL, ...}), thy) =
          Domaindef.add_domaindef false NONE spec defl NONE thy
        (* declare domain_defl_simps rules *)
        val thy = Context.theory_map (RepData.add_thm DEFL) thy
      in
        (DEFL, thy)
      end
    val (DEFL_thms, thy) = fold_map make_repdef (doms ~~ defl_terms) thy

    (* prove DEFL equations *)
    fun mk_DEFL_eq_thm (lhsT, rhsT) =
      let
        val goal = mk_eqs (mk_DEFL lhsT, mk_DEFL rhsT)
        val DEFL_simps = RepData.get (Proof_Context.init_global thy)
        val tac =
          rewrite_goals_tac (map mk_meta_eq DEFL_simps)
          THEN TRY (resolve_tac defl_unfold_thms 1)
      in
        Goal.prove_global thy [] [] goal (K tac)
      end
    val DEFL_eq_thms = map mk_DEFL_eq_thm dom_eqns

    (* register DEFL equations *)
    val DEFL_eq_binds = map (Binding.prefix_name "DEFL_eq_") dbinds
    val (_, thy) = thy |>
      (Global_Theory.add_thms o map Thm.no_attributes)
        (DEFL_eq_binds ~~ DEFL_eq_thms)

    (* define rep/abs functions *)
    fun mk_rep_abs ((tbind, _), (lhsT, rhsT)) thy =
      let
        val rep_bind = Binding.suffix_name "_rep" tbind
        val abs_bind = Binding.suffix_name "_abs" tbind
        val ((rep_const, rep_def), thy) =
            define_const (rep_bind, coerce_const (lhsT, rhsT)) thy
        val ((abs_const, abs_def), thy) =
            define_const (abs_bind, coerce_const (rhsT, lhsT)) thy
      in
        (((rep_const, abs_const), (rep_def, abs_def)), thy)
      end
    val ((rep_abs_consts, rep_abs_defs), thy) = thy
      |> fold_map mk_rep_abs (dbinds ~~ morphs ~~ dom_eqns)
      |>> ListPair.unzip

    (* prove isomorphism and isodefl rules *)
    fun mk_iso_thms ((tbind, DEFL_eq), (rep_def, abs_def)) thy =
      let
        fun make thm =
            Drule.zero_var_indexes (thm OF [DEFL_eq, abs_def, rep_def])
        val rep_iso_thm = make @{thm domain_rep_iso}
        val abs_iso_thm = make @{thm domain_abs_iso}
        val isodefl_thm = make @{thm isodefl_abs_rep}
        val thy = thy
          |> snd o add_qualified_thm "rep_iso" (tbind, rep_iso_thm)
          |> snd o add_qualified_thm "abs_iso" (tbind, abs_iso_thm)
          |> snd o add_qualified_thm "isodefl_abs_rep" (tbind, isodefl_thm)
      in
        (((rep_iso_thm, abs_iso_thm), isodefl_thm), thy)
      end
    val ((iso_thms, isodefl_abs_rep_thms), thy) =
      thy
      |> fold_map mk_iso_thms (dbinds ~~ DEFL_eq_thms ~~ rep_abs_defs)
      |>> ListPair.unzip

    (* collect info about rep/abs *)
    val iso_infos : Domain_Take_Proofs.iso_info list =
      let
        fun mk_info (((lhsT, rhsT), (repC, absC)), (rep_iso, abs_iso)) =
          {
            repT = rhsT,
            absT = lhsT,
            rep_const = repC,
            abs_const = absC,
            rep_inverse = rep_iso,
            abs_inverse = abs_iso
          }
      in
        map mk_info (dom_eqns ~~ rep_abs_consts ~~ iso_thms)
      end

    (* definitions and proofs related to map functions *)
    val (map_info, thy) =
        define_map_functions (dbinds ~~ iso_infos) thy
    val { map_consts, map_apply_thms, map_cont_thm, ...} = map_info

    (* prove isodefl rules for map functions *)
    val isodefl_thm =
      let
        fun unprime a = Library.unprefix "'" a
        fun mk_d T = Free ("d" ^ unprime (fst (dest_TFree T)), deflT)
        fun mk_p T = Free ("p" ^ unprime (fst (dest_TFree T)), udeflT)
        fun mk_f T = Free ("f" ^ unprime (fst (dest_TFree T)), T ->> T)
        fun mk_assm t =
          case try dest_LIFTDEFL t of
            SOME T => mk_trp (isodefl'_const T $ mk_f T $ mk_p T)
          | NONE =>
            let val T = dest_DEFL t
            in mk_trp (isodefl_const T $ mk_f T $ mk_d T) end
        fun mk_goal (map_const, (T, _)) =
          let
            val (_, Ts) = dest_Type T
            val map_term = list_ccomb (map_const, map mk_f (filter (is_cpo thy) Ts))
            val defl_term = defl_of_typ thy (Ts ~~ map mk_d Ts) (Ts ~~ map mk_p Ts) T
          in isodefl_const T $ map_term $ defl_term end
        val assms = (map mk_assm o snd o hd) defl_flagss
        val goals = map mk_goal (map_consts ~~ dom_eqns)
        val goal = mk_trp (foldr1 HOLogic.mk_conj goals)
        val adm_rules =
          @{thms adm_conj adm_isodefl cont2cont_fst cont2cont_snd cont_id}
        val bottom_rules =
          @{thms fst_strict snd_strict isodefl_bottom simp_thms}
        val tuple_rules =
          @{thms split_def fst_conv snd_conv}
        val map_ID_thms = Domain_Take_Proofs.get_map_ID_thms thy
        val map_ID_simps = map (fn th => th RS sym) map_ID_thms
        val isodefl_rules =
          @{thms conjI isodefl_ID_DEFL isodefl_LIFTDEFL}
          @ isodefl_abs_rep_thms
          @ IsodeflData.get (Proof_Context.init_global thy)
      in
        Goal.prove_global thy [] assms goal (fn {prems, ...} =>
         EVERY
          [rewrite_goals_tac (defl_apply_thms @ map_apply_thms),
           rtac (@{thm cont_parallel_fix_ind}
             OF [defl_cont_thm, map_cont_thm]) 1,
           REPEAT (resolve_tac adm_rules 1),
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           simp_tac (HOL_basic_ss addsimps tuple_rules) 1,
           simp_tac (HOL_basic_ss addsimps map_ID_simps) 1,
           REPEAT (etac @{thm conjE} 1),
           REPEAT (resolve_tac (isodefl_rules @ prems) 1 ORELSE atac 1)])
      end
    val isodefl_binds = map (Binding.prefix_name "isodefl_") dbinds
    fun conjuncts [] _ = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1}
          val thmR = thm RS @{thm conjunct2}
        in (n, thmL):: conjuncts ns thmR end
    val (isodefl_thms, thy) = thy |>
      (Global_Theory.add_thms o map (Thm.no_attributes o apsnd Drule.zero_var_indexes))
        (conjuncts isodefl_binds isodefl_thm)
    val thy = fold (Context.theory_map o IsodeflData.add_thm) isodefl_thms thy

    (* prove map_ID theorems *)
    fun prove_map_ID_thm
        (((map_const, (lhsT, _)), DEFL_thm), isodefl_thm) =
      let
        val Ts = snd (dest_Type lhsT)
        fun is_cpo T = Sign.of_sort thy (T, @{sort cpo})
        val lhs = list_ccomb (map_const, map mk_ID (filter is_cpo Ts))
        val goal = mk_eqs (lhs, mk_ID lhsT)
        val tac = EVERY
          [rtac @{thm isodefl_DEFL_imp_ID} 1,
           stac DEFL_thm 1,
           rtac isodefl_thm 1,
           REPEAT (resolve_tac @{thms isodefl_ID_DEFL isodefl_LIFTDEFL} 1)]
      in
        Goal.prove_global thy [] [] goal (K tac)
      end
    val map_ID_binds = map (Binding.suffix_name "_map_ID") dbinds
    val map_ID_thms =
      map prove_map_ID_thm
        (map_consts ~~ dom_eqns ~~ DEFL_thms ~~ isodefl_thms)
    val (_, thy) = thy |>
      (Global_Theory.add_thms o map (rpair [Domain_Take_Proofs.map_ID_add]))
        (map_ID_binds ~~ map_ID_thms)

    (* definitions and proofs related to take functions *)
    val (take_info, thy) =
        Domain_Take_Proofs.define_take_functions
          (dbinds ~~ iso_infos) thy
    val { take_consts, chain_take_thms, take_0_thms, take_Suc_thms, ...} =
        take_info

    (* least-upper-bound lemma for take functions *)
    val lub_take_lemma =
      let
        val lhs = mk_tuple (map mk_lub take_consts)
        fun is_cpo T = Sign.of_sort thy (T, @{sort cpo})
        fun mk_map_ID (map_const, (lhsT, _)) =
          list_ccomb (map_const, map mk_ID (filter is_cpo (snd (dest_Type lhsT))))
        val rhs = mk_tuple (map mk_map_ID (map_consts ~~ dom_eqns))
        val goal = mk_trp (mk_eq (lhs, rhs))
        val map_ID_thms = Domain_Take_Proofs.get_map_ID_thms thy
        val start_rules =
            @{thms lub_Pair [symmetric] ch2ch_Pair} @ chain_take_thms
            @ @{thms pair_collapse split_def}
            @ map_apply_thms @ map_ID_thms
        val rules0 =
            @{thms iterate_0 Pair_strict} @ take_0_thms
        val rules1 =
            @{thms iterate_Suc prod_eq_iff fst_conv snd_conv}
            @ take_Suc_thms
        val tac =
            EVERY
            [simp_tac (HOL_basic_ss addsimps start_rules) 1,
             simp_tac (HOL_basic_ss addsimps @{thms fix_def2}) 1,
             rtac @{thm lub_eq} 1,
             rtac @{thm nat.induct} 1,
             simp_tac (HOL_basic_ss addsimps rules0) 1,
             asm_full_simp_tac (beta_ss addsimps rules1) 1]
      in
        Goal.prove_global thy [] [] goal (K tac)
      end

    (* prove lub of take equals ID *)
    fun prove_lub_take (((dbind, take_const), map_ID_thm), (lhsT, _)) thy =
      let
        val n = Free ("n", natT)
        val goal = mk_eqs (mk_lub (lambda n (take_const $ n)), mk_ID lhsT)
        val tac =
            EVERY
            [rtac @{thm trans} 1, rtac map_ID_thm 2,
             cut_tac lub_take_lemma 1,
             REPEAT (etac @{thm Pair_inject} 1), atac 1]
        val lub_take_thm = Goal.prove_global thy [] [] goal (K tac)
      in
        add_qualified_thm "lub_take" (dbind, lub_take_thm) thy
      end
    val (lub_take_thms, thy) =
        fold_map prove_lub_take
          (dbinds ~~ take_consts ~~ map_ID_thms ~~ dom_eqns) thy

    (* prove additional take theorems *)
    val (take_info2, thy) =
        Domain_Take_Proofs.add_lub_take_theorems
          (dbinds ~~ iso_infos) take_info lub_take_thms thy
  in
    ((iso_infos, take_info2), thy)
  end

val domain_isomorphism = gen_domain_isomorphism cert_typ
val domain_isomorphism_cmd = snd oo gen_domain_isomorphism read_typ

(******************************************************************************)
(******************************** outer syntax ********************************)
(******************************************************************************)

local

val parse_domain_iso :
    (string list * binding * mixfix * string * (binding * binding) option)
      parser =
  (Parse.type_args -- Parse.binding -- Parse.opt_mixfix -- (Parse.$$$ "=" |-- Parse.typ) --
    Scan.option (Parse.$$$ "morphisms" |-- Parse.!!! (Parse.binding -- Parse.binding)))
    >> (fn ((((vs, t), mx), rhs), morphs) => (vs, t, mx, rhs, morphs))

val parse_domain_isos = Parse.and_list1 parse_domain_iso

in

val _ =
  Outer_Syntax.command "domain_isomorphism" "define domain isomorphisms (HOLCF)"
    Keyword.thy_decl
    (parse_domain_isos >> (Toplevel.theory o domain_isomorphism_cmd))

end

end
