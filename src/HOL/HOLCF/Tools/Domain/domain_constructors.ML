(*  Title:      HOL/HOLCF/Tools/Domain/domain_constructors.ML
    Author:     Brian Huffman

Defines constructor functions for a given domain isomorphism
and proves related theorems.
*)

signature DOMAIN_CONSTRUCTORS =
sig
  type constr_info =
    {
      iso_info : Domain_Take_Proofs.iso_info,
      con_specs : (term * (bool * typ) list) list,
      con_betas : thm list,
      nchotomy : thm,
      exhaust : thm,
      compacts : thm list,
      con_rews : thm list,
      inverts : thm list,
      injects : thm list,
      dist_les : thm list,
      dist_eqs : thm list,
      cases : thm list,
      sel_rews : thm list,
      dis_rews : thm list,
      match_rews : thm list
    }
  val add_domain_constructors :
      binding
      -> (binding * (bool * binding option * typ) list * mixfix) list
      -> Domain_Take_Proofs.iso_info
      -> theory
      -> constr_info * theory
end


structure Domain_Constructors : DOMAIN_CONSTRUCTORS =
struct

open HOLCF_Library

infixr 6 ->>
infix -->>
infix 9 `

type constr_info =
  {
    iso_info : Domain_Take_Proofs.iso_info,
    con_specs : (term * (bool * typ) list) list,
    con_betas : thm list,
    nchotomy : thm,
    exhaust : thm,
    compacts : thm list,
    con_rews : thm list,
    inverts : thm list,
    injects : thm list,
    dist_les : thm list,
    dist_eqs : thm list,
    cases : thm list,
    sel_rews : thm list,
    dis_rews : thm list,
    match_rews : thm list
  }

(************************** miscellaneous functions ***************************)

val simple_ss = HOL_basic_ss addsimps @{thms simp_thms}

val beta_rules =
  @{thms beta_cfun cont_id cont_const cont2cont_APP cont2cont_LAM'} @
  @{thms cont2cont_fst cont2cont_snd cont2cont_Pair}

val beta_ss = HOL_basic_ss addsimps (@{thms simp_thms} @ beta_rules)

fun define_consts
    (specs : (binding * term * mixfix) list)
    (thy : theory)
    : (term list * thm list) * theory =
  let
    fun mk_decl (b, t, mx) = (b, fastype_of t, mx)
    val decls = map mk_decl specs
    val thy = Cont_Consts.add_consts decls thy
    fun mk_const (b, T, _) = Const (Sign.full_name thy b, T)
    val consts = map mk_const decls
    fun mk_def c (b, t, _) =
      (Binding.suffix_name "_def" b, Logic.mk_equals (c, t))
    val defs = map2 mk_def consts specs
    val (def_thms, thy) =
      Global_Theory.add_defs false (map Thm.no_attributes defs) thy
  in
    ((consts, def_thms), thy)
  end

fun prove
    (thy : theory)
    (defs : thm list)
    (goal : term)
    (tacs : {prems: thm list, context: Proof.context} -> tactic list)
    : thm =
  let
    fun tac {prems, context} =
      rewrite_goals_tac defs THEN
      EVERY (tacs {prems = map (rewrite_rule defs) prems, context = context})
  in
    Goal.prove_global thy [] [] goal tac
  end

fun get_vars_avoiding
    (taken : string list)
    (args : (bool * typ) list)
    : (term list * term list) =
  let
    val Ts = map snd args
    val ns = Name.variant_list taken (Datatype_Prop.make_tnames Ts)
    val vs = map Free (ns ~~ Ts)
    val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs))
  in
    (vs, nonlazy)
  end

fun get_vars args = get_vars_avoiding [] args

(************** generating beta reduction rules from definitions **************)

local
  fun arglist (Const _ $ Abs (s, T, t)) =
      let
        val arg = Free (s, T)
        val (args, body) = arglist (subst_bound (arg, t))
      in (arg :: args, body) end
    | arglist t = ([], t)
in
  fun beta_of_def thy def_thm =
      let
        val (con, lam) = Logic.dest_equals (concl_of def_thm)
        val (args, rhs) = arglist lam
        val lhs = list_ccomb (con, args)
        val goal = mk_equals (lhs, rhs)
        val cs = ContProc.cont_thms lam
        val betas = map (fn c => mk_meta_eq (c RS @{thm beta_cfun})) cs
      in
        prove thy (def_thm::betas) goal (K [rtac reflexive_thm 1])
      end
end

(******************************************************************************)
(************* definitions and theorems for constructor functions *************)
(******************************************************************************)

fun add_constructors
    (spec : (binding * (bool * typ) list * mixfix) list)
    (abs_const : term)
    (iso_locale : thm)
    (thy : theory)
    =
  let

    (* get theorems about rep and abs *)
    val abs_strict = iso_locale RS @{thm iso.abs_strict}

    (* get types of type isomorphism *)
    val (_, lhsT) = dest_cfunT (fastype_of abs_const)

    fun vars_of args =
      let
        val Ts = map snd args
        val ns = Datatype_Prop.make_tnames Ts
      in
        map Free (ns ~~ Ts)
      end

    (* define constructor functions *)
    val ((con_consts, con_defs), thy) =
      let
        fun one_arg (lazy, _) var = if lazy then mk_up var else var
        fun one_con (_,args,_) = mk_stuple (map2 one_arg args (vars_of args))
        fun mk_abs t = abs_const ` t
        val rhss = map mk_abs (mk_sinjects (map one_con spec))
        fun mk_def (bind, args, mx) rhs =
          (bind, big_lambdas (vars_of args) rhs, mx)
      in
        define_consts (map2 mk_def spec rhss) thy
      end

    (* prove beta reduction rules for constructors *)
    val con_betas = map (beta_of_def thy) con_defs

    (* replace bindings with terms in constructor spec *)
    val spec' : (term * (bool * typ) list) list =
      let fun one_con con (_, args, _) = (con, args)
      in map2 one_con con_consts spec end

    (* prove exhaustiveness of constructors *)
    local
      fun arg2typ n (true,  _) = (n+1, mk_upT (TVar (("'a", n), @{sort cpo})))
        | arg2typ n (false, _) = (n+1, TVar (("'a", n), @{sort pcpo}))
      fun args2typ n [] = (n, oneT)
        | args2typ n [arg] = arg2typ n arg
        | args2typ n (arg::args) =
          let
            val (n1, t1) = arg2typ n arg
            val (n2, t2) = args2typ n1 args
          in (n2, mk_sprodT (t1, t2)) end
      fun cons2typ n [] = (n, oneT)
        | cons2typ n [con] = args2typ n (snd con)
        | cons2typ n (con::cons) =
          let
            val (n1, t1) = args2typ n (snd con)
            val (n2, t2) = cons2typ n1 cons
          in (n2, mk_ssumT (t1, t2)) end
      val ct = ctyp_of thy (snd (cons2typ 1 spec'))
      val thm1 = instantiate' [SOME ct] [] @{thm exh_start}
      val thm2 = rewrite_rule (map mk_meta_eq @{thms ex_bottom_iffs}) thm1
      val thm3 = rewrite_rule [mk_meta_eq @{thm conj_assoc}] thm2

      val y = Free ("y", lhsT)
      fun one_con (con, args) =
        let
          val (vs, nonlazy) = get_vars_avoiding ["y"] args
          val eqn = mk_eq (y, list_ccomb (con, vs))
          val conj = foldr1 mk_conj (eqn :: map mk_defined nonlazy)
        in Library.foldr mk_ex (vs, conj) end
      val goal = mk_trp (foldr1 mk_disj (mk_undef y :: map one_con spec'))
      (* first rules replace "y = bottom \/ P" with "rep$y = bottom \/ P" *)
      val tacs = [
          rtac (iso_locale RS @{thm iso.casedist_rule}) 1,
          rewrite_goals_tac [mk_meta_eq (iso_locale RS @{thm iso.iso_swap})],
          rtac thm3 1]
    in
      val nchotomy = prove thy con_betas goal (K tacs)
      val exhaust =
          (nchotomy RS @{thm exh_casedist0})
          |> rewrite_rule @{thms exh_casedists}
          |> Drule.zero_var_indexes
    end

    (* prove compactness rules for constructors *)
    val compacts =
      let
        val rules = @{thms compact_sinl compact_sinr compact_spair
                           compact_up compact_ONE}
        val tacs =
          [rtac (iso_locale RS @{thm iso.compact_abs}) 1,
           REPEAT (resolve_tac rules 1 ORELSE atac 1)]
        fun con_compact (con, args) =
          let
            val vs = vars_of args
            val con_app = list_ccomb (con, vs)
            val concl = mk_trp (mk_compact con_app)
            val assms = map (mk_trp o mk_compact) vs
            val goal = Logic.list_implies (assms, concl)
          in
            prove thy con_betas goal (K tacs)
          end
      in
        map con_compact spec'
      end

    (* prove strictness rules for constructors *)
    local
      fun con_strict (con, args) = 
        let
          val rules = abs_strict :: @{thms con_strict_rules}
          val (vs, nonlazy) = get_vars args
          fun one_strict v' =
            let
              val bottom = mk_bottom (fastype_of v')
              val vs' = map (fn v => if v = v' then bottom else v) vs
              val goal = mk_trp (mk_undef (list_ccomb (con, vs')))
              val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1]
            in prove thy con_betas goal (K tacs) end
        in map one_strict nonlazy end

      fun con_defin (con, args) =
        let
          fun iff_disj (t, []) = HOLogic.mk_not t
            | iff_disj (t, ts) = mk_eq (t, foldr1 HOLogic.mk_disj ts)
          val (vs, nonlazy) = get_vars args
          val lhs = mk_undef (list_ccomb (con, vs))
          val rhss = map mk_undef nonlazy
          val goal = mk_trp (iff_disj (lhs, rhss))
          val rule1 = iso_locale RS @{thm iso.abs_bottom_iff}
          val rules = rule1 :: @{thms con_bottom_iff_rules}
          val tacs = [simp_tac (HOL_ss addsimps rules) 1]
        in prove thy con_betas goal (K tacs) end
    in
      val con_stricts = maps con_strict spec'
      val con_defins = map con_defin spec'
      val con_rews = con_stricts @ con_defins
    end

    (* prove injectiveness of constructors *)
    local
      fun pgterm rel (con, args) =
        let
          fun prime (Free (n, T)) = Free (n^"'", T)
            | prime t             = t
          val (xs, nonlazy) = get_vars args
          val ys = map prime xs
          val lhs = rel (list_ccomb (con, xs), list_ccomb (con, ys))
          val rhs = foldr1 mk_conj (ListPair.map rel (xs, ys))
          val concl = mk_trp (mk_eq (lhs, rhs))
          val zs = case args of [_] => [] | _ => nonlazy
          val assms = map (mk_trp o mk_defined) zs
          val goal = Logic.list_implies (assms, concl)
        in prove thy con_betas goal end
      val cons' = filter (fn (_, args) => not (null args)) spec'
    in
      val inverts =
        let
          val abs_below = iso_locale RS @{thm iso.abs_below}
          val rules1 = abs_below :: @{thms sinl_below sinr_below spair_below up_below}
          val rules2 = @{thms up_defined spair_defined ONE_defined}
          val rules = rules1 @ rules2
          val tacs = [asm_simp_tac (simple_ss addsimps rules) 1]
        in map (fn c => pgterm mk_below c (K tacs)) cons' end
      val injects =
        let
          val abs_eq = iso_locale RS @{thm iso.abs_eq}
          val rules1 = abs_eq :: @{thms sinl_eq sinr_eq spair_eq up_eq}
          val rules2 = @{thms up_defined spair_defined ONE_defined}
          val rules = rules1 @ rules2
          val tacs = [asm_simp_tac (simple_ss addsimps rules) 1]
        in map (fn c => pgterm mk_eq c (K tacs)) cons' end
    end

    (* prove distinctness of constructors *)
    local
      fun map_dist (f : 'a -> 'a -> 'b) (xs : 'a list) : 'b list =
        flat (map_index (fn (i, x) => map (f x) (nth_drop i xs)) xs)
      fun prime (Free (n, T)) = Free (n^"'", T)
        | prime t             = t
      fun iff_disj (t, []) = mk_not t
        | iff_disj (t, ts) = mk_eq (t, foldr1 mk_disj ts)
      fun iff_disj2 (t, [], _) = mk_not t
        | iff_disj2 (t, _, []) = mk_not t
        | iff_disj2 (t, ts, us) =
          mk_eq (t, mk_conj (foldr1 mk_disj ts, foldr1 mk_disj us))
      fun dist_le (con1, args1) (con2, args2) =
        let
          val (vs1, zs1) = get_vars args1
          val (vs2, _) = get_vars args2 |> pairself (map prime)
          val lhs = mk_below (list_ccomb (con1, vs1), list_ccomb (con2, vs2))
          val rhss = map mk_undef zs1
          val goal = mk_trp (iff_disj (lhs, rhss))
          val rule1 = iso_locale RS @{thm iso.abs_below}
          val rules = rule1 :: @{thms con_below_iff_rules}
          val tacs = [simp_tac (HOL_ss addsimps rules) 1]
        in prove thy con_betas goal (K tacs) end
      fun dist_eq (con1, args1) (con2, args2) =
        let
          val (vs1, zs1) = get_vars args1
          val (vs2, zs2) = get_vars args2 |> pairself (map prime)
          val lhs = mk_eq (list_ccomb (con1, vs1), list_ccomb (con2, vs2))
          val rhss1 = map mk_undef zs1
          val rhss2 = map mk_undef zs2
          val goal = mk_trp (iff_disj2 (lhs, rhss1, rhss2))
          val rule1 = iso_locale RS @{thm iso.abs_eq}
          val rules = rule1 :: @{thms con_eq_iff_rules}
          val tacs = [simp_tac (HOL_ss addsimps rules) 1]
        in prove thy con_betas goal (K tacs) end
    in
      val dist_les = map_dist dist_le spec'
      val dist_eqs = map_dist dist_eq spec'
    end

    val result =
      {
        con_consts = con_consts,
        con_betas = con_betas,
        nchotomy = nchotomy,
        exhaust = exhaust,
        compacts = compacts,
        con_rews = con_rews,
        inverts = inverts,
        injects = injects,
        dist_les = dist_les,
        dist_eqs = dist_eqs
      }
  in
    (result, thy)
  end

(******************************************************************************)
(**************** definition and theorems for case combinator *****************)
(******************************************************************************)

fun add_case_combinator
    (spec : (term * (bool * typ) list) list)
    (lhsT : typ)
    (dbind : binding)
    (con_betas : thm list)
    (iso_locale : thm)
    (rep_const : term)
    (thy : theory)
    : ((typ -> term) * thm list) * theory =
  let

    (* prove rep/abs rules *)
    val rep_strict = iso_locale RS @{thm iso.rep_strict}
    val abs_inverse = iso_locale RS @{thm iso.abs_iso}

    (* calculate function arguments of case combinator *)
    val tns = map fst (Term.add_tfreesT lhsT [])
    val resultT = TFree (singleton (Name.variant_list tns) "'t", @{sort pcpo})
    fun fTs T = map (fn (_, args) => map snd args -->> T) spec
    val fns = Datatype_Prop.indexify_names (map (K "f") spec)
    val fs = map Free (fns ~~ fTs resultT)
    fun caseT T = fTs T -->> (lhsT ->> T)

    (* definition of case combinator *)
    local
      val case_bind = Binding.suffix_name "_case" dbind
      fun lambda_arg (lazy, v) t =
          (if lazy then mk_fup else I) (big_lambda v t)
      fun lambda_args []      t = mk_one_case t
        | lambda_args (x::[]) t = lambda_arg x t
        | lambda_args (x::xs) t = mk_ssplit (lambda_arg x (lambda_args xs t))
      fun one_con f (_, args) =
        let
          val Ts = map snd args
          val ns = Name.variant_list fns (Datatype_Prop.make_tnames Ts)
          val vs = map Free (ns ~~ Ts)
        in
          lambda_args (map fst args ~~ vs) (list_ccomb (f, vs))
        end
      fun mk_sscases [t] = mk_strictify t
        | mk_sscases ts = foldr1 mk_sscase ts
      val body = mk_sscases (map2 one_con fs spec)
      val rhs = big_lambdas fs (mk_cfcomp (body, rep_const))
      val ((_, case_defs), thy) =
          define_consts [(case_bind, rhs, NoSyn)] thy
      val case_name = Sign.full_name thy case_bind
    in
      val case_def = hd case_defs
      fun case_const T = Const (case_name, caseT T)
      val case_app = list_ccomb (case_const resultT, fs)
      val thy = thy
    end

    (* define syntax for case combinator *)
    (* TODO: re-implement case syntax using a parse translation *)
    local
      fun syntax c = Lexicon.mark_const (fst (dest_Const c))
      fun xconst c = Long_Name.base_name (fst (dest_Const c))
      fun c_ast authentic con = Ast.Constant (if authentic then syntax con else xconst con)
      fun showint n = string_of_int (n+1)
      fun expvar n = Ast.Variable ("e" ^ showint n)
      fun argvar n (m, _) = Ast.Variable ("a" ^ showint n ^ "_" ^ showint m)
      fun argvars n args = map_index (argvar n) args
      fun app s (l, r) = Ast.mk_appl (Ast.Constant s) [l, r]
      val cabs = app "_cabs"
      val capp = app @{const_syntax Rep_cfun}
      val capps = Library.foldl capp
      fun con1 authentic n (con,args) =
          Library.foldl capp (c_ast authentic con, argvars n args)
      fun case1 authentic (n, c) =
          app "_case1" (Ast.strip_positions (con1 authentic n c), expvar n)
      fun arg1 (n, (_, args)) = List.foldr cabs (expvar n) (argvars n args)
      fun when1 n (m, c) = if n = m then arg1 (n, c) else Ast.Constant @{const_syntax bottom}
      val case_constant = Ast.Constant (syntax (case_const dummyT))
      fun case_trans authentic =
        (if authentic then Syntax.Parse_Print_Rule else Syntax.Parse_Rule)
          (app "_case_syntax"
            (Ast.Variable "x",
             foldr1 (app "_case2") (map_index (case1 authentic) spec)),
           capp (capps (case_constant, map_index arg1 spec), Ast.Variable "x"))
      fun one_abscon_trans authentic (n, c) =
        (if authentic then Syntax.Parse_Print_Rule else Syntax.Parse_Rule)
          (cabs (con1 authentic n c, expvar n),
           capps (case_constant, map_index (when1 n) spec))
      fun abscon_trans authentic =
          map_index (one_abscon_trans authentic) spec
      val trans_rules : Ast.ast Syntax.trrule list =
          case_trans false :: case_trans true ::
          abscon_trans false @ abscon_trans true
    in
      val thy = Sign.add_trrules trans_rules thy
    end

    (* prove beta reduction rule for case combinator *)
    val case_beta = beta_of_def thy case_def

    (* prove strictness of case combinator *)
    val case_strict =
      let
        val defs = case_beta :: map mk_meta_eq [rep_strict, @{thm cfcomp2}]
        val goal = mk_trp (mk_strict case_app)
        val rules = @{thms sscase1 ssplit1 strictify1 one_case1}
        val tacs = [resolve_tac rules 1]
      in prove thy defs goal (K tacs) end
        
    (* prove rewrites for case combinator *)
    local
      fun one_case (con, args) f =
        let
          val (vs, nonlazy) = get_vars args
          val assms = map (mk_trp o mk_defined) nonlazy
          val lhs = case_app ` list_ccomb (con, vs)
          val rhs = list_ccomb (f, vs)
          val concl = mk_trp (mk_eq (lhs, rhs))
          val goal = Logic.list_implies (assms, concl)
          val defs = case_beta :: con_betas
          val rules1 = @{thms strictify2 sscase2 sscase3 ssplit2 fup2 ID1}
          val rules2 = @{thms con_bottom_iff_rules}
          val rules3 = @{thms cfcomp2 one_case2}
          val rules = abs_inverse :: rules1 @ rules2 @ rules3
          val tacs = [asm_simp_tac (beta_ss addsimps rules) 1]
        in prove thy defs goal (K tacs) end
    in
      val case_apps = map2 one_case spec fs
    end

  in
    ((case_const, case_strict :: case_apps), thy)
  end

(******************************************************************************)
(************** definitions and theorems for selector functions ***************)
(******************************************************************************)

fun add_selectors
    (spec : (term * (bool * binding option * typ) list) list)
    (rep_const : term)
    (abs_inv : thm)
    (rep_strict : thm)
    (rep_bottom_iff : thm)
    (con_betas : thm list)
    (thy : theory)
    : thm list * theory =
  let

    (* define selector functions *)
    val ((sel_consts, sel_defs), thy) =
      let
        fun rangeT s = snd (dest_cfunT (fastype_of s))
        fun mk_outl s = mk_cfcomp (from_sinl (dest_ssumT (rangeT s)), s)
        fun mk_outr s = mk_cfcomp (from_sinr (dest_ssumT (rangeT s)), s)
        fun mk_sfst s = mk_cfcomp (sfst_const (dest_sprodT (rangeT s)), s)
        fun mk_ssnd s = mk_cfcomp (ssnd_const (dest_sprodT (rangeT s)), s)
        fun mk_down s = mk_cfcomp (from_up (dest_upT (rangeT s)), s)

        fun sels_of_arg _ (_, NONE, _) = []
          | sels_of_arg s (lazy, SOME b, _) =
            [(b, if lazy then mk_down s else s, NoSyn)]
        fun sels_of_args _ [] = []
          | sels_of_args s (v :: []) = sels_of_arg s v
          | sels_of_args s (v :: vs) =
            sels_of_arg (mk_sfst s) v @ sels_of_args (mk_ssnd s) vs
        fun sels_of_cons _ [] = []
          | sels_of_cons s ((_, args) :: []) = sels_of_args s args
          | sels_of_cons s ((_, args) :: cs) =
            sels_of_args (mk_outl s) args @ sels_of_cons (mk_outr s) cs
        val sel_eqns : (binding * term * mixfix) list =
            sels_of_cons rep_const spec
      in
        define_consts sel_eqns thy
      end

    (* replace bindings with terms in constructor spec *)
    val spec2 : (term * (bool * term option * typ) list) list =
      let
        fun prep_arg (lazy, NONE, T) sels = ((lazy, NONE, T), sels)
          | prep_arg (lazy, SOME _, T) sels =
            ((lazy, SOME (hd sels), T), tl sels)
        fun prep_con (con, args) sels =
            apfst (pair con) (fold_map prep_arg args sels)
      in
        fst (fold_map prep_con spec sel_consts)
      end

    (* prove selector strictness rules *)
    val sel_stricts : thm list =
      let
        val rules = rep_strict :: @{thms sel_strict_rules}
        val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1]
        fun sel_strict sel =
          let
            val goal = mk_trp (mk_strict sel)
          in
            prove thy sel_defs goal (K tacs)
          end
      in
        map sel_strict sel_consts
      end

    (* prove selector application rules *)
    val sel_apps : thm list =
      let
        val defs = con_betas @ sel_defs
        val rules = abs_inv :: @{thms sel_app_rules}
        val tacs = [asm_simp_tac (simple_ss addsimps rules) 1]
        fun sel_apps_of (i, (con, args: (bool * term option * typ) list)) =
          let
            val Ts : typ list = map #3 args
            val ns : string list = Datatype_Prop.make_tnames Ts
            val vs : term list = map Free (ns ~~ Ts)
            val con_app : term = list_ccomb (con, vs)
            val vs' : (bool * term) list = map #1 args ~~ vs
            fun one_same (n, sel, _) =
              let
                val xs = map snd (filter_out fst (nth_drop n vs'))
                val assms = map (mk_trp o mk_defined) xs
                val concl = mk_trp (mk_eq (sel ` con_app, nth vs n))
                val goal = Logic.list_implies (assms, concl)
              in
                prove thy defs goal (K tacs)
              end
            fun one_diff (_, sel, T) =
              let
                val goal = mk_trp (mk_eq (sel ` con_app, mk_bottom T))
              in
                prove thy defs goal (K tacs)
              end
            fun one_con (j, (_, args')) : thm list =
              let
                fun prep (_, (_, NONE, _)) = NONE
                  | prep (i, (_, SOME sel, T)) = SOME (i, sel, T)
                val sels : (int * term * typ) list =
                  map_filter prep (map_index I args')
              in
                if i = j
                then map one_same sels
                else map one_diff sels
              end
          in
            flat (map_index one_con spec2)
          end
      in
        flat (map_index sel_apps_of spec2)
      end

  (* prove selector definedness rules *)
    val sel_defins : thm list =
      let
        val rules = rep_bottom_iff :: @{thms sel_bottom_iff_rules}
        val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1]
        fun sel_defin sel =
          let
            val (T, U) = dest_cfunT (fastype_of sel)
            val x = Free ("x", T)
            val lhs = mk_eq (sel ` x, mk_bottom U)
            val rhs = mk_eq (x, mk_bottom T)
            val goal = mk_trp (mk_eq (lhs, rhs))
          in
            prove thy sel_defs goal (K tacs)
          end
        fun one_arg (false, SOME sel, _) = SOME (sel_defin sel)
          | one_arg _                    = NONE
      in
        case spec2 of
          [(_, args)] => map_filter one_arg args
        | _           => []
      end

  in
    (sel_stricts @ sel_defins @ sel_apps, thy)
  end

(******************************************************************************)
(************ definitions and theorems for discriminator functions ************)
(******************************************************************************)

fun add_discriminators
    (bindings : binding list)
    (spec : (term * (bool * typ) list) list)
    (lhsT : typ)
    (exhaust : thm)
    (case_const : typ -> term)
    (case_rews : thm list)
    (thy : theory) =
  let

    (* define discriminator functions *)
    local
      fun dis_fun i (j, (_, args)) =
        let
          val (vs, _) = get_vars args
          val tr = if i = j then @{term TT} else @{term FF}
        in
          big_lambdas vs tr
        end
      fun dis_eqn (i, bind) : binding * term * mixfix =
        let
          val dis_bind = Binding.prefix_name "is_" bind
          val rhs = list_ccomb (case_const trT, map_index (dis_fun i) spec)
        in
          (dis_bind, rhs, NoSyn)
        end
    in
      val ((dis_consts, dis_defs), thy) =
          define_consts (map_index dis_eqn bindings) thy
    end

    (* prove discriminator strictness rules *)
    local
      fun dis_strict dis =
        let val goal = mk_trp (mk_strict dis)
        in prove thy dis_defs goal (K [rtac (hd case_rews) 1]) end
    in
      val dis_stricts = map dis_strict dis_consts
    end

    (* prove discriminator/constructor rules *)
    local
      fun dis_app (i, dis) (j, (con, args)) =
        let
          val (vs, nonlazy) = get_vars args
          val lhs = dis ` list_ccomb (con, vs)
          val rhs = if i = j then @{term TT} else @{term FF}
          val assms = map (mk_trp o mk_defined) nonlazy
          val concl = mk_trp (mk_eq (lhs, rhs))
          val goal = Logic.list_implies (assms, concl)
          val tacs = [asm_simp_tac (beta_ss addsimps case_rews) 1]
        in prove thy dis_defs goal (K tacs) end
      fun one_dis (i, dis) =
          map_index (dis_app (i, dis)) spec
    in
      val dis_apps = flat (map_index one_dis dis_consts)
    end

    (* prove discriminator definedness rules *)
    local
      fun dis_defin dis =
        let
          val x = Free ("x", lhsT)
          val simps = dis_apps @ @{thms dist_eq_tr}
          val tacs =
            [rtac @{thm iffI} 1,
             asm_simp_tac (HOL_basic_ss addsimps dis_stricts) 2,
             rtac exhaust 1, atac 1,
             DETERM_UNTIL_SOLVED (CHANGED
               (asm_full_simp_tac (simple_ss addsimps simps) 1))]
          val goal = mk_trp (mk_eq (mk_undef (dis ` x), mk_undef x))
        in prove thy [] goal (K tacs) end
    in
      val dis_defins = map dis_defin dis_consts
    end

  in
    (dis_stricts @ dis_defins @ dis_apps, thy)
  end

(******************************************************************************)
(*************** definitions and theorems for match combinators ***************)
(******************************************************************************)

fun add_match_combinators
    (bindings : binding list)
    (spec : (term * (bool * typ) list) list)
    (lhsT : typ)
    (case_const : typ -> term)
    (case_rews : thm list)
    (thy : theory) =
  let

    (* get a fresh type variable for the result type *)
    val resultT : typ =
      let
        val ts : string list = map fst (Term.add_tfreesT lhsT [])
        val t : string = singleton (Name.variant_list ts) "'t"
      in TFree (t, @{sort pcpo}) end

    (* define match combinators *)
    local
      val x = Free ("x", lhsT)
      fun k args = Free ("k", map snd args -->> mk_matchT resultT)
      val fail = mk_fail resultT
      fun mat_fun i (j, (_, args)) =
        let
          val (vs, _) = get_vars_avoiding ["x","k"] args
        in
          if i = j then k args else big_lambdas vs fail
        end
      fun mat_eqn (i, (bind, (_, args))) : binding * term * mixfix =
        let
          val mat_bind = Binding.prefix_name "match_" bind
          val funs = map_index (mat_fun i) spec
          val body = list_ccomb (case_const (mk_matchT resultT), funs)
          val rhs = big_lambda x (big_lambda (k args) (body ` x))
        in
          (mat_bind, rhs, NoSyn)
        end
    in
      val ((match_consts, match_defs), thy) =
          define_consts (map_index mat_eqn (bindings ~~ spec)) thy
    end

    (* register match combinators with fixrec package *)
    local
      val con_names = map (fst o dest_Const o fst) spec
      val mat_names = map (fst o dest_Const) match_consts
    in
      val thy = Fixrec.add_matchers (con_names ~~ mat_names) thy
    end

    (* prove strictness of match combinators *)
    local
      fun match_strict mat =
        let
          val (T, (U, V)) = apsnd dest_cfunT (dest_cfunT (fastype_of mat))
          val k = Free ("k", U)
          val goal = mk_trp (mk_eq (mat ` mk_bottom T ` k, mk_bottom V))
          val tacs = [asm_simp_tac (beta_ss addsimps case_rews) 1]
        in prove thy match_defs goal (K tacs) end
    in
      val match_stricts = map match_strict match_consts
    end

    (* prove match/constructor rules *)
    local
      val fail = mk_fail resultT
      fun match_app (i, mat) (j, (con, args)) =
        let
          val (vs, nonlazy) = get_vars_avoiding ["k"] args
          val (_, (kT, _)) = apsnd dest_cfunT (dest_cfunT (fastype_of mat))
          val k = Free ("k", kT)
          val lhs = mat ` list_ccomb (con, vs) ` k
          val rhs = if i = j then list_ccomb (k, vs) else fail
          val assms = map (mk_trp o mk_defined) nonlazy
          val concl = mk_trp (mk_eq (lhs, rhs))
          val goal = Logic.list_implies (assms, concl)
          val tacs = [asm_simp_tac (beta_ss addsimps case_rews) 1]
        in prove thy match_defs goal (K tacs) end
      fun one_match (i, mat) =
          map_index (match_app (i, mat)) spec
    in
      val match_apps = flat (map_index one_match match_consts)
    end

  in
    (match_stricts @ match_apps, thy)
  end

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun add_domain_constructors
    (dbind : binding)
    (spec : (binding * (bool * binding option * typ) list * mixfix) list)
    (iso_info : Domain_Take_Proofs.iso_info)
    (thy : theory) =
  let
    val dname = Binding.name_of dbind
    val _ = writeln ("Proving isomorphism properties of domain "^dname^" ...")

    val bindings = map #1 spec

    (* retrieve facts about rep/abs *)
    val lhsT = #absT iso_info
    val {rep_const, abs_const, ...} = iso_info
    val abs_iso_thm = #abs_inverse iso_info
    val rep_iso_thm = #rep_inverse iso_info
    val iso_locale = @{thm iso.intro} OF [abs_iso_thm, rep_iso_thm]
    val rep_strict = iso_locale RS @{thm iso.rep_strict}
    val abs_strict = iso_locale RS @{thm iso.abs_strict}
    val rep_bottom_iff = iso_locale RS @{thm iso.rep_bottom_iff}
    val iso_rews = [abs_iso_thm, rep_iso_thm, abs_strict, rep_strict]

    (* qualify constants and theorems with domain name *)
    val thy = Sign.add_path dname thy

    (* define constructor functions *)
    val (con_result, thy) =
      let
        fun prep_arg (lazy, _, T) = (lazy, T)
        fun prep_con (b, args, mx) = (b, map prep_arg args, mx)
        val con_spec = map prep_con spec
      in
        add_constructors con_spec abs_const iso_locale thy
      end
    val {con_consts, con_betas, nchotomy, exhaust, compacts, con_rews,
          inverts, injects, dist_les, dist_eqs} = con_result

    (* prepare constructor spec *)
    val con_specs : (term * (bool * typ) list) list =
      let
        fun prep_arg (lazy, _, T) = (lazy, T)
        fun prep_con c (_, args, _) = (c, map prep_arg args)
      in
        map2 prep_con con_consts spec
      end

    (* define case combinator *)
    val ((case_const : typ -> term, cases : thm list), thy) =
        add_case_combinator con_specs lhsT dbind
          con_betas iso_locale rep_const thy

    (* define and prove theorems for selector functions *)
    val (sel_thms : thm list, thy : theory) =
      let
        val sel_spec : (term * (bool * binding option * typ) list) list =
          map2 (fn con => fn (_, args, _) => (con, args)) con_consts spec
      in
        add_selectors sel_spec rep_const
          abs_iso_thm rep_strict rep_bottom_iff con_betas thy
      end

    (* define and prove theorems for discriminator functions *)
    val (dis_thms : thm list, thy : theory) =
        add_discriminators bindings con_specs lhsT
          exhaust case_const cases thy

    (* define and prove theorems for match combinators *)
    val (match_thms : thm list, thy : theory) =
        add_match_combinators bindings con_specs lhsT
          case_const cases thy

    (* restore original signature path *)
    val thy = Sign.parent_path thy

    (* bind theorem names in global theory *)
    val (_, thy) =
      let
        fun qualified name = Binding.qualified true name dbind
        val names = "bottom" :: map (fn (b,_,_) => Binding.name_of b) spec
        val dname = fst (dest_Type lhsT)
        val simp = Simplifier.simp_add
        val case_names = Rule_Cases.case_names names
        val cases_type = Induct.cases_type dname
      in
        Global_Theory.add_thmss [
          ((qualified "iso_rews"  , iso_rews    ), [simp]),
          ((qualified "nchotomy"  , [nchotomy]  ), []),
          ((qualified "exhaust"   , [exhaust]   ), [case_names, cases_type]),
          ((qualified "case_rews" , cases       ), [simp]),
          ((qualified "compacts"  , compacts    ), [simp]),
          ((qualified "con_rews"  , con_rews    ), [simp]),
          ((qualified "sel_rews"  , sel_thms    ), [simp]),
          ((qualified "dis_rews"  , dis_thms    ), [simp]),
          ((qualified "dist_les"  , dist_les    ), [simp]),
          ((qualified "dist_eqs"  , dist_eqs    ), [simp]),
          ((qualified "inverts"   , inverts     ), [simp]),
          ((qualified "injects"   , injects     ), [simp]),
          ((qualified "match_rews", match_thms  ), [simp])] thy
      end

    val result =
      {
        iso_info = iso_info,
        con_specs = con_specs,
        con_betas = con_betas,
        nchotomy = nchotomy,
        exhaust = exhaust,
        compacts = compacts,
        con_rews = con_rews,
        inverts = inverts,
        injects = injects,
        dist_les = dist_les,
        dist_eqs = dist_eqs,
        cases = cases,
        sel_rews = sel_thms,
        dis_rews = dis_thms,
        match_rews = match_thms
      }
  in
    (result, thy)
  end

end
