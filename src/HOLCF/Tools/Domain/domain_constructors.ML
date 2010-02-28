(*  Title:      HOLCF/Tools/domain/domain_constructors.ML
    Author:     Brian Huffman

Defines constructor functions for a given domain isomorphism
and proves related theorems.
*)

signature DOMAIN_CONSTRUCTORS =
sig
  val add_domain_constructors :
      string
      -> typ * (binding * (bool * binding option * typ) list * mixfix) list
      -> term * term
      -> thm * thm
      -> thm
      -> theory
      -> { con_consts : term list,
           con_betas : thm list,
           exhaust : thm,
           casedist : thm,
           con_compacts : thm list,
           con_rews : thm list,
           inverts : thm list,
           injects : thm list,
           dist_les : thm list,
           dist_eqs : thm list,
           cases : thm list,
           sel_rews : thm list,
           dis_rews : thm list,
           match_rews : thm list
         } * theory;
end;


structure Domain_Constructors :> DOMAIN_CONSTRUCTORS =
struct

(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)


(*** Operations from Isabelle/HOL ***)

val boolT = HOLogic.boolT;

val mk_equals = Logic.mk_equals;
val mk_eq = HOLogic.mk_eq;
val mk_trp = HOLogic.mk_Trueprop;
val mk_fst = HOLogic.mk_fst;
val mk_snd = HOLogic.mk_snd;
val mk_not = HOLogic.mk_not;
val mk_conj = HOLogic.mk_conj;
val mk_disj = HOLogic.mk_disj;

fun mk_ex (x, t) = HOLogic.exists_const (fastype_of x) $ Term.lambda x t;

(*** Basic HOLCF concepts ***)

fun mk_bottom T = Const (@{const_name UU}, T);

fun below_const T = Const (@{const_name below}, [T, T] ---> boolT);
fun mk_below (t, u) = below_const (fastype_of t) $ t $ u;

fun mk_undef t = mk_eq (t, mk_bottom (fastype_of t));

fun mk_defined t = mk_not (mk_undef t);

fun mk_compact t =
  Const (@{const_name compact}, fastype_of t --> boolT) $ t;

fun mk_cont t =
  Const (@{const_name cont}, fastype_of t --> boolT) $ t;


(*** Continuous function space ***)

(* ->> is taken from holcf_logic.ML *)
fun mk_cfunT (T, U) = Type(@{type_name "->"}, [T, U]);

infixr 6 ->>; val (op ->>) = mk_cfunT;
infix -->>; val (op -->>) = Library.foldr mk_cfunT;

fun dest_cfunT (Type(@{type_name "->"}, [T, U])) = (T, U)
  | dest_cfunT T = raise TYPE ("dest_cfunT", [T], []);

fun capply_const (S, T) =
  Const(@{const_name Rep_CFun}, (S ->> T) --> (S --> T));

fun cabs_const (S, T) =
  Const(@{const_name Abs_CFun}, (S --> T) --> (S ->> T));

fun mk_cabs t =
  let val T = fastype_of t
  in cabs_const (Term.domain_type T, Term.range_type T) $ t end

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs =
  cabs_const (fastype_of v, fastype_of rhs) $ Term.lambda v rhs;

(* builds the expression (LAM v1 v2 .. vn. rhs) *)
fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs);

fun mk_capply (t, u) =
  let val (S, T) =
    case fastype_of t of
        Type(@{type_name "->"}, [S, T]) => (S, T)
      | _ => raise TERM ("mk_capply " ^ ML_Syntax.print_list ML_Syntax.print_term [t, u], [t, u]);
  in capply_const (S, T) $ t $ u end;

infix 9 ` ; val (op `) = mk_capply;

val list_ccomb : term * term list -> term = Library.foldl mk_capply;

fun mk_ID T = Const (@{const_name ID}, T ->> T);

fun cfcomp_const (T, U, V) =
  Const (@{const_name cfcomp}, (U ->> V) ->> (T ->> U) ->> (T ->> V));

fun mk_cfcomp (f, g) =
  let
    val (U, V) = dest_cfunT (fastype_of f);
    val (T, U') = dest_cfunT (fastype_of g);
  in
    if U = U'
    then mk_capply (mk_capply (cfcomp_const (T, U, V), f), g)
    else raise TYPE ("mk_cfcomp", [U, U'], [f, g])
  end;


(*** Product type ***)

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT [T] = T
  | mk_tupleT (T :: Ts) = HOLogic.mk_prodT (T, mk_tupleT Ts);

(* builds the expression (v1,v2,..,vn) *)
fun mk_tuple [] = HOLogic.unit
  | mk_tuple (t::[]) = t
  | mk_tuple (t::ts) = HOLogic.mk_prod (t, mk_tuple ts);

(* builds the expression (%(v1,v2,..,vn). rhs) *)
fun lambda_tuple [] rhs = Term.lambda (Free("unit", HOLogic.unitT)) rhs
  | lambda_tuple (v::[]) rhs = Term.lambda v rhs
  | lambda_tuple (v::vs) rhs =
      HOLogic.mk_split (Term.lambda v (lambda_tuple vs rhs));


(*** Lifted cpo type ***)

fun mk_upT T = Type(@{type_name "u"}, [T]);

fun dest_upT (Type(@{type_name "u"}, [T])) = T
  | dest_upT T = raise TYPE ("dest_upT", [T], []);

fun up_const T = Const(@{const_name up}, T ->> mk_upT T);

fun mk_up t = up_const (fastype_of t) ` t;

fun fup_const (T, U) =
  Const(@{const_name fup}, (T ->> U) ->> mk_upT T ->> U);

fun from_up T = fup_const (T, T) ` mk_ID T;


(*** Strict product type ***)

val oneT = @{typ "one"};

fun mk_sprodT (T, U) = Type(@{type_name "**"}, [T, U]);

fun dest_sprodT (Type(@{type_name "**"}, [T, U])) = (T, U)
  | dest_sprodT T = raise TYPE ("dest_sprodT", [T], []);

fun spair_const (T, U) =
  Const(@{const_name spair}, T ->> U ->> mk_sprodT (T, U));

(* builds the expression (:t, u:) *)
fun mk_spair (t, u) =
  spair_const (fastype_of t, fastype_of u) ` t ` u;

(* builds the expression (:t1,t2,..,tn:) *)
fun mk_stuple [] = @{term "ONE"}
  | mk_stuple (t::[]) = t
  | mk_stuple (t::ts) = mk_spair (t, mk_stuple ts);

fun sfst_const (T, U) =
  Const(@{const_name sfst}, mk_sprodT (T, U) ->> T);

fun ssnd_const (T, U) =
  Const(@{const_name ssnd}, mk_sprodT (T, U) ->> U);


(*** Strict sum type ***)

fun mk_ssumT (T, U) = Type(@{type_name "++"}, [T, U]);

fun dest_ssumT (Type(@{type_name "++"}, [T, U])) = (T, U)
  | dest_ssumT T = raise TYPE ("dest_ssumT", [T], []);

fun sinl_const (T, U) = Const(@{const_name sinl}, T ->> mk_ssumT (T, U));
fun sinr_const (T, U) = Const(@{const_name sinr}, U ->> mk_ssumT (T, U));

(* builds the list [sinl(t1), sinl(sinr(t2)), ... sinr(...sinr(tn))] *)
fun mk_sinjects ts =
  let
    val Ts = map fastype_of ts;
    fun combine (t, T) (us, U) =
      let
        val v = sinl_const (T, U) ` t;
        val vs = map (fn u => sinr_const (T, U) ` u) us;
      in
        (v::vs, mk_ssumT (T, U))
      end
    fun inj [] = error "mk_sinjects: empty list"
      | inj ((t, T)::[]) = ([t], T)
      | inj ((t, T)::ts) = combine (t, T) (inj ts);
  in
    fst (inj (ts ~~ Ts))
  end;

fun sscase_const (T, U, V) =
  Const(@{const_name sscase},
    (T ->> V) ->> (U ->> V) ->> mk_ssumT (T, U) ->> V);

fun from_sinl (T, U) =
  sscase_const (T, U, T) ` mk_ID T ` mk_bottom (U ->> T);

fun from_sinr (T, U) =
  sscase_const (T, U, U) ` mk_bottom (T ->> U) ` mk_ID U;


(*** pattern match monad type ***)

fun mk_matchT T = Type (@{type_name "maybe"}, [T]);

fun mk_fail T = Const (@{const_name "Fixrec.fail"}, mk_matchT T);


(*** miscellaneous constructions ***)

val trT = @{typ "tr"};

val deflT = @{typ "udom alg_defl"};

fun mapT T =
  let
    fun argTs (Type (_, Ts)) = Ts | argTs _ = [];
    fun auto T = T ->> T;
  in
    map auto (argTs T) -->> auto T
  end;

fun mk_strict t =
  let val (T, U) = dest_cfunT (fastype_of t);
  in mk_eq (t ` mk_bottom T, mk_bottom U) end;

fun mk_fix t =
  let val (T, _) = dest_cfunT (fastype_of t)
  in mk_capply (Const(@{const_name fix}, (T ->> T) ->> T), t) end;

fun mk_Rep_of T =
  Const (@{const_name Rep_of}, Term.itselfT T --> deflT) $ Logic.mk_type T;

fun coerce_const T = Const (@{const_name coerce}, T);

fun isodefl_const T =
  Const (@{const_name isodefl}, (T ->> T) --> deflT --> boolT);

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u));


(************************** miscellaneous functions ***************************)

val simple_ss =
  HOL_basic_ss addsimps simp_thms;

val beta_ss =
  HOL_basic_ss
    addsimps simp_thms
    addsimps [@{thm beta_cfun}]
    addsimprocs [@{simproc cont_proc}];

fun define_consts
    (specs : (binding * term * mixfix) list)
    (thy : theory)
    : (term list * thm list) * theory =
  let
    fun mk_decl (b, t, mx) = (b, fastype_of t, mx);
    val decls = map mk_decl specs;
    val thy = Cont_Consts.add_consts decls thy;
    fun mk_const (b, T, mx) = Const (Sign.full_name thy b, T);
    val consts = map mk_const decls;
    fun mk_def c (b, t, mx) =
      (Binding.suffix_name "_def" b, Logic.mk_equals (c, t));
    val defs = map2 mk_def consts specs;
    val (def_thms, thy) =
      PureThy.add_defs false (map Thm.no_attributes defs) thy;
  in
    ((consts, def_thms), thy)
  end;

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
  end;

(************** generating beta reduction rules from definitions **************)

local
  fun arglist (Const _ $ Abs (s, T, t)) =
      let
        val arg = Free (s, T);
        val (args, body) = arglist (subst_bound (arg, t));
      in (arg :: args, body) end
    | arglist t = ([], t);
in
  fun beta_of_def thy def_thm =
      let
        val (con, lam) = Logic.dest_equals (concl_of def_thm);
        val (args, rhs) = arglist lam;
        val lhs = list_ccomb (con, args);
        val goal = mk_equals (lhs, rhs);
        val cs = ContProc.cont_thms lam;
        val betas = map (fn c => mk_meta_eq (c RS @{thm beta_cfun})) cs;
      in
        prove thy (def_thm::betas) goal (K [rtac reflexive_thm 1])
      end;
end;

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
    val abs_strict = iso_locale RS @{thm iso.abs_strict};

    (* get types of type isomorphism *)
    val (rhsT, lhsT) = dest_cfunT (fastype_of abs_const);

    fun vars_of args =
      let
        val Ts = map snd args;
        val ns = Datatype_Prop.make_tnames Ts;
      in
        map Free (ns ~~ Ts)
      end;

    (* define constructor functions *)
    val ((con_consts, con_defs), thy) =
      let
        fun one_arg (lazy, T) var = if lazy then mk_up var else var;
        fun one_con (_,args,_) = mk_stuple (map2 one_arg args (vars_of args));
        fun mk_abs t = abs_const ` t;
        val rhss = map mk_abs (mk_sinjects (map one_con spec));
        fun mk_def (bind, args, mx) rhs =
          (bind, big_lambdas (vars_of args) rhs, mx);
      in
        define_consts (map2 mk_def spec rhss) thy
      end;

    (* prove beta reduction rules for constructors *)
    val con_betas = map (beta_of_def thy) con_defs;

    (* replace bindings with terms in constructor spec *)
    val spec' : (term * (bool * typ) list) list =
      let fun one_con con (b, args, mx) = (con, args);
      in map2 one_con con_consts spec end;

    (* prove exhaustiveness of constructors *)
    local
      fun arg2typ n (true,  T) = (n+1, mk_upT (TVar (("'a", n), @{sort cpo})))
        | arg2typ n (false, T) = (n+1, TVar (("'a", n), @{sort pcpo}));
      fun args2typ n [] = (n, oneT)
        | args2typ n [arg] = arg2typ n arg
        | args2typ n (arg::args) =
          let
            val (n1, t1) = arg2typ n arg;
            val (n2, t2) = args2typ n1 args
          in (n2, mk_sprodT (t1, t2)) end;
      fun cons2typ n [] = (n, oneT)
        | cons2typ n [con] = args2typ n (snd con)
        | cons2typ n (con::cons) =
          let
            val (n1, t1) = args2typ n (snd con);
            val (n2, t2) = cons2typ n1 cons
          in (n2, mk_ssumT (t1, t2)) end;
      val ct = ctyp_of thy (snd (cons2typ 1 spec'));
      val thm1 = instantiate' [SOME ct] [] @{thm exh_start};
      val thm2 = rewrite_rule (map mk_meta_eq @{thms ex_defined_iffs}) thm1;
      val thm3 = rewrite_rule [mk_meta_eq @{thm conj_assoc}] thm2;

      val x = Free ("x", lhsT);
      fun one_con (con, args) =
        let
          val Ts = map snd args;
          val ns = Name.variant_list ["x"] (Datatype_Prop.make_tnames Ts);
          val vs = map Free (ns ~~ Ts);
          val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs));
          val eqn = mk_eq (x, list_ccomb (con, vs));
          val conj = foldr1 mk_conj (eqn :: map mk_defined nonlazy);
        in Library.foldr mk_ex (vs, conj) end;
      val goal = mk_trp (foldr1 mk_disj (mk_undef x :: map one_con spec'));
      (* first 3 rules replace "x = UU \/ P" with "rep$x = UU \/ P" *)
      val tacs = [
          rtac (iso_locale RS @{thm iso.casedist_rule}) 1,
          rewrite_goals_tac [mk_meta_eq (iso_locale RS @{thm iso.iso_swap})],
          rtac thm3 1];
    in
      val exhaust = prove thy con_betas goal (K tacs);
      val casedist =
          (exhaust RS @{thm exh_casedist0})
          |> rewrite_rule @{thms exh_casedists}
          |> Drule.export_without_context;
    end;

    (* prove compactness rules for constructors *)
    val con_compacts =
      let
        val rules = @{thms compact_sinl compact_sinr compact_spair
                           compact_up compact_ONE};
        val tacs =
          [rtac (iso_locale RS @{thm iso.compact_abs}) 1,
           REPEAT (resolve_tac rules 1 ORELSE atac 1)];
        fun con_compact (con, args) =
          let
            val vs = vars_of args;
            val con_app = list_ccomb (con, vs);
            val concl = mk_trp (mk_compact con_app);
            val assms = map (mk_trp o mk_compact) vs;
            val goal = Logic.list_implies (assms, concl);
          in
            prove thy con_betas goal (K tacs)
          end;
      in
        map con_compact spec'
      end;

    (* prove strictness rules for constructors *)
    local
      fun con_strict (con, args) = 
        let
          val rules = abs_strict :: @{thms con_strict_rules};
          val vs = vars_of args;
          val nonlazy = map snd (filter_out fst (map fst args ~~ vs));
          fun one_strict v' =
            let
              val UU = mk_bottom (fastype_of v');
              val vs' = map (fn v => if v = v' then UU else v) vs;
              val goal = mk_trp (mk_undef (list_ccomb (con, vs')));
              val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1];
            in prove thy con_betas goal (K tacs) end;
        in map one_strict nonlazy end;

      fun con_defin (con, args) =
        let
          fun iff_disj (t, []) = HOLogic.mk_not t
            | iff_disj (t, ts) = mk_eq (t, foldr1 HOLogic.mk_disj ts);
          val vs = vars_of args;
          val nonlazy = map snd (filter_out fst (map fst args ~~ vs));
          val lhs = mk_undef (list_ccomb (con, vs));
          val rhss = map mk_undef nonlazy;
          val goal = mk_trp (iff_disj (lhs, rhss));
          val rule1 = iso_locale RS @{thm iso.abs_defined_iff};
          val rules = rule1 :: @{thms con_defined_iff_rules};
          val tacs = [simp_tac (HOL_ss addsimps rules) 1];
        in prove thy con_betas goal (K tacs) end;
    in
      val con_stricts = maps con_strict spec';
      val con_defins = map con_defin spec';
      val con_rews = con_stricts @ con_defins;
    end;

    (* prove injectiveness of constructors *)
    local
      fun pgterm rel (con, args) =
        let
          fun prime (Free (n, T)) = Free (n^"'", T)
            | prime t             = t;
          val xs = vars_of args;
          val ys = map prime xs;
          val nonlazy = map snd (filter_out (fst o fst) (args ~~ xs));
          val lhs = rel (list_ccomb (con, xs), list_ccomb (con, ys));
          val rhs = foldr1 mk_conj (ListPair.map rel (xs, ys));
          val concl = mk_trp (mk_eq (lhs, rhs));
          val zs = case args of [_] => [] | _ => nonlazy;
          val assms = map (mk_trp o mk_defined) zs;
          val goal = Logic.list_implies (assms, concl);
        in prove thy con_betas goal end;
      val cons' = filter (fn (_, args) => not (null args)) spec';
    in
      val inverts =
        let
          val abs_below = iso_locale RS @{thm iso.abs_below};
          val rules1 = abs_below :: @{thms sinl_below sinr_below spair_below up_below};
          val rules2 = @{thms up_defined spair_defined ONE_defined}
          val rules = rules1 @ rules2;
          val tacs = [asm_simp_tac (simple_ss addsimps rules) 1];
        in map (fn c => pgterm mk_below c (K tacs)) cons' end;
      val injects =
        let
          val abs_eq = iso_locale RS @{thm iso.abs_eq};
          val rules1 = abs_eq :: @{thms sinl_eq sinr_eq spair_eq up_eq};
          val rules2 = @{thms up_defined spair_defined ONE_defined}
          val rules = rules1 @ rules2;
          val tacs = [asm_simp_tac (simple_ss addsimps rules) 1];
        in map (fn c => pgterm mk_eq c (K tacs)) cons' end;
    end;

    (* prove distinctness of constructors *)
    local
      fun map_dist (f : 'a -> 'a -> 'b) (xs : 'a list) : 'b list =
        flat (map_index (fn (i, x) => map (f x) (nth_drop i xs)) xs);
      fun prime (Free (n, T)) = Free (n^"'", T)
        | prime t             = t;
      fun iff_disj (t, []) = mk_not t
        | iff_disj (t, ts) = mk_eq (t, foldr1 mk_disj ts);
      fun iff_disj2 (t, [], us) = mk_not t
        | iff_disj2 (t, ts, []) = mk_not t
        | iff_disj2 (t, ts, us) =
          mk_eq (t, mk_conj (foldr1 mk_disj ts, foldr1 mk_disj us));
      fun dist_le (con1, args1) (con2, args2) =
        let
          val vs1 = vars_of args1;
          val vs2 = map prime (vars_of args2);
          val zs1 = map snd (filter_out (fst o fst) (args1 ~~ vs1));
          val lhs = mk_below (list_ccomb (con1, vs1), list_ccomb (con2, vs2));
          val rhss = map mk_undef zs1;
          val goal = mk_trp (iff_disj (lhs, rhss));
          val rule1 = iso_locale RS @{thm iso.abs_below};
          val rules = rule1 :: @{thms con_below_iff_rules};
          val tacs = [simp_tac (HOL_ss addsimps rules) 1];
        in prove thy con_betas goal (K tacs) end;
      fun dist_eq (con1, args1) (con2, args2) =
        let
          val vs1 = vars_of args1;
          val vs2 = map prime (vars_of args2);
          val zs1 = map snd (filter_out (fst o fst) (args1 ~~ vs1));
          val zs2 = map snd (filter_out (fst o fst) (args2 ~~ vs2));
          val lhs = mk_eq (list_ccomb (con1, vs1), list_ccomb (con2, vs2));
          val rhss1 = map mk_undef zs1;
          val rhss2 = map mk_undef zs2;
          val goal = mk_trp (iff_disj2 (lhs, rhss1, rhss2));
          val rule1 = iso_locale RS @{thm iso.abs_eq};
          val rules = rule1 :: @{thms con_eq_iff_rules};
          val tacs = [simp_tac (HOL_ss addsimps rules) 1];
        in prove thy con_betas goal (K tacs) end;
    in
      val dist_les = map_dist dist_le spec';
      val dist_eqs = map_dist dist_eq spec';
    end;

    val result =
      {
        con_consts = con_consts,
        con_betas = con_betas,
        exhaust = exhaust,
        casedist = casedist,
        con_compacts = con_compacts,
        con_rews = con_rews,
        inverts = inverts,
        injects = injects,
        dist_les = dist_les,
        dist_eqs = dist_eqs
      };
  in
    (result, thy)
  end;

(******************************************************************************)
(**************** definition and theorems for case combinator *****************)
(******************************************************************************)

fun add_case_combinator
    (spec : (term * (bool * typ) list) list)
    (lhsT : typ)
    (dname : string)
    (case_def : thm)
    (con_betas : thm list)
    (casedist : thm)
    (iso_locale : thm)
    (thy : theory)
    : ((typ -> term) * thm list) * theory =
  let

    (* prove rep/abs rules *)
    val rep_strict = iso_locale RS @{thm iso.rep_strict};
    val abs_inverse = iso_locale RS @{thm iso.abs_iso};

    (* calculate function arguments of case combinator *)
    val resultT = TVar (("'t",0), @{sort pcpo});
    fun fTs T = map (fn (_, args) => map snd args -->> T) spec;
    val fns = Datatype_Prop.indexify_names (map (K "f") spec);
    val fs = map Free (fns ~~ fTs resultT);
    fun caseT T = fTs T -->> (lhsT ->> T);

    (* TODO: move definition of case combinator here *)
    val case_bind = Binding.name (dname ^ "_when");
    val case_name = Sign.full_name thy case_bind;
    fun case_const T = Const (case_name, caseT T);
    val case_app = list_ccomb (case_const resultT, fs);

    (* prove beta reduction rule for case combinator *)
    val case_beta = beta_of_def thy case_def;

    (* prove strictness of case combinator *)
    val case_strict =
      let
        val defs = [case_beta, mk_meta_eq rep_strict];
        val lhs = case_app ` mk_bottom lhsT;
        val goal = mk_trp (mk_eq (lhs, mk_bottom resultT));
        val tacs = [resolve_tac @{thms sscase1 ssplit1 strictify1} 1];
      in prove thy defs goal (K tacs) end;
        
    (* prove rewrites for case combinator *)
    local
      fun one_case (con, args) f =
        let
          val Ts = map snd args;
          val ns = Name.variant_list fns (Datatype_Prop.make_tnames Ts);
          val vs = map Free (ns ~~ Ts);
          val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs));
          val assms = map (mk_trp o mk_defined) nonlazy;
          val lhs = case_app ` list_ccomb (con, vs);
          val rhs = list_ccomb (f, vs);
          val concl = mk_trp (mk_eq (lhs, rhs));
          val goal = Logic.list_implies (assms, concl);
          val defs = case_beta :: con_betas;
          val rules1 = @{thms sscase2 sscase3 ssplit2 fup2 ID1};
          val rules2 = @{thms con_defined_iff_rules};
          val rules = abs_inverse :: rules1 @ rules2;
          val tacs = [asm_simp_tac (beta_ss addsimps rules) 1];
        in prove thy defs goal (K tacs) end;
    in
      val case_apps = map2 one_case spec fs;
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
    (rep_strict_iff : thm)
    (con_betas : thm list)
    (thy : theory)
    : thm list * theory =
  let

    (* define selector functions *)
    val ((sel_consts, sel_defs), thy) =
      let
        fun rangeT s = snd (dest_cfunT (fastype_of s));
        fun mk_outl s = mk_cfcomp (from_sinl (dest_ssumT (rangeT s)), s);
        fun mk_outr s = mk_cfcomp (from_sinr (dest_ssumT (rangeT s)), s);
        fun mk_sfst s = mk_cfcomp (sfst_const (dest_sprodT (rangeT s)), s);
        fun mk_ssnd s = mk_cfcomp (ssnd_const (dest_sprodT (rangeT s)), s);
        fun mk_down s = mk_cfcomp (from_up (dest_upT (rangeT s)), s);

        fun sels_of_arg s (lazy, NONE,   T) = []
          | sels_of_arg s (lazy, SOME b, T) =
            [(b, if lazy then mk_down s else s, NoSyn)];
        fun sels_of_args s [] = []
          | sels_of_args s (v :: []) = sels_of_arg s v
          | sels_of_args s (v :: vs) =
            sels_of_arg (mk_sfst s) v @ sels_of_args (mk_ssnd s) vs;
        fun sels_of_cons s [] = []
          | sels_of_cons s ((con, args) :: []) = sels_of_args s args
          | sels_of_cons s ((con, args) :: cs) =
            sels_of_args (mk_outl s) args @ sels_of_cons (mk_outr s) cs;
        val sel_eqns : (binding * term * mixfix) list =
            sels_of_cons rep_const spec;
      in
        define_consts sel_eqns thy
      end

    (* replace bindings with terms in constructor spec *)
    val spec2 : (term * (bool * term option * typ) list) list =
      let
        fun prep_arg (lazy, NONE, T) sels = ((lazy, NONE, T), sels)
          | prep_arg (lazy, SOME _, T) sels =
            ((lazy, SOME (hd sels), T), tl sels);
        fun prep_con (con, args) sels =
            apfst (pair con) (fold_map prep_arg args sels);
      in
        fst (fold_map prep_con spec sel_consts)
      end;

    (* prove selector strictness rules *)
    val sel_stricts : thm list =
      let
        val rules = rep_strict :: @{thms sel_strict_rules};
        val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1];
        fun sel_strict sel =
          let
            val goal = mk_trp (mk_strict sel);
          in
            prove thy sel_defs goal (K tacs)
          end
      in
        map sel_strict sel_consts
      end

    (* prove selector application rules *)
    val sel_apps : thm list =
      let
        val defs = con_betas @ sel_defs;
        val rules = abs_inv :: @{thms sel_app_rules};
        val tacs = [asm_simp_tac (simple_ss addsimps rules) 1];
        fun sel_apps_of (i, (con, args)) =
          let
            val Ts : typ list = map #3 args;
            val ns : string list = Datatype_Prop.make_tnames Ts;
            val vs : term list = map Free (ns ~~ Ts);
            val con_app : term = list_ccomb (con, vs);
            val vs' : (bool * term) list = map #1 args ~~ vs;
            fun one_same (n, sel, T) =
              let
                val xs = map snd (filter_out fst (nth_drop n vs'));
                val assms = map (mk_trp o mk_defined) xs;
                val concl = mk_trp (mk_eq (sel ` con_app, nth vs n));
                val goal = Logic.list_implies (assms, concl);
              in
                prove thy defs goal (K tacs)
              end;
            fun one_diff (n, sel, T) =
              let
                val goal = mk_trp (mk_eq (sel ` con_app, mk_bottom T));
              in
                prove thy defs goal (K tacs)
              end;
            fun one_con (j, (_, args')) : thm list =
              let
                fun prep (i, (lazy, NONE, T)) = NONE
                  | prep (i, (lazy, SOME sel, T)) = SOME (i, sel, T);
                val sels : (int * term * typ) list =
                  map_filter prep (map_index I args');
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
        val rules = rep_strict_iff :: @{thms sel_defined_iff_rules};
        val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1];
        fun sel_defin sel =
          let
            val (T, U) = dest_cfunT (fastype_of sel);
            val x = Free ("x", T);
            val lhs = mk_eq (sel ` x, mk_bottom U);
            val rhs = mk_eq (x, mk_bottom T);
            val goal = mk_trp (mk_eq (lhs, rhs));
          in
            prove thy sel_defs goal (K tacs)
          end
        fun one_arg (false, SOME sel, T) = SOME (sel_defin sel)
          | one_arg _                    = NONE;
      in
        case spec2 of
          [(con, args)] => map_filter one_arg args
        | _             => []
      end;

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
    (casedist : thm)
    (case_const : typ -> term)
    (case_rews : thm list)
    (thy : theory) =
  let

    fun vars_of args =
      let
        val Ts = map snd args;
        val ns = Datatype_Prop.make_tnames Ts;
      in
        map Free (ns ~~ Ts)
      end;

    (* define discriminator functions *)
    local
      fun dis_fun i (j, (con, args)) =
        let
          val Ts = map snd args;
          val ns = Datatype_Prop.make_tnames Ts;
          val vs = map Free (ns ~~ Ts);
          val tr = if i = j then @{term TT} else @{term FF};
        in
          big_lambdas vs tr
        end;
      fun dis_eqn (i, bind) : binding * term * mixfix =
        let
          val dis_bind = Binding.prefix_name "is_" bind;
          val rhs = list_ccomb (case_const trT, map_index (dis_fun i) spec);
        in
          (dis_bind, rhs, NoSyn)
        end;
    in
      val ((dis_consts, dis_defs), thy) =
          define_consts (map_index dis_eqn bindings) thy
    end;

    (* prove discriminator strictness rules *)
    local
      fun dis_strict dis =
        let val goal = mk_trp (mk_strict dis);
        in prove thy dis_defs goal (K [rtac (hd case_rews) 1]) end;
    in
      val dis_stricts = map dis_strict dis_consts;
    end;

    (* prove discriminator/constructor rules *)
    local
      fun dis_app (i, dis) (j, (con, args)) =
        let
          val Ts = map snd args;
          val ns = Datatype_Prop.make_tnames Ts;
          val vs = map Free (ns ~~ Ts);
          val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs));
          val lhs = dis ` list_ccomb (con, vs);
          val rhs = if i = j then @{term TT} else @{term FF};
          val assms = map (mk_trp o mk_defined) nonlazy;
          val concl = mk_trp (mk_eq (lhs, rhs));
          val goal = Logic.list_implies (assms, concl);
          val tacs = [asm_simp_tac (beta_ss addsimps case_rews) 1];
        in prove thy dis_defs goal (K tacs) end;
      fun one_dis (i, dis) =
          map_index (dis_app (i, dis)) spec;
    in
      val dis_apps = flat (map_index one_dis dis_consts);
    end;

    (* prove discriminator definedness rules *)
    local
      fun dis_defin dis =
        let
          val x = Free ("x", lhsT);
          val simps = dis_apps @ @{thms dist_eq_tr};
          val tacs =
            [rtac @{thm iffI} 1,
             asm_simp_tac (HOL_basic_ss addsimps dis_stricts) 2,
             rtac casedist 1, atac 1,
             DETERM_UNTIL_SOLVED (CHANGED
               (asm_full_simp_tac (simple_ss addsimps simps) 1))];
          val goal = mk_trp (mk_eq (mk_undef (dis ` x), mk_undef x));
        in prove thy [] goal (K tacs) end;
    in
      val dis_defins = map dis_defin dis_consts;
    end;

  in
    (dis_stricts @ dis_defins @ dis_apps, thy)
  end;

(******************************************************************************)
(*************** definitions and theorems for match combinators ***************)
(******************************************************************************)

fun add_match_combinators
    (bindings : binding list)
    (spec : (term * (bool * typ) list) list)
    (lhsT : typ)
    (casedist : thm)
    (case_const : typ -> term)
    (case_rews : thm list)
    (thy : theory) =
  let

    (* get a fresh type variable for the result type *)
    val resultT : typ =
      let
        val ts : string list = map (fst o dest_TFree) (snd (dest_Type lhsT));
        val t : string = Name.variant ts "'t";
      in TFree (t, @{sort pcpo}) end;

    (* define match combinators *)
    local
      val x = Free ("x", lhsT);
      fun k args = Free ("k", map snd args -->> mk_matchT resultT);
      val fail = mk_fail resultT;
      fun mat_fun i (j, (con, args)) =
        let
          val Ts = map snd args;
          val ns = Name.variant_list ["x","k"] (Datatype_Prop.make_tnames Ts);
          val vs = map Free (ns ~~ Ts);
        in
          if i = j then k args else big_lambdas vs fail
        end;
      fun mat_eqn (i, (bind, (con, args))) : binding * term * mixfix =
        let
          val mat_bind = Binding.prefix_name "match_" bind;
          val funs = map_index (mat_fun i) spec
          val body = list_ccomb (case_const (mk_matchT resultT), funs);
          val rhs = big_lambda x (big_lambda (k args) (body ` x));
        in
          (mat_bind, rhs, NoSyn)
        end;
    in
      val ((match_consts, match_defs), thy) =
          define_consts (map_index mat_eqn (bindings ~~ spec)) thy
    end;

  in
    (match_defs, thy)
(*
    (match_stricts @ match_apps, thy)
*)
  end;

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun add_domain_constructors
    (dname : string)
    (lhsT : typ,
     spec : (binding * (bool * binding option * typ) list * mixfix) list)
    (rep_const : term, abs_const : term)
    (rep_iso_thm : thm, abs_iso_thm : thm)
    (case_def : thm)
    (thy : theory) =
  let

    (* prove rep/abs strictness rules *)
    val iso_locale = @{thm iso.intro} OF [abs_iso_thm, rep_iso_thm];
    val rep_strict = iso_locale RS @{thm iso.rep_strict};
    val abs_strict = iso_locale RS @{thm iso.abs_strict};
    val rep_defined_iff = iso_locale RS @{thm iso.rep_defined_iff};
    val abs_defined_iff = iso_locale RS @{thm iso.abs_defined_iff};

    (* define constructor functions *)
    val (con_result, thy) =
      let
        fun prep_arg (lazy, sel, T) = (lazy, T);
        fun prep_con (b, args, mx) = (b, map prep_arg args, mx);
        val con_spec = map prep_con spec;
      in
        add_constructors con_spec abs_const iso_locale thy
      end;
    val {con_consts, con_betas, casedist, ...} = con_result;

    (* define case combinator *)
    val ((case_const : typ -> term, cases : thm list), thy) =
      let
        fun prep_arg (lazy, sel, T) = (lazy, T);
        fun prep_con c (b, args, mx) = (c, map prep_arg args);
        val case_spec = map2 prep_con con_consts spec;
      in
        add_case_combinator case_spec lhsT dname
          case_def con_betas casedist iso_locale thy
      end;

    (* TODO: enable this earlier *)
    val thy = Sign.add_path dname thy;

    (* define and prove theorems for selector functions *)
    val (sel_thms : thm list, thy : theory) =
      let
        val sel_spec : (term * (bool * binding option * typ) list) list =
          map2 (fn con => fn (b, args, mx) => (con, args)) con_consts spec;
      in
        add_selectors sel_spec rep_const
          abs_iso_thm rep_strict rep_defined_iff con_betas thy
      end;

    (* define and prove theorems for discriminator functions *)
    val (dis_thms : thm list, thy : theory) =
      let
        val bindings = map #1 spec;
        fun prep_arg (lazy, sel, T) = (lazy, T);
        fun prep_con c (b, args, mx) = (c, map prep_arg args);
        val dis_spec = map2 prep_con con_consts spec;
      in
        add_discriminators bindings dis_spec lhsT
          casedist case_const cases thy
      end

    (* define and prove theorems for match combinators *)
    val (match_thms : thm list, thy : theory) =
      let
        val bindings = map #1 spec;
        fun prep_arg (lazy, sel, T) = (lazy, T);
        fun prep_con c (b, args, mx) = (c, map prep_arg args);
        val mat_spec = map2 prep_con con_consts spec;
      in
        add_match_combinators bindings mat_spec lhsT
          casedist case_const cases thy
      end

    (* restore original signature path *)
    val thy = Sign.parent_path thy;

    val result =
      { con_consts = con_consts,
        con_betas = con_betas,
        exhaust = #exhaust con_result,
        casedist = casedist,
        con_compacts = #con_compacts con_result,
        con_rews = #con_rews con_result,
        inverts = #inverts con_result,
        injects = #injects con_result,
        dist_les = #dist_les con_result,
        dist_eqs = #dist_eqs con_result,
        cases = cases,
        sel_rews = sel_thms,
        dis_rews = dis_thms,
        match_rews = match_thms };
  in
    (result, thy)
  end;

end;
