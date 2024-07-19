(*  Title:      HOL/Tools/inductive_realizer.ML
    Author:     Stefan Berghofer, TU Muenchen

Program extraction from proofs involving inductive predicates:
Realizers for induction and elimination rules.
*)

signature INDUCTIVE_REALIZER =
sig
  val add_ind_realizers: string -> string list -> theory -> theory
end;

structure InductiveRealizer : INDUCTIVE_REALIZER =
struct

fun thm_name_of thm =
  (case Proofterm.fold_proof_atoms false (fn PThm ({thm_name, ...}, _) => cons thm_name | _ => I)
      [Thm.proof_of thm] [] of
    [(thm_name, _)] => thm_name
  | _ => raise THM ("thm_name_of: bad proof of theorem", 0, [thm]));

val short_name_of = Thm_Name.short o thm_name_of;

fun prf_of thy =
  Thm.transfer thy #>
  Thm.reconstruct_proof_of #>
  Proofterm.expand_proof thy Proofterm.expand_name_empty;

fun subsets [] = [[]]
  | subsets (x::xs) =
      let val ys = subsets xs
      in ys @ map (cons x) ys end;

val pred_of = fst o dest_Const o head_of;

fun strip_all' used names (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (s, T, t)) =
      let val (s', names') = (case names of
          [] => (singleton (Name.variant_list used) s, [])
        | name :: names' => (name, names'))
      in strip_all' (s'::used) names' (subst_bound (Free (s', T), t)) end
  | strip_all' used names ((t as Const (\<^const_name>\<open>Pure.imp\<close>, _) $ P) $ Q) =
      t $ strip_all' used names Q
  | strip_all' _ _ t = t;

fun strip_all t = strip_all' (Term.add_free_names t []) [] t;

fun strip_one name
    (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (s, T, Const (\<^const_name>\<open>Pure.imp\<close>, _) $ P $ Q)) =
      (subst_bound (Free (name, T), P), subst_bound (Free (name, T), Q))
  | strip_one _ (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ P $ Q) = (P, Q);

fun relevant_vars prop = fold (fn ((a, i), T) => fn vs =>
     (case strip_type T of
        (_, Type (s, _)) => if s = \<^type_name>\<open>bool\<close> then (a, T) :: vs else vs
      | _ => vs)) (Term.add_vars prop []) [];

val attach_typeS = Term.smash_sorts \<^sort>\<open>type\<close>;

fun dt_of_intrs thy vs nparms intrs =
  let
    val iTs = rev (Term.add_tvars (Thm.prop_of (hd intrs)) []);
    val (Const (s, _), ts) = strip_comb (HOLogic.dest_Trueprop
      (Logic.strip_imp_concl (Thm.prop_of (hd intrs))));
    val params = map dest_Var (take nparms ts);
    val tname = Binding.name (space_implode "_" (Long_Name.base_name s ^ "T" :: vs));
    fun constr_of_intr intr = (Binding.name (Long_Name.base_name (short_name_of intr)),
      map (Logic.unvarifyT_global o snd)
        (subtract (op =) params (rev (Term.add_vars (Thm.prop_of intr) []))) @
      filter_out (equal Extraction.nullT)
        (map (Logic.unvarifyT_global o Extraction.etype_of thy vs []) (Thm.prems_of intr)), NoSyn);
  in
    ((tname, map (rpair dummyS) (map (fn a => "'" ^ a) vs @ map (fst o fst) iTs), NoSyn),
      map constr_of_intr intrs)
  end;

fun mk_rlz T = Const ("realizes", [T, HOLogic.boolT] ---> HOLogic.boolT);

(** turn "P" into "%r x. realizes r (P x)" **)

fun gen_rvar vs (t as Var ((a, 0), T)) =
      if body_type T <> HOLogic.boolT then t else
        let
          val U = TVar (("'" ^ a, 0), [])
          val Ts = binder_types T;
          val i = length Ts;
          val xs = map (pair "x") Ts;
          val u = list_comb (t, map Bound (i - 1 downto 0))
        in 
          if member (op =) vs a then
            fold_rev Term.abs (("r", U) :: xs) (mk_rlz U $ Bound i $ u)
          else
            fold_rev Term.abs xs (mk_rlz Extraction.nullT $ Extraction.nullt $ u)
        end
  | gen_rvar _ t = t;

fun mk_realizes_eqn n vs nparms intrs =
  let
    val intr = Term.strip_sorts (Thm.prop_of (hd intrs));
    val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl intr);
    val iTs = rev (Term.add_tvars intr []);
    val Tvs = map TVar iTs;
    val (h as Const (s, T), us) = strip_comb concl;
    val params = List.take (us, nparms);
    val elTs = List.drop (binder_types T, nparms);
    val predT = elTs ---> HOLogic.boolT;
    val used = map (fst o fst o dest_Var) params;
    val xs = map (Var o apfst (rpair 0))
      (Name.variant_list used (replicate (length elTs) "x") ~~ elTs);
    val rT = if n then Extraction.nullT
      else Type (space_implode "_" (s ^ "T" :: vs),
        map (fn a => TVar (("'" ^ a, 0), [])) vs @ Tvs);
    val r = if n then Extraction.nullt else Var ((Long_Name.base_name s, 0), rT);
    val S = list_comb (h, params @ xs);
    val rvs = relevant_vars S;
    val vs' = subtract (op =) vs (map fst rvs);
    val rname = space_implode "_" (s ^ "R" :: vs);

    fun mk_Tprem n v =
      let val T = (the o AList.lookup (op =) rvs) v
      in (Const ("typeof", T --> Type ("Type", [])) $ Var ((v, 0), T),
        Extraction.mk_typ (if n then Extraction.nullT
          else TVar (("'" ^ v, 0), [])))
      end;

    val prems = map (mk_Tprem true) vs' @ map (mk_Tprem false) vs;
    val ts = map (gen_rvar vs) params;
    val argTs = map fastype_of ts;

  in ((prems, (Const ("typeof", HOLogic.boolT --> Type ("Type", [])) $ S,
       Extraction.mk_typ rT)),
    (prems, (mk_rlz rT $ r $ S,
       if n then list_comb (Const (rname, argTs ---> predT), ts @ xs)
       else list_comb (Const (rname, argTs @ [rT] ---> predT), ts @ [r] @ xs))))
  end;

fun fun_of_prem thy rsets vs params rule ivs intr =
  let
    val ctxt = Proof_Context.init_global thy
    val args = map (Free o apfst fst o dest_Var) ivs;
    val args' = map (Free o apfst fst)
      (subtract (op =) params (Term.add_vars (Thm.prop_of intr) []));
    val rule' = strip_all rule;
    val conclT = Extraction.etype_of thy vs [] (Logic.strip_imp_concl rule');
    val used = map (fst o dest_Free) args;

    val is_rec = exists_Const (fn (c, _) => member (op =) rsets c);

    fun is_meta (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (s, _, P)) = is_meta P
      | is_meta (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ Q) = is_meta Q
      | is_meta (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) =
          (case head_of t of
            Const (s, _) => can (Inductive.the_inductive_global ctxt) s
          | _ => true)
      | is_meta _ = false;

    fun fun_of ts rts args used (prem :: prems) =
          let
            val T = Extraction.etype_of thy vs [] prem;
            val [x, r] = Name.variant_list used ["x", "r"]
          in if T = Extraction.nullT
            then fun_of ts rts args used prems
            else if is_rec prem then
              if is_meta prem then
                let
                  val prem' :: prems' = prems;
                  val U = Extraction.etype_of thy vs [] prem';
                in
                  if U = Extraction.nullT
                  then fun_of (Free (x, T) :: ts)
                    (Free (r, binder_types T ---> HOLogic.unitT) :: rts)
                    (Free (x, T) :: args) (x :: r :: used) prems'
                  else fun_of (Free (x, T) :: ts) (Free (r, U) :: rts)
                    (Free (r, U) :: Free (x, T) :: args) (x :: r :: used) prems'
                end
              else
                (case strip_type T of
                  (Ts, Type (\<^type_name>\<open>Product_Type.prod\<close>, [T1, T2])) =>
                    let
                      val fx = Free (x, Ts ---> T1);
                      val fr = Free (r, Ts ---> T2);
                      val bs = map Bound (length Ts - 1 downto 0);
                      val t =
                        fold_rev (Term.abs o pair "z") Ts
                          (HOLogic.mk_prod (list_comb (fx, bs), list_comb (fr, bs)));
                    in fun_of (fx :: ts) (fr :: rts) (t::args) (x :: r :: used) prems end
                | (Ts, U) => fun_of (Free (x, T) :: ts)
                    (Free (r, binder_types T ---> HOLogic.unitT) :: rts)
                    (Free (x, T) :: args) (x :: r :: used) prems)
            else fun_of (Free (x, T) :: ts) rts (Free (x, T) :: args)
              (x :: used) prems
          end
      | fun_of ts rts args used [] =
          let val xs = rev (rts @ ts)
          in if conclT = Extraction.nullT
            then fold_rev (absfree o dest_Free) xs HOLogic.unit
            else fold_rev (absfree o dest_Free) xs
              (list_comb
                (Free ("r" ^ Long_Name.base_name (short_name_of intr),
                  map fastype_of (rev args) ---> conclT), rev args))
          end

  in fun_of args' [] (rev args) used (Logic.strip_imp_prems rule') end;

fun indrule_realizer thy induct raw_induct rsets params vs rec_names rss intrs dummies =
  let
    val concls = HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of raw_induct));
    val premss = map_filter (fn (s, rs) => if member (op =) rsets s then
      SOME (rs, map (fn (_, r) => nth (Thm.prems_of raw_induct)
        (find_index (fn prp => prp = Thm.prop_of r) (map Thm.prop_of intrs))) rs) else NONE) rss;
    val fs = maps (fn ((intrs, prems), dummy) =>
      let
        val fs = map (fn (rule, (ivs, intr)) =>
          fun_of_prem thy rsets vs params rule ivs intr) (prems ~~ intrs)
      in
        if dummy then Const (\<^const_name>\<open>default\<close>,
            HOLogic.unitT --> body_type (fastype_of (hd fs))) :: fs
        else fs
      end) (premss ~~ dummies);
    val frees = fold Term.add_frees fs [];
    val Ts = map fastype_of fs;
    fun name_of_fn intr = "r" ^ Long_Name.base_name (short_name_of intr)
  in
    fst (fold_map (fn concl => fn names =>
      let val T = Extraction.etype_of thy vs [] concl
      in if T = Extraction.nullT then (Extraction.nullt, names) else
        let
          val Type ("fun", [U, _]) = T;
          val a :: names' = names
        in
          (fold_rev absfree (("x", U) :: map_filter (fn intr =>
            Option.map (pair (name_of_fn intr))
              (AList.lookup (op =) frees (name_of_fn intr))) intrs)
            (list_comb (Const (a, Ts ---> T), fs) $ Free ("x", U)), names')
        end
      end) concls rec_names)
  end;

fun add_dummy name dname (x as (_, ((s, vs, mx), cs))) =
  if Binding.eq_name (name, s)
  then (true, ((s, vs, mx), (dname, [HOLogic.unitT], NoSyn) :: cs))
  else x;

fun add_dummies f [] _ thy =
      (([], NONE), thy)
  | add_dummies f dts used thy =
      thy
      |> f (map snd dts)
      |-> (fn dtinfo => pair (map fst dts, SOME dtinfo))
    handle BNF_FP_Util.EMPTY_DATATYPE name' =>
      let
        val name = Long_Name.base_name name';
        val dname = singleton (Name.variant_list used) "Dummy";
      in
        thy
        |> add_dummies f (map (add_dummy (Binding.name name) (Binding.name dname)) dts) (dname :: used)
      end;

fun mk_realizer thy vs (name, rule, rrule, rlz, rt) =
  let
    val rvs = map fst (relevant_vars (Thm.prop_of rule));
    val xs = rev (Term.add_vars (Thm.prop_of rule) []);
    val vs1 = map Var (filter_out (fn ((a, _), _) => member (op =) rvs a) xs);
    val rlzvs = rev (Term.add_vars (Thm.prop_of rrule) []);
    val vs2 = map (fn (ixn, _) => Var (ixn, (the o AList.lookup (op =) rlzvs) ixn)) xs;
    val rs = map Var (subtract (op = o apply2 fst) xs rlzvs);
    val rlz' = fold_rev Logic.all rs (Thm.prop_of rrule)
  in (name, (vs,
    if rt = Extraction.nullt then rt else fold_rev lambda vs1 rt,
    Extraction.abs_corr_shyps thy rule vs vs2
      (Proof_Rewrite_Rules.un_hhf_proof rlz' (attach_typeS rlz)
         (fold_rev Proofterm.forall_intr_proof' rs (prf_of thy rrule)))))
  end;

fun rename tab = map (fn x => the_default x (AList.lookup op = tab x));

fun add_ind_realizer rsets intrs induct raw_induct elims vs thy =
  let
    val qualifier = Long_Name.qualifier (short_name_of induct);
    val inducts = Global_Theory.get_thms thy (Long_Name.qualify qualifier "inducts");
    val iTs = rev (Term.add_tvars (Thm.prop_of (hd intrs)) []);
    val ar = length vs + length iTs;
    val params = Inductive.params_of raw_induct;
    val arities = Inductive.arities_of raw_induct;
    val nparms = length params;
    val params' = map dest_Var params;
    val rss = Inductive.partition_rules raw_induct intrs;
    val rss' = map (fn (((s, rs), (_, arity)), elim) =>
      (s, (Inductive.infer_intro_vars thy elim arity rs ~~ rs)))
        (rss ~~ arities ~~ elims);
    val (prfx, _) = split_last (Long_Name.explode (fst (hd rss)));
    val tnames = map (fn s => space_implode "_" (s ^ "T" :: vs)) rsets;

    val thy1 = thy |>
      Sign.root_path |>
      Sign.add_path (Long_Name.implode prfx);
    val (ty_eqs, rlz_eqs) = split_list
      (map (fn (s, rs) => mk_realizes_eqn (not (member (op =) rsets s)) vs nparms rs) rss);

    val thy1' = thy1 |>
      Sign.add_types_global
        (map (fn s => (Binding.name (Long_Name.base_name s), ar, NoSyn)) tnames) |>
      Extraction.add_typeof_eqns_i ty_eqs;
    val dts = map_filter (fn (s, rs) => if member (op =) rsets s then
      SOME (dt_of_intrs thy1' vs nparms rs) else NONE) rss;

    (** datatype representing computational content of inductive set **)

    val ((dummies, some_dt_names), thy2) =
      thy1
      |> add_dummies (BNF_LFP_Compat.add_datatype [BNF_LFP_Compat.Kill_Type_Args])
        (map (pair false) dts) []
      ||> Extraction.add_typeof_eqns_i ty_eqs
      ||> Extraction.add_realizes_eqns_i rlz_eqs;
    val dt_names = these some_dt_names;
    val case_thms = map (#case_rewrites o BNF_LFP_Compat.the_info thy2 []) dt_names;
    val rec_thms =
      if null dt_names then []
      else #rec_rewrites (BNF_LFP_Compat.the_info thy2 [] (hd dt_names));
    val rec_names = distinct (op =) (map (fst o dest_Const o head_of o fst o
      HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) rec_thms);
    val (constrss, _) = fold_map (fn (s, rs) => fn (recs, dummies) =>
      if member (op =) rsets s then
        let
          val (d :: dummies') = dummies;
          val (recs1, recs2) = chop (length rs) (if d then tl recs else recs)
        in (map (head_of o hd o rev o snd o strip_comb o fst o
          HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) recs1, (recs2, dummies'))
        end
      else (replicate (length rs) Extraction.nullt, (recs, dummies)))
        rss (rec_thms, dummies);
    val rintrs = map (fn (intr, c) => attach_typeS (Envir.eta_contract
      (Extraction.realizes_of thy2 vs
        (if c = Extraction.nullt then c else list_comb (c, map Var (rev
          (subtract (op =) params' (Term.add_vars (Thm.prop_of intr) []))))) (Thm.prop_of intr))))
            (maps snd rss ~~ flat constrss);
    val (rlzpreds, rlzpreds') =
      rintrs |> map (fn rintr =>
        let
          val Const (s, T) = head_of (HOLogic.dest_Trueprop (Logic.strip_assums_concl rintr));
          val s' = Long_Name.base_name s;
          val T' = Logic.unvarifyT_global T;
        in (((s', T'), NoSyn), (Const (s, T'), Free (s', T'))) end)
      |> distinct (op = o apply2 (#1 o #1))
      |> map (apfst (apfst (apfst Binding.name)))
      |> split_list;

    val rlzparams = map (fn Var ((s, _), T) => (s, Logic.unvarifyT_global T))
      (List.take (snd (strip_comb
        (HOLogic.dest_Trueprop (Logic.strip_assums_concl (hd rintrs)))), nparms));

    (** realizability predicate **)

    val (ind_info, thy3') = thy2 |>
      Named_Target.theory_map_result Inductive.transform_result
      (Inductive.add_inductive
        {quiet_mode = false, verbose = false, alt_name = Binding.empty, coind = false,
          no_elim = false, no_ind = false, skip_mono = false}
        rlzpreds rlzparams (map (fn (rintr, intr) =>
          ((Binding.name (Long_Name.base_name (short_name_of intr)), []),
           subst_atomic rlzpreds' (Logic.unvarify_global rintr)))
             (rintrs ~~ maps snd rss)) []) ||>
      Sign.root_path;
    val thy3 = fold (Global_Theory.hide_fact false o short_name_of) (#intrs ind_info) thy3';

    (** realizer for induction rule **)

    val Ps = map_filter (fn _ $ M $ P => if member (op =) rsets (pred_of M) then
      SOME (fst (fst (dest_Var (head_of P)))) else NONE)
        (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of raw_induct)));

    fun add_ind_realizer Ps thy =
      let
        val vs' = rename (map (apply2 (fst o fst o dest_Var))
          (params ~~ List.take (snd (strip_comb (HOLogic.dest_Trueprop
            (hd (Thm.prems_of (hd inducts))))), nparms))) vs;
        val rs = indrule_realizer thy induct raw_induct rsets params'
          (vs' @ Ps) rec_names rss' intrs dummies;
        val rlzs = map (fn (r, ind) => Extraction.realizes_of thy (vs' @ Ps) r
          (Thm.prop_of ind)) (rs ~~ inducts);
        val used = fold Term.add_free_names rlzs [];
        val rnames = Name.variant_list used (replicate (length inducts) "r");
        val rnames' = Name.variant_list
          (used @ rnames) (replicate (length intrs) "s");
        val rlzs' as (prems, _, _) :: _ = map (fn (rlz, name) =>
          let
            val (P, Q) = strip_one name (Logic.unvarify_global rlz);
            val Q' = strip_all' [] rnames' Q
          in
            (Logic.strip_imp_prems Q', P, Logic.strip_imp_concl Q')
          end) (rlzs ~~ rnames);
        val concl = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map
          (fn (_, _ $ P, _ $ Q) => HOLogic.mk_imp (P, Q)) rlzs'));
        val rews = map mk_meta_eq (@{thm fst_conv} :: @{thm snd_conv} :: rec_thms);
        val thm = Goal.prove_global thy []
          (map attach_typeS prems) (attach_typeS concl)
          (fn {context = ctxt, prems} => EVERY
          [resolve_tac ctxt [#raw_induct ind_info] 1,
           rewrite_goals_tac ctxt rews,
           REPEAT ((resolve_tac ctxt prems THEN_ALL_NEW EVERY'
             [K (rewrite_goals_tac ctxt rews), Object_Logic.atomize_prems_tac ctxt,
              DEPTH_SOLVE_1 o
              FIRST' [assume_tac ctxt, eresolve_tac ctxt [allE], eresolve_tac ctxt [impE]]]) 1)]);
        val (thm', thy') = Global_Theory.store_thm (Binding.qualified_name (space_implode "_"
          (Long_Name.qualify qualifier "induct" :: vs' @ Ps @ ["correctness"])), thm) thy;
        val thms = map (fn th => zero_var_indexes (rotate_prems ~1 (th RS mp)))
          (Old_Datatype_Aux.split_conj_thm thm');
        val ([thms'], thy'') = Global_Theory.add_thmss
          [((Binding.qualified_name (space_implode "_"
             (Long_Name.qualify qualifier "inducts" :: vs' @ Ps @
               ["correctness"])), thms), [])] thy';
        val realizers = inducts ~~ thms' ~~ rlzs ~~ rs;
      in
        Extraction.add_realizers_i
          (map (fn (((ind, corr), rlz), r) =>
              mk_realizer thy'' (vs' @ Ps) (Thm.derivation_name ind, ind, corr, rlz, r))
            realizers @ (case realizers of
             [(((ind, corr), rlz), r)] =>
               [mk_realizer thy'' (vs' @ Ps) ((Long_Name.qualify qualifier "induct", 0),
                  ind, corr, rlz, r)]
           | _ => [])) thy''
      end;

    (** realizer for elimination rules **)

    val case_names = map (fst o dest_Const o head_of o fst o HOLogic.dest_eq o
      HOLogic.dest_Trueprop o Thm.prop_of o hd) case_thms;

    fun add_elim_realizer Ps
      (((((elim, elimR), intrs), case_thms), case_name), dummy) thy =
      let
        val (prem :: prems) = Thm.prems_of elim;
        fun reorder1 (p, (_, intr)) =
          fold (fn ((s, _), T) => Logic.all (Free (s, T)))
            (subtract (op =) params' (Term.add_vars (Thm.prop_of intr) []))
            (strip_all p);
        fun reorder2 ((ivs, intr), i) =
          let val fs = subtract (op =) params' (Term.add_vars (Thm.prop_of intr) [])
          in fold (lambda o Var) fs (list_comb (Bound (i + length ivs), ivs)) end;
        val p = Logic.list_implies
          (map reorder1 (prems ~~ intrs) @ [prem], Thm.concl_of elim);
        val T' = Extraction.etype_of thy (vs @ Ps) [] p;
        val T = if dummy then (HOLogic.unitT --> body_type T') --> T' else T';
        val Ts = map (Extraction.etype_of thy (vs @ Ps) []) (Thm.prems_of elim);
        val r =
          if null Ps then Extraction.nullt
          else
            fold_rev (Term.abs o pair "x") Ts
              (list_comb (Const (case_name, T),
                (if dummy then
                   [Abs ("x", HOLogic.unitT, Const (\<^const_name>\<open>default\<close>, body_type T))]
                 else []) @
                map reorder2 (intrs ~~ (length prems - 1 downto 0)) @
                [Bound (length prems)]));
        val rlz = Extraction.realizes_of thy (vs @ Ps) r (Thm.prop_of elim);
        val rlz' = attach_typeS (strip_all (Logic.unvarify_global rlz));
        val rews = map mk_meta_eq case_thms;
        val thm = Goal.prove_global thy []
          (Logic.strip_imp_prems rlz') (Logic.strip_imp_concl rlz')
          (fn {context = ctxt, prems, ...} => EVERY
            [cut_tac (hd prems) 1,
             eresolve_tac ctxt [elimR] 1,
             ALLGOALS (asm_simp_tac (put_simpset HOL_basic_ss ctxt)),
             rewrite_goals_tac ctxt rews,
             REPEAT ((resolve_tac ctxt prems THEN_ALL_NEW (Object_Logic.atomize_prems_tac ctxt THEN'
               DEPTH_SOLVE_1 o
               FIRST' [assume_tac ctxt, eresolve_tac ctxt [allE], eresolve_tac ctxt [impE]])) 1)]);
        val (thm', thy') = Global_Theory.store_thm (Binding.qualified_name (space_implode "_"
          (short_name_of elim :: vs @ Ps @ ["correctness"])), thm) thy
      in
        Extraction.add_realizers_i
          [mk_realizer thy' (vs @ Ps) (thm_name_of elim, elim, thm', rlz, r)] thy'
      end;

    (** add realizers to theory **)

    val thy4 = fold add_ind_realizer (subsets Ps) thy3;
    val thy5 = Extraction.add_realizers_i
      (map (mk_realizer thy4 vs) (map (fn (((rule, rrule), rlz), c) =>
         (thm_name_of rule, rule, rrule, rlz,
            list_comb (c, map Var (subtract (op =) params' (rev (Term.add_vars (Thm.prop_of rule) []))))))
              (maps snd rss ~~ #intrs ind_info ~~ rintrs ~~ flat constrss))) thy4;
    val elimps = map_filter (fn ((s, intrs), p) =>
      if member (op =) rsets s then SOME (p, intrs) else NONE)
        (rss' ~~ (elims ~~ #elims ind_info));
    val thy6 =
      fold (fn p as (((((elim, _), _), _), _), _) =>
        add_elim_realizer [] p #>
        add_elim_realizer [fst (fst (dest_Var (HOLogic.dest_Trueprop (Thm.concl_of elim))))] p)
      (elimps ~~ case_thms ~~ case_names ~~ dummies) thy5;

  in Sign.restore_naming thy thy6 end;

fun add_ind_realizers name rsets thy =
  let
    val (_, {intrs, induct, raw_induct, elims, ...}) =
      Inductive.the_inductive_global (Proof_Context.init_global thy) name;
    val vss = sort (int_ord o apply2 length)
      (subsets (map fst (relevant_vars (Thm.concl_of (hd intrs)))))
  in
    fold_rev (add_ind_realizer rsets intrs induct raw_induct elims) vss thy
  end

fun rlz_attrib arg = Thm.declaration_attribute (fn thm => Context.mapping
  let
    fun err () = error "ind_realizer: bad rule";
    val sets =
      (case HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of thm)) of
           [_] => [pred_of (HOLogic.dest_Trueprop (hd (Thm.prems_of thm)))]
         | xs => map (pred_of o fst o HOLogic.dest_imp) xs)
         handle TERM _ => err () | List.Empty => err ();
  in 
    add_ind_realizers (hd sets)
      (case arg of
        NONE => sets | SOME NONE => []
      | SOME (SOME sets') => subtract (op =) sets' sets)
  end I);

val _ = Theory.setup (Attrib.setup \<^binding>\<open>ind_realizer\<close>
  ((Scan.option (Scan.lift (Args.$$$ "irrelevant") |--
    Scan.option (Scan.lift (Args.colon) |--
      Scan.repeat1 (Args.const {proper = true, strict = true})))) >> rlz_attrib)
  "add realizers for inductive set");

end;
