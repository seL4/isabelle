(*  Title:      HOL/Nominal/nominal_inductive.ML
    Author:     Stefan Berghofer, TU Muenchen

Infrastructure for proving equivariance and strong induction theorems
for inductive predicates involving nominal datatypes.
*)

signature NOMINAL_INDUCTIVE =
sig
  val prove_strong_ind: string -> (string * string list) list -> local_theory -> Proof.state
  val prove_eqvt: string -> string list -> local_theory -> local_theory
end

structure NominalInductive : NOMINAL_INDUCTIVE =
struct

val inductive_forall_def = @{thm induct_forall_def};
val inductive_atomize = @{thms induct_atomize};
val inductive_rulify = @{thms induct_rulify};

fun rulify_term thy = Raw_Simplifier.rewrite_term thy inductive_rulify [];

val atomize_conv =
  Raw_Simplifier.rewrite_cterm (true, false, false) (K (K NONE))
    (HOL_basic_ss addsimps inductive_atomize);
val atomize_intr = Conv.fconv_rule (Conv.prems_conv ~1 atomize_conv);
fun atomize_induct ctxt = Conv.fconv_rule (Conv.prems_conv ~1
  (Conv.params_conv ~1 (K (Conv.prems_conv ~1 atomize_conv)) ctxt));

fun preds_of ps t = inter (op = o apsnd dest_Free) ps (Term.add_frees t []);

val fresh_prod = @{thm fresh_prod};

val perm_bool = mk_meta_eq @{thm perm_bool_def};
val perm_boolI = @{thm perm_boolI};
val (_, [perm_boolI_pi, _]) = Drule.strip_comb (snd (Thm.dest_comb
  (Drule.strip_imp_concl (cprop_of perm_boolI))));

fun mk_perm_bool pi th = th RS Drule.cterm_instantiate
  [(perm_boolI_pi, pi)] perm_boolI;

fun mk_perm_bool_simproc names = Simplifier.simproc_global_i
  (theory_of_thm perm_bool) "perm_bool" [@{term "perm pi x"}] (fn thy => fn ss =>
    fn Const (@{const_name Nominal.perm}, _) $ _ $ t =>
         if member (op =) names (the_default "" (try (head_of #> dest_Const #> fst) t))
         then SOME perm_bool else NONE
     | _ => NONE);

fun transp ([] :: _) = []
  | transp xs = map hd xs :: transp (map tl xs);

fun add_binders thy i (t as (_ $ _)) bs = (case strip_comb t of
      (Const (s, T), ts) => (case strip_type T of
        (Ts, Type (tname, _)) =>
          (case NominalDatatype.get_nominal_datatype thy tname of
             NONE => fold (add_binders thy i) ts bs
           | SOME {descr, index, ...} => (case AList.lookup op =
                 (#3 (the (AList.lookup op = descr index))) s of
               NONE => fold (add_binders thy i) ts bs
             | SOME cargs => fst (fold (fn (xs, x) => fn (bs', cargs') =>
                 let val (cargs1, (u, _) :: cargs2) = chop (length xs) cargs'
                 in (add_binders thy i u
                   (fold (fn (u, T) =>
                      if exists (fn j => j < i) (loose_bnos u) then I
                      else insert (op aconv o pairself fst)
                        (incr_boundvars (~i) u, T)) cargs1 bs'), cargs2)
                 end) cargs (bs, ts ~~ Ts))))
      | _ => fold (add_binders thy i) ts bs)
    | (u, ts) => add_binders thy i u (fold (add_binders thy i) ts bs))
  | add_binders thy i (Abs (_, _, t)) bs = add_binders thy (i + 1) t bs
  | add_binders thy i _ bs = bs;

fun split_conj f names (Const (@{const_name HOL.conj}, _) $ p $ q) _ = (case head_of p of
      Const (name, _) =>
        if member (op =) names name then SOME (f p q) else NONE
    | _ => NONE)
  | split_conj _ _ _ _ = NONE;

fun strip_all [] t = t
  | strip_all (_ :: xs) (Const (@{const_name All}, _) $ Abs (s, T, t)) = strip_all xs t;

(*********************************************************************)
(* maps  R ... & (ALL pi_1 ... pi_n z. P z (pi_1 o ... o pi_n o t))  *)
(* or    ALL pi_1 ... pi_n z. P z (pi_1 o ... o pi_n o t)            *)
(* to    R ... & id (ALL z. P z (pi_1 o ... o pi_n o t))             *)
(* or    id (ALL z. P z (pi_1 o ... o pi_n o t))                     *)
(*                                                                   *)
(* where "id" protects the subformula from simplification            *)
(*********************************************************************)

fun inst_conj_all names ps pis (Const (@{const_name HOL.conj}, _) $ p $ q) _ =
      (case head_of p of
         Const (name, _) =>
           if member (op =) names name then SOME (HOLogic.mk_conj (p,
             Const (@{const_name Fun.id}, HOLogic.boolT --> HOLogic.boolT) $
               (subst_bounds (pis, strip_all pis q))))
           else NONE
       | _ => NONE)
  | inst_conj_all names ps pis t u =
      if member (op aconv) ps (head_of u) then
        SOME (Const (@{const_name Fun.id}, HOLogic.boolT --> HOLogic.boolT) $
          (subst_bounds (pis, strip_all pis t)))
      else NONE
  | inst_conj_all _ _ _ _ _ = NONE;

fun inst_conj_all_tac k = EVERY
  [TRY (EVERY [etac conjE 1, rtac conjI 1, atac 1]),
   REPEAT_DETERM_N k (etac allE 1),
   simp_tac (HOL_basic_ss addsimps [@{thm id_apply}]) 1];

fun map_term f t u = (case f t u of
      NONE => map_term' f t u | x => x)
and map_term' f (t $ u) (t' $ u') = (case (map_term f t t', map_term f u u') of
      (NONE, NONE) => NONE
    | (SOME t'', NONE) => SOME (t'' $ u)
    | (NONE, SOME u'') => SOME (t $ u'')
    | (SOME t'', SOME u'') => SOME (t'' $ u''))
  | map_term' f (Abs (s, T, t)) (Abs (s', T', t')) = (case map_term f t t' of
      NONE => NONE
    | SOME t'' => SOME (Abs (s, T, t'')))
  | map_term' _ _ _ = NONE;

(*********************************************************************)
(*         Prove  F[f t]  from  F[t],  where F is monotone           *)
(*********************************************************************)

fun map_thm ctxt f tac monos opt th =
  let
    val prop = prop_of th;
    fun prove t =
      Goal.prove ctxt [] [] t (fn _ =>
        EVERY [cut_facts_tac [th] 1, etac rev_mp 1,
          REPEAT_DETERM (FIRSTGOAL (resolve_tac monos)),
          REPEAT_DETERM (rtac impI 1 THEN (atac 1 ORELSE tac))])
  in Option.map prove (map_term f prop (the_default prop opt)) end;

val eta_contract_cterm = Thm.dest_arg o Thm.cprop_of o Thm.eta_conversion;

fun first_order_matchs pats objs = Thm.first_order_match
  (eta_contract_cterm (Conjunction.mk_conjunction_balanced pats),
   eta_contract_cterm (Conjunction.mk_conjunction_balanced objs));

fun first_order_mrs ths th = ths MRS
  Thm.instantiate (first_order_matchs (cprems_of th) (map cprop_of ths)) th;

fun prove_strong_ind s avoids ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ({names, ...}, {raw_induct, intrs, elims, ...}) =
      Inductive.the_inductive ctxt (Sign.intern_const thy s);
    val ind_params = Inductive.params_of raw_induct;
    val raw_induct = atomize_induct ctxt raw_induct;
    val elims = map (atomize_induct ctxt) elims;
    val monos = Inductive.get_monos ctxt;
    val eqvt_thms = NominalThmDecls.get_eqvt_thms ctxt;
    val _ = (case subtract (op =) (fold (Term.add_const_names o Thm.prop_of) eqvt_thms []) names of
        [] => ()
      | xs => error ("Missing equivariance theorem for predicate(s): " ^
          commas_quote xs));
    val induct_cases = map (fst o fst) (fst (Rule_Cases.get (the
      (Induct.lookup_inductP ctxt (hd names)))));
    val ([raw_induct'], ctxt') = Variable.import_terms false [prop_of raw_induct] ctxt;
    val concls = raw_induct' |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop |>
      HOLogic.dest_conj |> map (HOLogic.dest_imp ##> strip_comb);
    val ps = map (fst o snd) concls;

    val _ = (case duplicates (op = o pairself fst) avoids of
        [] => ()
      | xs => error ("Duplicate case names: " ^ commas_quote (map fst xs)));
    val _ = assert_all (null o duplicates op = o snd) avoids
      (fn (a, _) => error ("Duplicate variable names for case " ^ quote a));
    val _ = (case subtract (op =) induct_cases (map fst avoids) of
        [] => ()
      | xs => error ("No such case(s) in inductive definition: " ^ commas_quote xs));
    val avoids' = if null induct_cases then replicate (length intrs) ("", [])
      else map (fn name =>
        (name, the_default [] (AList.lookup op = avoids name))) induct_cases;
    fun mk_avoids params (name, ps) =
      let val k = length params - 1
      in map (fn x => case find_index (equal x o fst) params of
          ~1 => error ("No such variable in case " ^ quote name ^
            " of inductive definition: " ^ quote x)
        | i => (Bound (k - i), snd (nth params i))) ps
      end;

    val prems = map (fn (prem, avoid) =>
      let
        val prems = map (incr_boundvars 1) (Logic.strip_assums_hyp prem);
        val concl = incr_boundvars 1 (Logic.strip_assums_concl prem);
        val params = Logic.strip_params prem
      in
        (params,
         fold (add_binders thy 0) (prems @ [concl]) [] @
           map (apfst (incr_boundvars 1)) (mk_avoids params avoid),
         prems, strip_comb (HOLogic.dest_Trueprop concl))
      end) (Logic.strip_imp_prems raw_induct' ~~ avoids');

    val atomTs = distinct op = (maps (map snd o #2) prems);
    val ind_sort = if null atomTs then HOLogic.typeS
      else Sign.minimize_sort thy (Sign.certify_sort thy (map (fn T => Sign.intern_class thy
        ("fs_" ^ Long_Name.base_name (fst (dest_Type T)))) atomTs));
    val (fs_ctxt_tyname, _) = Name.variant "'n" (Variable.names_of ctxt');
    val ([fs_ctxt_name], ctxt'') = Variable.variant_fixes ["z"] ctxt';
    val fsT = TFree (fs_ctxt_tyname, ind_sort);

    val inductive_forall_def' = Drule.instantiate'
      [SOME (ctyp_of thy fsT)] [] inductive_forall_def;

    fun lift_pred' t (Free (s, T)) ts =
      list_comb (Free (s, fsT --> T), t :: ts);
    val lift_pred = lift_pred' (Bound 0);

    fun lift_prem (t as (f $ u)) =
          let val (p, ts) = strip_comb t
          in
            if member (op =) ps p then HOLogic.mk_induct_forall fsT $
              Abs ("z", fsT, lift_pred p (map (incr_boundvars 1) ts))
            else lift_prem f $ lift_prem u
          end
      | lift_prem (Abs (s, T, t)) = Abs (s, T, lift_prem t)
      | lift_prem t = t;

    fun mk_distinct [] = []
      | mk_distinct ((x, T) :: xs) = map_filter (fn (y, U) =>
          if T = U then SOME (HOLogic.mk_Trueprop
            (HOLogic.mk_not (HOLogic.eq_const T $ x $ y)))
          else NONE) xs @ mk_distinct xs;

    fun mk_fresh (x, T) = HOLogic.mk_Trueprop
      (NominalDatatype.fresh_const T fsT $ x $ Bound 0);

    val (prems', prems'') = split_list (map (fn (params, bvars, prems, (p, ts)) =>
      let
        val params' = params @ [("y", fsT)];
        val prem = Logic.list_implies
          (map mk_fresh bvars @ mk_distinct bvars @
           map (fn prem =>
             if null (preds_of ps prem) then prem
             else lift_prem prem) prems,
           HOLogic.mk_Trueprop (lift_pred p ts));
        val vs = map (Var o apfst (rpair 0)) (Term.rename_wrt_term prem params')
      in
        (Logic.list_all (params', prem), (rev vs, subst_bounds (vs, prem)))
      end) prems);

    val ind_vars =
      (Datatype_Prop.indexify_names (replicate (length atomTs) "pi") ~~
       map NominalAtoms.mk_permT atomTs) @ [("z", fsT)];
    val ind_Ts = rev (map snd ind_vars);

    val concl = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
      (map (fn (prem, (p, ts)) => HOLogic.mk_imp (prem,
        HOLogic.list_all (ind_vars, lift_pred p
          (map (fold_rev (NominalDatatype.mk_perm ind_Ts)
            (map Bound (length atomTs downto 1))) ts)))) concls));

    val concl' = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
      (map (fn (prem, (p, ts)) => HOLogic.mk_imp (prem,
        lift_pred' (Free (fs_ctxt_name, fsT)) p ts)) concls));

    val vc_compat = map (fn (params, bvars, prems, (p, ts)) =>
      map (fn q => Logic.list_all (params, incr_boundvars ~1 (Logic.list_implies
          (map_filter (fn prem =>
             if null (preds_of ps prem) then SOME prem
             else map_term (split_conj (K o I) names) prem prem) prems, q))))
        (mk_distinct bvars @
         maps (fn (t, T) => map (fn (u, U) => HOLogic.mk_Trueprop
           (NominalDatatype.fresh_const U T $ u $ t)) bvars)
             (ts ~~ binder_types (fastype_of p)))) prems;

    val perm_pi_simp = Global_Theory.get_thms thy "perm_pi_simp";
    val pt2_atoms = map (fn aT => Global_Theory.get_thm thy
      ("pt_" ^ Long_Name.base_name (fst (dest_Type aT)) ^ "2")) atomTs;
    val eqvt_ss = Simplifier.global_context thy HOL_basic_ss
      addsimps (eqvt_thms @ perm_pi_simp @ pt2_atoms)
      addsimprocs [mk_perm_bool_simproc [@{const_name Fun.id}],
        NominalPermeq.perm_simproc_app, NominalPermeq.perm_simproc_fun];
    val fresh_bij = Global_Theory.get_thms thy "fresh_bij";
    val perm_bij = Global_Theory.get_thms thy "perm_bij";
    val fs_atoms = map (fn aT => Global_Theory.get_thm thy
      ("fs_" ^ Long_Name.base_name (fst (dest_Type aT)) ^ "1")) atomTs;
    val exists_fresh' = Global_Theory.get_thms thy "exists_fresh'";
    val fresh_atm = Global_Theory.get_thms thy "fresh_atm";
    val swap_simps = Global_Theory.get_thms thy "swap_simps";
    val perm_fresh_fresh = Global_Theory.get_thms thy "perm_fresh_fresh";

    fun obtain_fresh_name ts T (freshs1, freshs2, ctxt) =
      let
        (** protect terms to avoid that fresh_prod interferes with  **)
        (** pairs used in introduction rules of inductive predicate **)
        fun protect t =
          let val T = fastype_of t in Const (@{const_name Fun.id}, T --> T) $ t end;
        val p = foldr1 HOLogic.mk_prod (map protect ts @ freshs1);
        val ex = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
            (HOLogic.exists_const T $ Abs ("x", T,
              NominalDatatype.fresh_const T (fastype_of p) $
                Bound 0 $ p)))
          (fn _ => EVERY
            [resolve_tac exists_fresh' 1,
             resolve_tac fs_atoms 1]);
        val (([(_, cx)], ths), ctxt') = Obtain.result
          (fn _ => EVERY
            [etac exE 1,
             full_simp_tac (HOL_ss addsimps (fresh_prod :: fresh_atm)) 1,
             full_simp_tac (HOL_basic_ss addsimps [@{thm id_apply}]) 1,
             REPEAT (etac conjE 1)])
          [ex] ctxt
      in (freshs1 @ [term_of cx], freshs2 @ ths, ctxt') end;

    fun mk_ind_proof ctxt' thss =
      Goal.prove ctxt' [] prems' concl' (fn {prems = ihyps, context = ctxt} =>
        let val th = Goal.prove ctxt [] [] concl (fn {context, ...} =>
          rtac raw_induct 1 THEN
          EVERY (maps (fn ((((_, bvars, oprems, _), vc_compat_ths), ihyp), (vs, ihypt)) =>
            [REPEAT (rtac allI 1), simp_tac eqvt_ss 1,
             SUBPROOF (fn {prems = gprems, params, concl, context = ctxt', ...} =>
               let
                 val (params', (pis, z)) =
                   chop (length params - length atomTs - 1) (map (term_of o #2) params) ||>
                   split_last;
                 val bvars' = map
                   (fn (Bound i, T) => (nth params' (length params' - i), T)
                     | (t, T) => (t, T)) bvars;
                 val pi_bvars = map (fn (t, _) =>
                   fold_rev (NominalDatatype.mk_perm []) pis t) bvars';
                 val (P, ts) = strip_comb (HOLogic.dest_Trueprop (term_of concl));
                 val (freshs1, freshs2, ctxt'') = fold
                   (obtain_fresh_name (ts @ pi_bvars))
                   (map snd bvars') ([], [], ctxt');
                 val freshs2' = NominalDatatype.mk_not_sym freshs2;
                 val pis' = map NominalDatatype.perm_of_pair (pi_bvars ~~ freshs1);
                 fun concat_perm pi1 pi2 =
                   let val T = fastype_of pi1
                   in if T = fastype_of pi2 then
                       Const (@{const_name List.append}, T --> T --> T) $ pi1 $ pi2
                     else pi2
                   end;
                 val pis'' = fold (concat_perm #> map) pis' pis;
                 val env = Pattern.first_order_match thy (ihypt, prop_of ihyp)
                   (Vartab.empty, Vartab.empty);
                 val ihyp' = Thm.instantiate ([], map (pairself (cterm_of thy))
                   (map (Envir.subst_term env) vs ~~
                    map (fold_rev (NominalDatatype.mk_perm [])
                      (rev pis' @ pis)) params' @ [z])) ihyp;
                 fun mk_pi th =
                   Simplifier.simplify (HOL_basic_ss addsimps [@{thm id_apply}]
                       addsimprocs [NominalDatatype.perm_simproc])
                     (Simplifier.simplify eqvt_ss
                       (fold_rev (mk_perm_bool o cterm_of thy)
                         (rev pis' @ pis) th));
                 val (gprems1, gprems2) = split_list
                   (map (fn (th, t) =>
                      if null (preds_of ps t) then (SOME th, mk_pi th)
                      else
                        (map_thm ctxt (split_conj (K o I) names)
                           (etac conjunct1 1) monos NONE th,
                         mk_pi (the (map_thm ctxt (inst_conj_all names ps (rev pis''))
                           (inst_conj_all_tac (length pis'')) monos (SOME t) th))))
                      (gprems ~~ oprems)) |>> map_filter I;
                 val vc_compat_ths' = map (fn th =>
                   let
                     val th' = first_order_mrs gprems1 th;
                     val (bop, lhs, rhs) = (case concl_of th' of
                         _ $ (fresh $ lhs $ rhs) =>
                           (fn t => fn u => fresh $ t $ u, lhs, rhs)
                       | _ $ (_ $ (_ $ lhs $ rhs)) =>
                           (curry (HOLogic.mk_not o HOLogic.mk_eq), lhs, rhs));
                     val th'' = Goal.prove ctxt'' [] [] (HOLogic.mk_Trueprop
                         (bop (fold_rev (NominalDatatype.mk_perm []) pis lhs)
                            (fold_rev (NominalDatatype.mk_perm []) pis rhs)))
                       (fn _ => simp_tac (HOL_basic_ss addsimps
                          (fresh_bij @ perm_bij)) 1 THEN rtac th' 1)
                   in Simplifier.simplify (eqvt_ss addsimps fresh_atm) th'' end)
                     vc_compat_ths;
                 val vc_compat_ths'' = NominalDatatype.mk_not_sym vc_compat_ths';
                 (** Since swap_simps simplifies (pi :: 'a prm) o (x :: 'b) to x **)
                 (** we have to pre-simplify the rewrite rules                   **)
                 val swap_simps_ss = HOL_ss addsimps swap_simps @
                    map (Simplifier.simplify (HOL_ss addsimps swap_simps))
                      (vc_compat_ths'' @ freshs2');
                 val th = Goal.prove ctxt'' [] []
                   (HOLogic.mk_Trueprop (list_comb (P $ hd ts,
                     map (fold (NominalDatatype.mk_perm []) pis') (tl ts))))
                   (fn _ => EVERY ([simp_tac eqvt_ss 1, rtac ihyp' 1,
                     REPEAT_DETERM_N (nprems_of ihyp - length gprems)
                       (simp_tac swap_simps_ss 1),
                     REPEAT_DETERM_N (length gprems)
                       (simp_tac (HOL_basic_ss
                          addsimps [inductive_forall_def']
                          addsimprocs [NominalDatatype.perm_simproc]) 1 THEN
                        resolve_tac gprems2 1)]));
                 val final = Goal.prove ctxt'' [] [] (term_of concl)
                   (fn _ => cut_facts_tac [th] 1 THEN full_simp_tac (HOL_ss
                     addsimps vc_compat_ths'' @ freshs2' @
                       perm_fresh_fresh @ fresh_atm) 1);
                 val final' = Proof_Context.export ctxt'' ctxt' [final];
               in resolve_tac final' 1 end) context 1])
                 (prems ~~ thss ~~ ihyps ~~ prems'')))
        in
          cut_facts_tac [th] 1 THEN REPEAT (etac conjE 1) THEN
          REPEAT (REPEAT (resolve_tac [conjI, impI] 1) THEN
            etac impE 1 THEN atac 1 THEN REPEAT (etac @{thm allE_Nil} 1) THEN
            asm_full_simp_tac (simpset_of ctxt) 1)
        end) |> singleton (Proof_Context.export ctxt' ctxt);

    (** strong case analysis rule **)

    val cases_prems = map (fn ((name, avoids), rule) =>
      let
        val ([rule'], ctxt') = Variable.import_terms false [prop_of rule] ctxt;
        val prem :: prems = Logic.strip_imp_prems rule';
        val concl = Logic.strip_imp_concl rule'
      in
        (prem,
         List.drop (snd (strip_comb (HOLogic.dest_Trueprop prem)), length ind_params),
         concl,
         fold_map (fn (prem, (_, avoid)) => fn ctxt =>
           let
             val prems = Logic.strip_assums_hyp prem;
             val params = Logic.strip_params prem;
             val bnds = fold (add_binders thy 0) prems [] @ mk_avoids params avoid;
             fun mk_subst (p as (s, T)) (i, j, ctxt, ps, qs, is, ts) =
               if member (op = o apsnd fst) bnds (Bound i) then
                 let
                   val ([s'], ctxt') = Variable.variant_fixes [s] ctxt;
                   val t = Free (s', T)
                 in (i + 1, j, ctxt', ps, (t, T) :: qs, i :: is, t :: ts) end
               else (i + 1, j + 1, ctxt, p :: ps, qs, is, Bound j :: ts);
             val (_, _, ctxt', ps, qs, is, ts) = fold_rev mk_subst params
               (0, 0, ctxt, [], [], [], [])
           in
             ((ps, qs, is, map (curry subst_bounds (rev ts)) prems), ctxt')
           end) (prems ~~ avoids) ctxt')
      end)
        (Inductive.partition_rules' raw_induct (intrs ~~ avoids') ~~
         elims);

    val cases_prems' =
      map (fn (prem, args, concl, (prems, _)) =>
        let
          fun mk_prem (ps, [], _, prems) =
                Logic.list_all (ps, Logic.list_implies (prems, concl))
            | mk_prem (ps, qs, _, prems) =
                Logic.list_all (ps, Logic.mk_implies
                  (Logic.list_implies
                    (mk_distinct qs @
                     maps (fn (t, T) => map (fn u => HOLogic.mk_Trueprop
                      (NominalDatatype.fresh_const T (fastype_of u) $ t $ u))
                        args) qs,
                     HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                       (map HOLogic.dest_Trueprop prems))),
                   concl))
          in map mk_prem prems end) cases_prems;

    val cases_eqvt_ss = Simplifier.global_context thy HOL_ss
      addsimps eqvt_thms @ swap_simps @ perm_pi_simp
      addsimprocs [NominalPermeq.perm_simproc_app,
        NominalPermeq.perm_simproc_fun];

    val simp_fresh_atm = map
      (Simplifier.simplify (HOL_basic_ss addsimps fresh_atm));

    fun mk_cases_proof ((((name, thss), elim), (prem, args, concl, (prems, ctxt'))),
        prems') =
      (name, Goal.prove ctxt' [] (prem :: prems') concl
        (fn {prems = hyp :: hyps, context = ctxt1} =>
        EVERY (rtac (hyp RS elim) 1 ::
          map (fn (((_, vc_compat_ths), case_hyp), (_, qs, is, _)) =>
            SUBPROOF (fn {prems = case_hyps, params, context = ctxt2, concl, ...} =>
              if null qs then
                rtac (first_order_mrs case_hyps case_hyp) 1
              else
                let
                  val params' = map (term_of o #2 o nth (rev params)) is;
                  val tab = params' ~~ map fst qs;
                  val (hyps1, hyps2) = chop (length args) case_hyps;
                  (* turns a = t and [x1 # t, ..., xn # t] *)
                  (* into [x1 # a, ..., xn # a]            *)
                  fun inst_fresh th' ths =
                    let val (ths1, ths2) = chop (length qs) ths
                    in
                      (map (fn th =>
                         let
                           val (cf, ct) =
                             Thm.dest_comb (Thm.dest_arg (cprop_of th));
                           val arg_cong' = Drule.instantiate'
                             [SOME (ctyp_of_term ct)]
                             [NONE, SOME ct, SOME cf] (arg_cong RS iffD2);
                           val inst = Thm.first_order_match (ct,
                             Thm.dest_arg (Thm.dest_arg (cprop_of th')))
                         in [th', th] MRS Thm.instantiate inst arg_cong'
                         end) ths1,
                       ths2)
                    end;
                  val (vc_compat_ths1, vc_compat_ths2) =
                    chop (length vc_compat_ths - length args * length qs)
                      (map (first_order_mrs hyps2) vc_compat_ths);
                  val vc_compat_ths' =
                    NominalDatatype.mk_not_sym vc_compat_ths1 @
                    flat (fst (fold_map inst_fresh hyps1 vc_compat_ths2));
                  val (freshs1, freshs2, ctxt3) = fold
                    (obtain_fresh_name (args @ map fst qs @ params'))
                    (map snd qs) ([], [], ctxt2);
                  val freshs2' = NominalDatatype.mk_not_sym freshs2;
                  val pis = map (NominalDatatype.perm_of_pair)
                    ((freshs1 ~~ map fst qs) @ (params' ~~ freshs1));
                  val mk_pis = fold_rev mk_perm_bool (map (cterm_of thy) pis);
                  val obj = cterm_of thy (foldr1 HOLogic.mk_conj (map (map_aterms
                     (fn x as Free _ =>
                           if member (op =) args x then x
                           else (case AList.lookup op = tab x of
                             SOME y => y
                           | NONE => fold_rev (NominalDatatype.mk_perm []) pis x)
                       | x => x) o HOLogic.dest_Trueprop o prop_of) case_hyps));
                  val inst = Thm.first_order_match (Thm.dest_arg
                    (Drule.strip_imp_concl (hd (cprems_of case_hyp))), obj);
                  val th = Goal.prove ctxt3 [] [] (term_of concl)
                    (fn {context = ctxt4, ...} =>
                       rtac (Thm.instantiate inst case_hyp) 1 THEN
                       SUBPROOF (fn {prems = fresh_hyps, ...} =>
                         let
                           val fresh_hyps' = NominalDatatype.mk_not_sym fresh_hyps;
                           val case_ss = cases_eqvt_ss addsimps freshs2' @
                             simp_fresh_atm (vc_compat_ths' @ fresh_hyps');
                           val fresh_fresh_ss = case_ss addsimps perm_fresh_fresh;
                           val hyps1' = map
                             (mk_pis #> Simplifier.simplify fresh_fresh_ss) hyps1;
                           val hyps2' = map
                             (mk_pis #> Simplifier.simplify case_ss) hyps2;
                           val case_hyps' = hyps1' @ hyps2'
                         in
                           simp_tac case_ss 1 THEN
                           REPEAT_DETERM (TRY (rtac conjI 1) THEN
                             resolve_tac case_hyps' 1)
                         end) ctxt4 1)
                  val final = Proof_Context.export ctxt3 ctxt2 [th]
                in resolve_tac final 1 end) ctxt1 1)
                  (thss ~~ hyps ~~ prems))) |>
                  singleton (Proof_Context.export ctxt' ctxt))

  in
    ctxt'' |>
    Proof.theorem NONE (fn thss => fn ctxt =>
      let
        val rec_name = space_implode "_" (map Long_Name.base_name names);
        val rec_qualified = Binding.qualify false rec_name;
        val ind_case_names = Rule_Cases.case_names induct_cases;
        val induct_cases' = Inductive.partition_rules' raw_induct
          (intrs ~~ induct_cases); 
        val thss' = map (map atomize_intr) thss;
        val thsss = Inductive.partition_rules' raw_induct (intrs ~~ thss');
        val strong_raw_induct =
          mk_ind_proof ctxt thss' |> Inductive.rulify;
        val strong_cases = map (mk_cases_proof ##> Inductive.rulify)
          (thsss ~~ elims ~~ cases_prems ~~ cases_prems');
        val strong_induct =
          if length names > 1 then
            (strong_raw_induct, [ind_case_names, Rule_Cases.consumes 0])
          else (strong_raw_induct RSN (2, rev_mp),
            [ind_case_names, Rule_Cases.consumes 1]);
        val ((_, [strong_induct']), ctxt') = ctxt |> Local_Theory.note
          ((rec_qualified (Binding.name "strong_induct"),
            map (Attrib.internal o K) (#2 strong_induct)), [#1 strong_induct]);
        val strong_inducts =
          Project_Rule.projects ctxt (1 upto length names) strong_induct';
      in
        ctxt' |>
        Local_Theory.note
          ((rec_qualified (Binding.name "strong_inducts"),
            [Attrib.internal (K ind_case_names),
             Attrib.internal (K (Rule_Cases.consumes 1))]),
           strong_inducts) |> snd |>
        Local_Theory.notes (map (fn ((name, elim), (_, cases)) =>
            ((Binding.qualified_name (Long_Name.qualify (Long_Name.base_name name) "strong_cases"),
              [Attrib.internal (K (Rule_Cases.case_names (map snd cases))),
               Attrib.internal (K (Rule_Cases.consumes 1))]), [([elim], [])]))
          (strong_cases ~~ induct_cases')) |> snd
      end)
      (map (map (rulify_term thy #> rpair [])) vc_compat)
  end;

fun prove_eqvt s xatoms ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ({names, ...}, {raw_induct, intrs, elims, ...}) =
      Inductive.the_inductive ctxt (Sign.intern_const thy s);
    val raw_induct = atomize_induct ctxt raw_induct;
    val elims = map (atomize_induct ctxt) elims;
    val intrs = map atomize_intr intrs;
    val monos = Inductive.get_monos ctxt;
    val intrs' = Inductive.unpartition_rules intrs
      (map (fn (((s, ths), (_, k)), th) =>
           (s, ths ~~ Inductive.infer_intro_vars th k ths))
         (Inductive.partition_rules raw_induct intrs ~~
          Inductive.arities_of raw_induct ~~ elims));
    val k = length (Inductive.params_of raw_induct);
    val atoms' = NominalAtoms.atoms_of thy;
    val atoms =
      if null xatoms then atoms' else
      let val atoms = map (Sign.intern_type thy) xatoms
      in
        (case duplicates op = atoms of
             [] => ()
           | xs => error ("Duplicate atoms: " ^ commas xs);
         case subtract (op =) atoms' atoms of
             [] => ()
           | xs => error ("No such atoms: " ^ commas xs);
         atoms)
      end;
    val perm_pi_simp = Global_Theory.get_thms thy "perm_pi_simp";
    val eqvt_ss = Simplifier.global_context thy HOL_basic_ss addsimps
      (NominalThmDecls.get_eqvt_thms ctxt @ perm_pi_simp) addsimprocs
      [mk_perm_bool_simproc names,
       NominalPermeq.perm_simproc_app, NominalPermeq.perm_simproc_fun];
    val (([t], [pi]), ctxt') = ctxt |>
      Variable.import_terms false [concl_of raw_induct] ||>>
      Variable.variant_fixes ["pi"];
    val ps = map (fst o HOLogic.dest_imp)
      (HOLogic.dest_conj (HOLogic.dest_Trueprop t));
    fun eqvt_tac ctxt'' pi (intr, vs) st =
      let
        fun eqvt_err s =
          let val ([t], ctxt''') = Variable.import_terms true [prop_of intr] ctxt
          in error ("Could not prove equivariance for introduction rule\n" ^
            Syntax.string_of_term ctxt''' t ^ "\n" ^ s)
          end;
        val res = SUBPROOF (fn {prems, params, ...} =>
          let
            val prems' = map (fn th => the_default th (map_thm ctxt'
              (split_conj (K I) names) (etac conjunct2 1) monos NONE th)) prems;
            val prems'' = map (fn th => Simplifier.simplify eqvt_ss
              (mk_perm_bool (cterm_of thy pi) th)) prems';
            val intr' = Drule.cterm_instantiate (map (cterm_of thy) vs ~~
               map (cterm_of thy o NominalDatatype.mk_perm [] pi o term_of o #2) params)
               intr
          in (rtac intr' THEN_ALL_NEW (TRY o resolve_tac prems'')) 1
          end) ctxt' 1 st
      in
        case (Seq.pull res handle THM (s, _, _) => eqvt_err s) of
          NONE => eqvt_err ("Rule does not match goal\n" ^
            Syntax.string_of_term ctxt'' (hd (prems_of st)))
        | SOME (th, _) => Seq.single th
      end;
    val thss = map (fn atom =>
      let val pi' = Free (pi, NominalAtoms.mk_permT (Type (atom, [])))
      in map (fn th => zero_var_indexes (th RS mp))
        (Datatype_Aux.split_conj_thm (Goal.prove ctxt' [] []
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map (fn p =>
            let
              val (h, ts) = strip_comb p;
              val (ts1, ts2) = chop k ts
            in
              HOLogic.mk_imp (p, list_comb (h, ts1 @
                map (NominalDatatype.mk_perm [] pi') ts2))
            end) ps)))
          (fn {context, ...} => EVERY (rtac raw_induct 1 :: map (fn intr_vs =>
              full_simp_tac eqvt_ss 1 THEN
              eqvt_tac context pi' intr_vs) intrs')) |>
          singleton (Proof_Context.export ctxt' ctxt)))
      end) atoms
  in
    ctxt |>
    Local_Theory.notes (map (fn (name, ths) =>
        ((Binding.qualified_name (Long_Name.qualify (Long_Name.base_name name) "eqvt"),
          [Attrib.internal (K NominalThmDecls.eqvt_add)]), [(ths, [])]))
      (names ~~ transp thss)) |> snd
  end;


(* outer syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof "nominal_inductive"
    "prove equivariance and strong induction theorem for inductive predicate involving nominal datatypes"
    Keyword.thy_goal
    (Parse.xname -- Scan.optional (Parse.$$$ "avoids" |-- Parse.and_list1 (Parse.name --
      (Parse.$$$ ":" |-- Scan.repeat1 Parse.name))) [] >> (fn (name, avoids) =>
        prove_strong_ind name avoids));

val _ =
  Outer_Syntax.local_theory "equivariance"
    "prove equivariance for inductive predicate involving nominal datatypes" Keyword.thy_decl
    (Parse.xname -- Scan.optional (Parse.$$$ "[" |-- Parse.list1 Parse.name --| Parse.$$$ "]") [] >>
      (fn (name, atoms) => prove_eqvt name atoms));

end
