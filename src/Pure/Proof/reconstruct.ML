(*  Title:      Pure/Proof/reconstruct.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Reconstruction of partial proof terms.
*)

signature RECONSTRUCT =
sig
  val quiet_mode : bool ref
  val reconstruct_proof : Sign.sg -> term -> Proofterm.proof -> Proofterm.proof
  val prop_of : Proofterm.proof -> term
  val expand_proof : Sign.sg -> string list -> Proofterm.proof -> Proofterm.proof
end;

structure Reconstruct : RECONSTRUCT =
struct

open Proofterm;

val quiet_mode = ref true;
fun message s = if !quiet_mode then () else writeln s;

fun vars_of t = rev (foldl_aterms
  (fn (vs, v as Var _) => v ins vs | (vs, _) => vs) ([], t));

fun forall_intr (t, prop) =
  let val (a, T) = (case t of Var ((a, _), T) => (a, T) | Free p => p)
  in all T $ Abs (a, T, abstract_over (t, prop)) end;

fun forall_intr_vfs prop = foldr forall_intr
  (vars_of prop @ sort (make_ord atless) (term_frees prop), prop);

fun forall_intr_prf (t, prf) =
  let val (a, T) = (case t of Var ((a, _), T) => (a, T) | Free p => p)
  in Abst (a, Some T, prf_abstract_over t prf) end;

fun forall_intr_vfs_prf prop prf = foldr forall_intr_prf
  (vars_of prop @ sort (make_ord atless) (term_frees prop), prf);

fun merge_envs (Envir.Envir {asol=asol1, iTs=iTs1, maxidx=maxidx1})
  (Envir.Envir {asol=asol2, iTs=iTs2, maxidx=maxidx2}) =
    Envir.Envir {asol=Vartab.merge (op aconv) (asol1, asol2),
                 iTs=Vartab.merge (op =) (iTs1, iTs2),
                 maxidx=Int.max (maxidx1, maxidx2)};

fun strip_abs (_::Ts) (Abs (_, _, t)) = strip_abs Ts t
  | strip_abs _ t = t;


(********************************************************************************
  generate constraints for proof term
*********************************************************************************)

fun mk_var env Ts T = 
  let val (env', v) = Envir.genvar "a" (env, rev Ts ---> T)
  in (env', list_comb (v, map Bound (length Ts - 1 downto 0))) end;

fun mk_tvar (Envir.Envir {iTs, asol, maxidx}, s) =
  (Envir.Envir {iTs = iTs, asol = asol, maxidx = maxidx+1},
   TVar (("'t", maxidx+1), s));

fun mk_abs Ts t = foldl (fn (u, T) => Abs ("", T, u)) (t, Ts);

fun make_Tconstraints_cprf maxidx cprf =
  let
    fun mk_Tcnstrts maxidx Ts (Abst (s, Some T, cprf)) =
          let val (cs, cprf', maxidx') = mk_Tcnstrts maxidx (T::Ts) cprf;
          in (cs, Abst (s, Some T, cprf'), maxidx') end
      | mk_Tcnstrts maxidx Ts (Abst (s, None, cprf)) =
          let
            val T' = TVar (("'t", maxidx+1), ["logic"]);
            val (cs, cprf', maxidx') = mk_Tcnstrts (maxidx+1) (T'::Ts) cprf;
          in (cs, Abst (s, Some T', cprf'), maxidx') end
      | mk_Tcnstrts maxidx Ts (AbsP (s, Some t, cprf)) =
          let val (cs, cprf', maxidx') = mk_Tcnstrts maxidx Ts cprf;
          in ((mk_abs Ts t, rev Ts ---> propT)::cs, AbsP (s, Some t, cprf'), maxidx') end
      | mk_Tcnstrts maxidx Ts (AbsP (s, None, cprf)) =
          let val (cs, cprf', maxidx') = mk_Tcnstrts maxidx Ts cprf;
          in (cs, AbsP (s, None, cprf'), maxidx') end
      | mk_Tcnstrts maxidx Ts (cprf1 %% cprf2) =
          let
            val (cs, cprf1', maxidx') = mk_Tcnstrts maxidx Ts cprf1;
            val (cs', cprf2', maxidx'') = mk_Tcnstrts maxidx' Ts cprf2;
          in (cs' @ cs, cprf1' %% cprf2', maxidx'') end
      | mk_Tcnstrts maxidx Ts (cprf % Some t) =
          let val (cs, cprf', maxidx') = mk_Tcnstrts maxidx Ts cprf;
          in ((mk_abs Ts t, rev Ts ---> TypeInfer.logicT)::cs,
            cprf' % Some t, maxidx')
          end
      | mk_Tcnstrts maxidx Ts (cprf % None) =
          let val (cs, cprf', maxidx') = mk_Tcnstrts maxidx Ts cprf;
          in (cs, cprf % None, maxidx') end
      | mk_Tcnstrts maxidx _ cprf = ([], cprf, maxidx);
  in mk_Tcnstrts maxidx [] cprf end;

fun unifyT sg env T U =
  let
    val Envir.Envir {asol, iTs, maxidx} = env;
    val (iTs', maxidx') = Type.unify (Sign.tsig_of sg) (iTs, maxidx) (T, U)
  in Envir.Envir {asol=asol, iTs=iTs', maxidx=maxidx'} end
  handle Type.TUNIFY => error ("Non-unifiable types:\n" ^
    Sign.string_of_typ sg T ^ "\n\n" ^ Sign.string_of_typ sg U);

fun decompose sg env Ts t u = case (Envir.head_norm env t, Envir.head_norm env u) of
    (Const ("all", _) $ t, Const ("all", _) $ u) => decompose sg env Ts t u
  | (Const ("==>", _) $ t1 $ t2, Const ("==>", _) $ u1 $ u2) =>
      let val (env', cs) = decompose sg env Ts t1 u1
      in apsnd (curry op @ cs) (decompose sg env' Ts t2 u2) end
  | (Abs (_, T, t), Abs (_, U, u)) =>
      decompose sg (unifyT sg env T U) (T::Ts) t u
  | (t, u) => (env, [(mk_abs Ts t, mk_abs Ts u)]);

fun cantunify sg t u = error ("Non-unifiable terms:\n" ^
  Sign.string_of_term sg t ^ "\n\n" ^ Sign.string_of_term sg u);

fun make_constraints_cprf sg env ts cprf =
  let
    fun add_cnstrt Ts prop prf cs env ts (t, u) =
      let
        val t' = mk_abs Ts t;
        val u' = mk_abs Ts u
      in
        (prop, prf, cs, Pattern.unify (sg, env, [(t', u')]), ts)
        handle Pattern.Pattern =>
            let val (env', cs') = decompose sg env [] t' u'
            in (prop, prf, cs @ cs', env', ts) end
        | Pattern.Unif =>
            cantunify sg (Envir.norm_term env t') (Envir.norm_term env u')
      end;

    fun mk_cnstrts_atom env ts prop opTs prf =
          let
            val tvars = term_tvars prop;
            val (env', Ts) = if_none (apsome (pair env) opTs)
              (foldl_map (mk_tvar o apsnd snd) (env, tvars));
            val prop' = subst_TVars (map fst tvars ~~ Ts) (forall_intr_vfs prop)
              handle LIST _ => error ("Wrong number of type arguments for " ^
                quote (fst (get_name_tags [] prop prf)))
          in (prop', change_type (Some Ts) prf, [], env', ts) end;

    fun mk_cnstrts env _ Hs ts (PBound i) = (nth_elem (i, Hs), PBound i, [], env, ts)
      | mk_cnstrts env Ts Hs ts (Abst (s, Some T, cprf)) =
          let val (t, prf, cnstrts, env', ts') =
              mk_cnstrts env (T::Ts) (map (incr_boundvars 1) Hs) ts cprf;
          in (Const ("all", (T --> propT) --> propT) $ Abs (s, T, t), Abst (s, Some T, prf),
            cnstrts, env', ts')
          end
      | mk_cnstrts env Ts Hs (t::ts) (AbsP (s, Some _, cprf)) =
          let
            val (u, prf, cnstrts, env', ts') = mk_cnstrts env Ts (t::Hs) ts cprf;
            val t' = strip_abs Ts t;
          in (Logic.mk_implies (t', u), AbsP (s, Some t', prf), cnstrts, env', ts')
          end
      | mk_cnstrts env Ts Hs ts (AbsP (s, None, cprf)) =
          let
            val (env', t) = mk_var env Ts propT;
            val (u, prf, cnstrts, env'', ts') = mk_cnstrts env' Ts (t::Hs) ts cprf;
          in (Logic.mk_implies (t, u), AbsP (s, Some t, prf), cnstrts, env'', ts')
          end
      | mk_cnstrts env Ts Hs ts (cprf1 %% cprf2) =
          let val (u, prf2, cnstrts, env', ts') = mk_cnstrts env Ts Hs ts cprf2
          in (case mk_cnstrts env' Ts Hs ts' cprf1 of
              (Const ("==>", _) $ u' $ t', prf1, cnstrts', env'', ts'') =>
                add_cnstrt Ts t' (prf1 %% prf2) (cnstrts' @ cnstrts)
                  env'' ts'' (u, u')
            | (t, prf1, cnstrts', env'', ts'') =>
                let val (env''', v) = mk_var env'' Ts propT
                in add_cnstrt Ts v (prf1 %% prf2) (cnstrts' @ cnstrts)
                  env''' ts'' (t, Logic.mk_implies (u, v))
                end)
          end
      | mk_cnstrts env Ts Hs (t::ts) (cprf % Some _) =
          let val t' = strip_abs Ts t
          in (case mk_cnstrts env Ts Hs ts cprf of
             (Const ("all", Type ("fun", [Type ("fun", [T, _]), _])) $ f,
                 prf, cnstrts, env', ts') =>
               let val env'' = unifyT sg env' T (Envir.fastype env' Ts t')
               in (betapply (f, t'), prf % Some t', cnstrts, env'', ts')
               end
           | (u, prf, cnstrts, env', ts') =>
               let
                 val T = Envir.fastype env' Ts t';
                 val (env'', v) = mk_var env' Ts (T --> propT);
               in
                 add_cnstrt Ts (v $ t') (prf % Some t') cnstrts env'' ts'
                   (u, Const ("all", (T --> propT) --> propT) $ v)
               end)
          end
      | mk_cnstrts env Ts Hs ts (cprf % None) =
          (case mk_cnstrts env Ts Hs ts cprf of
             (Const ("all", Type ("fun", [Type ("fun", [T, _]), _])) $ f,
                 prf, cnstrts, env', ts') =>
               let val (env'', t) = mk_var env' Ts T
               in (betapply (f, t), prf % Some t, cnstrts, env'', ts')
               end
           | (u, prf, cnstrts, env', ts') =>
               let
                 val (env1, T) = mk_tvar (env', ["logic"]);
                 val (env2, v) = mk_var env1 Ts (T --> propT);
                 val (env3, t) = mk_var env2 Ts T
               in
                 add_cnstrt Ts (v $ t) (prf % Some t) cnstrts env3 ts'
                   (u, Const ("all", (T --> propT) --> propT) $ v)
               end)
      | mk_cnstrts env _ _ ts (prf as PThm (_, _, prop, opTs)) =
          mk_cnstrts_atom env ts prop opTs prf
      | mk_cnstrts env _ _ ts (prf as PAxm (_, prop, opTs)) =
          mk_cnstrts_atom env ts prop opTs prf
      | mk_cnstrts env _ _ ts (prf as Oracle (_, prop, opTs)) =
          mk_cnstrts_atom env ts prop opTs prf
      | mk_cnstrts env _ _ ts (Hyp t) = (t, Hyp t, [], env, ts)
      | mk_cnstrts _ _ _ _ _ = error "reconstruct_proof: minimal proof object"
  in mk_cnstrts env [] [] ts cprf end;

fun add_term_ixns (is, Var (i, T)) = add_typ_ixns (i ins is, T)
  | add_term_ixns (is, Free (_, T)) = add_typ_ixns (is, T)
  | add_term_ixns (is, Const (_, T)) = add_typ_ixns (is, T)
  | add_term_ixns (is, t1 $ t2) = add_term_ixns (add_term_ixns (is, t1), t2)
  | add_term_ixns (is, Abs (_, T, t)) = add_term_ixns (add_typ_ixns (is, T), t)
  | add_term_ixns (is, _) = is;


(********************************************************************************
  update list of free variables of constraints
*********************************************************************************)

fun upd_constrs env cs =
  let
    val Envir.Envir {asol, iTs, ...} = env;
    val dom = Vartab.foldl (uncurry (cons o fst) o Library.swap)
      (Vartab.foldl (uncurry (cons o fst) o Library.swap) ([], asol), iTs); 
    val vran = Vartab.foldl (add_typ_ixns o apsnd snd)
      (Vartab.foldl (add_term_ixns o apsnd snd) ([], asol), iTs);
    fun check_cs [] = []
      | check_cs ((u, p, vs)::ps) =
          let val vs' = vs \\ dom;
          in if vs = vs' then (u, p, vs)::check_cs ps
             else (true, p, vs' union vran)::check_cs ps
          end
  in check_cs cs end;

(********************************************************************************
  solution of constraints
*********************************************************************************)

fun solve _ [] bigenv = bigenv
  | solve sg cs bigenv =
      let
        fun search env [] = error ("Unsolvable constraints:\n" ^
              Pretty.string_of (Pretty.chunks (map (fn (_, p, _) =>
                Sign.pretty_term sg (Logic.mk_flexpair (pairself
                  (Envir.norm_term bigenv) p))) cs)))
          | search env ((u, p as (t1, t2), vs)::ps) =
              if u then
                let
                  val tn1 = Envir.norm_term bigenv t1;
                  val tn2 = Envir.norm_term bigenv t2
                in
                  if Pattern.pattern tn1 andalso Pattern.pattern tn2 then
                    ((Pattern.unify (sg, env, [(tn1, tn2)]), ps) handle Pattern.Unif =>
                       cantunify sg tn1 tn2)
                  else
                    let val (env', cs') = decompose sg env [] tn1 tn2
                    in if cs' = [(tn1, tn2)] then
                         apsnd (cons (false, (tn1, tn2), vs)) (search env ps)
                       else search env' (map (fn q => (true, q, vs)) cs' @ ps)
                    end
                end
              else apsnd (cons (false, p, vs)) (search env ps);
        val Envir.Envir {maxidx, ...} = bigenv;
        val (env, cs') = search (Envir.empty maxidx) cs;
      in
        solve sg (upd_constrs env cs') (merge_envs bigenv env)
      end;


(********************************************************************************
  reconstruction of proofs
*********************************************************************************)

fun reconstruct_proof sg prop cprf =
  let
    val (cprf' % Some prop', thawf) = freeze_thaw_prf (cprf % Some prop);
    val _ = message "Collecting type constraints...";
    val (Tcs, cprf'', maxidx) = make_Tconstraints_cprf 0 cprf';
    val (ts, Ts) = ListPair.unzip Tcs;
    val tsig = Sign.tsig_of sg;
    val {classrel, arities, ...} = Type.rep_tsig tsig;
    val _ = message "Solving type constraints...";
    val (ts', _, unifier) = TypeInfer.infer_types (Sign.pretty_term sg) (Sign.pretty_typ sg)
      (Sign.const_type sg) classrel arities [] false (K true) ts Ts;
    val env = Envir.Envir {asol = Vartab.empty, iTs = Vartab.make unifier, maxidx = maxidx};
    val _ = message "Collecting term constraints...";
    val (t, prf, cs, env, _) = make_constraints_cprf sg env ts' cprf'';
    val cs' = map (fn p => (true, p, op union
      (pairself (map (fst o dest_Var) o term_vars) p))) (map (pairself (Envir.norm_term env)) ((t, prop')::cs));
    val _ = message ("Solving remaining constraints (" ^ string_of_int (length cs') ^ ") ...");
    val env' = solve sg cs' env
  in
    thawf (norm_proof env' prf)
  end;

fun prop_of prf =
  let
    fun prop_of_atom prop Ts =
      subst_TVars (map fst (term_tvars prop) ~~ Ts) (forall_intr_vfs prop);

    fun prop_of' Hs (PBound i) = nth_elem (i, Hs)
      | prop_of' Hs (Abst (s, Some T, prf)) =
          all T $ (Abs (s, T, prop_of' Hs prf))
      | prop_of' Hs (AbsP (s, Some t, prf)) =
          Logic.mk_implies (t, prop_of' (t :: Hs) prf)
      | prop_of' Hs (prf % Some t) = (case prop_of' Hs prf of
          Const ("all", _) $ f => betapply (f, t)
        | _ => error "prop_of: all expected")
      | prop_of' Hs (prf1 %% prf2) = (case prop_of' Hs prf1 of
          Const ("==>", _) $ P $ Q => Q
        | _ => error "prop_of: ==> expected")
      | prop_of' Hs (Hyp t) = t
      | prop_of' Hs (PThm (_, _, prop, Some Ts)) = prop_of_atom prop Ts
      | prop_of' Hs (PAxm (_, prop, Some Ts)) = prop_of_atom prop Ts
      | prop_of' Hs (Oracle (_, prop, Some Ts)) = prop_of_atom prop Ts
      | prop_of' _ _ = error "prop_of: partial proof object";

  in prop_of' [] prf end;


(********************************************************************************
  expand and reconstruct subproofs
*********************************************************************************)

fun expand_proof sg names prf =
  let
    fun expand maxidx prfs (AbsP (s, t, prf)) = 
          let val (maxidx', prfs', prf') = expand maxidx prfs prf
          in (maxidx', prfs', AbsP (s, t, prf')) end
      | expand maxidx prfs (Abst (s, T, prf)) = 
          let val (maxidx', prfs', prf') = expand maxidx prfs prf
          in (maxidx', prfs', Abst (s, T, prf')) end
      | expand maxidx prfs (prf1 %% prf2) =
          let
            val (maxidx', prfs', prf1') = expand maxidx prfs prf1;
            val (maxidx'', prfs'', prf2') = expand maxidx' prfs' prf2;
          in (maxidx'', prfs'', prf1' %% prf2') end
      | expand maxidx prfs (prf % t) =
          let val (maxidx', prfs', prf') = expand maxidx prfs prf
          in (maxidx', prfs', prf' % t) end
      | expand maxidx prfs (prf as PThm ((a, _), cprf, prop, Some Ts)) =
          if not (a mem names) then (maxidx, prfs, prf) else
          let
            val (maxidx', (i, prf), prfs') = (case assoc (prfs, (a, prop)) of
                None =>
                  let
                    val _ = message ("Reconstructing proof of " ^ a);
                    val _ = message (Sign.string_of_term sg prop);
                    val i = maxidx + 1;
                    val prf' = map_proof_terms (Logic.incr_indexes ([], i))
                      (incr_tvar i) (forall_intr_vfs_prf prop
                        (reconstruct_proof sg prop cprf));
                    val (maxidx', prfs', prf) = expand
                      (maxidx_of_proof prf') prfs prf'
                  in (maxidx', (i, prf), ((a, prop), (i, prf)) :: prfs') end
              | Some p => (maxidx, p, prfs));
            val tye = map (fn ((s, j), _) => (s, i + j)) (term_tvars prop) ~~ Ts
          in
            (maxidx', prfs',
             map_proof_terms (subst_TVars tye) (typ_subst_TVars tye) prf)
          end
      | expand maxidx prfs prf = (maxidx, prfs, prf);

  in #3 (expand (maxidx_of_proof prf) [] prf) end;

end;
