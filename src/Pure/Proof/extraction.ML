(*  Title:      Pure/Proof/extraction.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Extraction of programs from proofs.
*)

signature EXTRACTION =
sig
  val set_preprocessor : (Sign.sg -> Proofterm.proof -> Proofterm.proof) -> theory -> theory
  val add_realizes_eqns_i : ((term * term) list * (term * term)) list -> theory -> theory
  val add_realizes_eqns : string list -> theory -> theory
  val add_typeof_eqns_i : ((term * term) list * (term * term)) list -> theory -> theory
  val add_typeof_eqns : string list -> theory -> theory
  val add_realizers_i : (string * (string list * term * Proofterm.proof)) list
    -> theory -> theory
  val add_realizers : (thm * (string list * string * string)) list
    -> theory -> theory
  val add_expand_thms : thm list -> theory -> theory
  val extract : thm list -> theory -> theory
  val nullT : typ
  val nullt : term
  val parsers: OuterSyntax.parser list
  val setup: (theory -> theory) list
end;

structure Extraction : EXTRACTION =
struct

open Proofterm;

(**** tools ****)

fun add_syntax thy =
  thy
  |> Theory.copy
  |> Theory.root_path
  |> Theory.add_types [("Type", 0, NoSyn), ("Null", 0, NoSyn)]
  |> Theory.add_arities [("Type", [], "logic"), ("Null", [], "logic")]
  |> Theory.add_consts
      [("typeof", "'b::logic => Type", NoSyn),
       ("Type", "'a::logic itself => Type", NoSyn),
       ("Null", "Null", NoSyn),
       ("realizes", "'a::logic => 'b::logic => 'b", NoSyn)];

val nullT = Type ("Null", []);
val nullt = Const ("Null", nullT);

fun mk_typ T =
  Const ("Type", itselfT T --> Type ("Type", [])) $ Logic.mk_type T;

fun typeof_proc defaultS vs (Const ("typeof", _) $ u) =
      Some (mk_typ (case strip_comb u of
          (Var ((a, i), _), _) =>
            if a mem vs then TFree ("'" ^ a ^ ":" ^ string_of_int i, defaultS)
            else nullT
        | (Free (a, _), _) =>
            if a mem vs then TFree ("'" ^ a, defaultS) else nullT
        | _ => nullT))
  | typeof_proc _ _ _ = None;

fun rlz_proc (Const ("realizes", Type (_, [Type ("Null", []), _])) $ _ $ t) =
  (case strip_comb t of (Const _, _) => Some t | _ => None)
  | rlz_proc _ = None;

fun rlz_proc' (Const ("realizes", _) $ _ $ t) = Some t
  | rlz_proc' _ = None;

val unpack_ixn = apfst implode o apsnd (fst o read_int o tl) o
  take_prefix (not o equal ":") o explode;

type rules =
  {next: int, rs: ((term * term) list * (term * term)) list,
   net: (int * ((term * term) list * (term * term))) Net.net};

val empty_rules : rules = {next = 0, rs = [], net = Net.empty};

fun add_rule (r as (_, (lhs, _)), {next, rs, net} : rules) =
  {next = next - 1, rs = r :: rs, net = Net.insert_term
     ((Pattern.eta_contract lhs, (next, r)), net, K false)};

fun merge_rules
  ({next, rs = rs1, net} : rules) ({next = next2, rs = rs2, ...} : rules) =
  foldr add_rule (rs2 \\ rs1, {next = next, rs = rs1, net = net});

fun condrew sign rules procs =
  let
    val tsig = Sign.tsig_of sign;

    fun rew tm =
      Pattern.rewrite_term tsig [] (condrew' :: procs) tm
    and condrew' tm = get_first (fn (_, (prems, (tm1, tm2))) =>
      let
        fun ren t = if_none (Term.rename_abs tm1 tm t) t;
        val inc = Logic.incr_indexes ([], maxidx_of_term tm + 1);
        val env as (Tenv, tenv) = Pattern.match tsig (inc tm1, tm);
        val prems' = map (pairself (rew o subst_vars env o inc o ren)) prems;
        val env' = Envir.Envir
          {maxidx = foldl Int.max
            (~1, map (Int.max o pairself maxidx_of_term) prems'),
           iTs = Vartab.make Tenv, asol = Vartab.make tenv}
      in Some (Envir.norm_term
        (Pattern.unify (sign, env', prems')) (inc (ren tm2)))
      end handle Pattern.MATCH => None | Pattern.Unif => None)
        (sort (int_ord o pairself fst)
          (Net.match_term rules (Pattern.eta_contract tm)));

  in rew end;

val chtype = change_type o Some;

fun add_prefix a b = NameSpace.pack (a :: NameSpace.unpack b);

fun msg d s = priority (implode (replicate d " ") ^ s);

fun vars_of t = rev (foldl_aterms
  (fn (vs, v as Var _) => v ins vs | (vs, _) => vs) ([], t));

fun vfs_of t = vars_of t @ sort (make_ord atless) (term_frees t);

fun forall_intr (t, prop) =
  let val (a, T) = (case t of Var ((a, _), T) => (a, T) | Free p => p)
  in all T $ Abs (a, T, abstract_over (t, prop)) end;

fun forall_intr_prf (t, prf) =
  let val (a, T) = (case t of Var ((a, _), T) => (a, T) | Free p => p)
  in Abst (a, Some T, prf_abstract_over t prf) end;

val mkabs = foldr (fn (v, t) => Abs ("x", fastype_of v, abstract_over (v, t)));

fun prf_subst_TVars tye =
  map_proof_terms (subst_TVars tye) (typ_subst_TVars tye);

fun add_types (Const ("typeof", Type (_, [T, _])), xs) =
      (case strip_type T of (_, Type (s, _)) => s ins xs | _ => xs)
  | add_types (t $ u, xs) = add_types (t, add_types (u, xs))
  | add_types (Abs (_, _, t), xs) = add_types (t, xs)
  | add_types (_, xs) = xs;

fun relevant_vars types prop = foldr (fn
      (Var ((a, i), T), vs) => (case strip_type T of
        (_, Type (s, _)) => if s mem types then a :: vs else vs
      | _ => vs)
    | (_, vs) => vs) (vars_of prop, []);


(**** theory data ****)

(* data kind 'Pure/extraction' *)

structure ExtractionArgs =
struct
  val name = "Pure/extraction";
  type T =
    {realizes_eqns : rules,
     typeof_eqns : rules,
     types : string list,
     realizers : (string list * (term * proof)) list Symtab.table,
     defs : thm list,
     expand : (string * term) list,
     prep : (Sign.sg -> proof -> proof) option}

  val empty =
    {realizes_eqns = empty_rules,
     typeof_eqns = empty_rules,
     types = [],
     realizers = Symtab.empty,
     defs = [],
     expand = [],
     prep = None};
  val copy = I;
  val prep_ext = I;

  fun merge
    (({realizes_eqns = realizes_eqns1, typeof_eqns = typeof_eqns1, types = types1,
       realizers = realizers1, defs = defs1, expand = expand1, prep = prep1},
      {realizes_eqns = realizes_eqns2, typeof_eqns = typeof_eqns2, types = types2,
       realizers = realizers2, defs = defs2, expand = expand2, prep = prep2}) : T * T) =
    {realizes_eqns = merge_rules realizes_eqns1 realizes_eqns2,
     typeof_eqns = merge_rules typeof_eqns1 typeof_eqns2,
     types = types1 union types2,
     realizers = Symtab.merge_multi' (eq_set o pairself #1)
       (realizers1, realizers2),
     defs = gen_merge_lists eq_thm defs1 defs2,
     expand = merge_lists expand1 expand2,
     prep = (case prep1 of None => prep2 | _ => prep1)};

  fun print sg (x : T) = ();
end;

structure ExtractionData = TheoryDataFun(ExtractionArgs);

fun read_condeq thy =
  let val sg = sign_of (add_syntax thy)
  in fn s =>
    let val t = Logic.varify (term_of (read_cterm sg (s, propT)))
    in (map Logic.dest_equals (Logic.strip_imp_prems t),
      Logic.dest_equals (Logic.strip_imp_concl t))
    end handle TERM _ => error ("Not a (conditional) meta equality:\n" ^ s)
  end;

(** preprocessor **)

fun set_preprocessor prep thy =
  let val {realizes_eqns, typeof_eqns, types, realizers,
    defs, expand, ...} = ExtractionData.get thy
  in
    ExtractionData.put
      {realizes_eqns = realizes_eqns, typeof_eqns = typeof_eqns, types = types,
       realizers = realizers, defs = defs, expand = expand, prep = Some prep} thy
  end;

(** equations characterizing realizability **)

fun gen_add_realizes_eqns prep_eq eqns thy =
  let val {realizes_eqns, typeof_eqns, types, realizers,
    defs, expand, prep} = ExtractionData.get thy;
  in
    ExtractionData.put
      {realizes_eqns = foldr add_rule (map (prep_eq thy) eqns, realizes_eqns),
       typeof_eqns = typeof_eqns, types = types, realizers = realizers,
       defs = defs, expand = expand, prep = prep} thy
  end

val add_realizes_eqns_i = gen_add_realizes_eqns (K I);
val add_realizes_eqns = gen_add_realizes_eqns read_condeq;

(** equations characterizing type of extracted program **)

fun gen_add_typeof_eqns prep_eq eqns thy =
  let
    val {realizes_eqns, typeof_eqns, types, realizers,
      defs, expand, prep} = ExtractionData.get thy;
    val eqns' = map (prep_eq thy) eqns;
    val ts = flat (flat
      (map (fn (ps, p) => map (fn (x, y) => [x, y]) (p :: ps)) eqns'))
  in
    ExtractionData.put
      {realizes_eqns = realizes_eqns, realizers = realizers,
       typeof_eqns = foldr add_rule (eqns', typeof_eqns),
       types = foldr add_types (ts, types),
       defs = defs, expand = expand, prep = prep} thy
  end

val add_typeof_eqns_i = gen_add_typeof_eqns (K I);
val add_typeof_eqns = gen_add_typeof_eqns read_condeq;

fun thaw (T as TFree (a, S)) =
      if ":" mem explode a then TVar (unpack_ixn a, S) else T
  | thaw (Type (a, Ts)) = Type (a, map thaw Ts)
  | thaw T = T;

fun freeze (TVar ((a, i), S)) = TFree (a ^ ":" ^ string_of_int i, S)
  | freeze (Type (a, Ts)) = Type (a, map freeze Ts)
  | freeze T = T;

fun freeze_thaw f x =
  map_term_types thaw (f (map_term_types freeze x));

fun etype_of sg vs Ts t =
  let
    val {typeof_eqns, ...} = ExtractionData.get_sg sg;
    fun err () = error ("Unable to determine type of extracted program for\n" ^
      Sign.string_of_term sg t);
    val abs = foldr (fn (T, u) => Abs ("x", T, u))
  in case strip_abs_body (freeze_thaw (condrew sg (#net typeof_eqns)
    [typeof_proc (Sign.defaultS sg) vs]) (abs (Ts,
      Const ("typeof", fastype_of1 (Ts, t) --> Type ("Type", [])) $ t))) of
      Const ("Type", _) $ u => (Logic.dest_type u handle TERM _ => err ())
    | _ => err ()
  end;

(** realizers for axioms / theorems, together with correctness proofs **)

fun gen_add_realizers prep_rlz rs thy =
  let val {realizes_eqns, typeof_eqns, types, realizers,
    defs, expand, prep} = ExtractionData.get thy
  in
    ExtractionData.put
      {realizes_eqns = realizes_eqns, typeof_eqns = typeof_eqns, types = types,
       realizers = foldr Symtab.update_multi
         (map (prep_rlz thy) (rev rs), realizers),
       defs = defs, expand = expand, prep = prep} thy
  end

fun prep_realizer thy =
  let
    val {realizes_eqns, typeof_eqns, defs, ...} =
      ExtractionData.get thy;
    val eqns = Net.merge (#net realizes_eqns, #net typeof_eqns, K false);
    val thy' = add_syntax thy;
    val sign = sign_of thy';
    val tsg = Sign.tsig_of sign;
    val rd = ProofSyntax.read_proof thy' false
  in fn (thm, (vs, s1, s2)) =>
    let
      val name = Thm.name_of_thm thm;
      val _ = assert (name <> "") "add_realizers: unnamed theorem";
      val prop = Pattern.rewrite_term tsg
        (map (Logic.dest_equals o prop_of) defs) [] (prop_of thm);
      val vars = vars_of prop;
      val T = etype_of sign vs [] prop;
      val (T', thw) = Type.freeze_thaw_type
        (if T = nullT then nullT else map fastype_of vars ---> T);
      val t = map_term_types thw (term_of (read_cterm sign (s1, T')));
      val r = foldr forall_intr (vars, freeze_thaw
        (condrew sign eqns [typeof_proc (Sign.defaultS sign) vs, rlz_proc])
          (Const ("realizes", T --> propT --> propT) $
            (if T = nullT then t else list_comb (t, vars)) $ prop));
      val prf = Reconstruct.reconstruct_proof sign r (rd s2);
    in (name, (vs, (t, prf))) end
  end;

val add_realizers_i = gen_add_realizers
  (fn _ => fn (name, (vs, t, prf)) => (name, (vs, (t, prf))));
val add_realizers = gen_add_realizers prep_realizer;

(** expanding theorems / definitions **)

fun add_expand_thm (thy, thm) =
  let
    val {realizes_eqns, typeof_eqns, types, realizers,
      defs, expand, prep} = ExtractionData.get thy;

    val name = Thm.name_of_thm thm;
    val _ = assert (name <> "") "add_expand_thms: unnamed theorem";

    val is_def =
      (case strip_comb (fst (Logic.dest_equals (prop_of thm))) of
         (Const _, ts) => forall is_Var ts andalso null (duplicates ts)
           andalso exists (fn thy =>
               is_some (Symtab.lookup (#axioms (rep_theory thy), name)))
             (thy :: ancestors_of thy)
       | _ => false) handle TERM _ => false;

    val name = Thm.name_of_thm thm;
    val _ = assert (name <> "") "add_expand_thms: unnamed theorem";
  in
    (ExtractionData.put (if is_def then
        {realizes_eqns = realizes_eqns,
         typeof_eqns = add_rule (([],
           Logic.dest_equals (prop_of (Drule.abs_def thm))), typeof_eqns),
         types = types,
         realizers = realizers, defs = gen_ins eq_thm (thm, defs),
         expand = expand, prep = prep}
      else
        {realizes_eqns = realizes_eqns, typeof_eqns = typeof_eqns, types = types,
         realizers = realizers, defs = defs,
         expand = (name, prop_of thm) ins expand, prep = prep}) thy, thm)
  end;

fun add_expand_thms thms thy = foldl (fst o add_expand_thm) (thy, thms);


(**** extract program ****)

val dummyt = Const ("dummy", dummyT);

fun extract thms thy =
  let
    val sg = sign_of (add_syntax thy);
    val tsg = Sign.tsig_of sg;
    val {realizes_eqns, typeof_eqns, types, realizers, defs, expand, prep} =
      ExtractionData.get thy;
    val typroc = typeof_proc (Sign.defaultS sg);
    val prep = if_none prep (K I) sg o ProofRewriteRules.elim_defs sg false defs o
      Reconstruct.expand_proof sg (("", None) :: map (apsnd Some) expand);
    val rrews = Net.merge (#net realizes_eqns, #net typeof_eqns, K false);

    fun find_inst prop Ts ts vs =
      let
        val rvs = relevant_vars types prop;
        val vars = vars_of prop;
        val n = Int.min (length vars, length ts);

        fun add_args ((Var ((a, i), _), t), (vs', tye)) =
          if a mem rvs then
            let val T = etype_of sg vs Ts t
            in if T = nullT then (vs', tye)
               else (a :: vs', (("'" ^ a, i), T) :: tye)
            end
          else (vs', tye)

      in foldr add_args (take (n, vars) ~~ take (n, ts), ([], [])) end;

    fun find vs = apsome snd o find_first (curry eq_set vs o fst);
    fun find' s = map snd o filter (equal s o fst)

    fun realizes_null vs prop =
      freeze_thaw (condrew sg rrews [typroc vs, rlz_proc])
        (Const ("realizes", nullT --> propT --> propT) $ nullt $ prop);

    fun corr d defs vs ts Ts hs (PBound i) _ _ = (defs, PBound i)

      | corr d defs vs ts Ts hs (Abst (s, Some T, prf)) (Abst (_, _, prf')) t =
          let val (defs', corr_prf) = corr d defs vs [] (T :: Ts)
            (dummyt :: hs) prf (incr_pboundvars 1 0 prf')
            (case t of Some (Abs (_, _, u)) => Some u | _ => None)
          in (defs', Abst (s, Some T, corr_prf)) end

      | corr d defs vs ts Ts hs (AbsP (s, Some prop, prf)) (AbsP (_, _, prf')) t =
          let
            val T = etype_of sg vs Ts prop;
            val u = if T = nullT then 
                (case t of Some u => Some (incr_boundvars 1 u) | None => None)
              else (case t of Some (Abs (_, _, u)) => Some u | _ => None);
            val (defs', corr_prf) = corr d defs vs [] (T :: Ts) (prop :: hs)
              (incr_pboundvars 0 1 prf) (incr_pboundvars 0 1 prf') u;
            val rlz = Const ("realizes", T --> propT --> propT)
          in (defs',
            if T = nullT then AbsP ("R", Some (rlz $ nullt $ prop),
              prf_subst_bounds [nullt] corr_prf)
            else Abst (s, Some T, AbsP ("R",
              Some (rlz $ Bound 0 $ incr_boundvars 1 prop), corr_prf)))
          end

      | corr d defs vs ts Ts hs (prf % Some t) (prf' % _) t' =
          let val (defs', corr_prf) = corr d defs vs (t :: ts) Ts hs prf prf'
            (case t' of Some (u $ _) => Some u | _ => None)
          in (defs', corr_prf % Some t) end

      | corr d defs vs ts Ts hs (prf1 %% prf2) (prf1' %% prf2') t =
          let
            val prop = Reconstruct.prop_of' hs prf2';
            val T = etype_of sg vs Ts prop;
            val (defs1, f, u) = if T = nullT then (defs, t, None) else
              (case t of
                 Some (f $ u) => (defs, Some f, Some u)
               | _ =>
                 let val (defs1, u) = extr d defs vs [] Ts hs prf2'
                 in (defs1, None, Some u) end)
            val (defs2, corr_prf1) = corr d defs1 vs [] Ts hs prf1 prf1' f;
            val (defs3, corr_prf2) = corr d defs2 vs [] Ts hs prf2 prf2' u;
          in
            if T = nullT then (defs3, corr_prf1 %% corr_prf2) else
              (defs3, corr_prf1 % u %% corr_prf2)
          end

      | corr d defs vs ts Ts hs (prf0 as PThm ((name, _), prf, prop, Some Ts')) _ _ =
          let
            val (vs', tye) = find_inst prop Ts ts vs;
            val tye' = (map fst (term_tvars prop) ~~ Ts') @ tye;
            val T = etype_of sg vs' [] prop;
            val defs' = if T = nullT then defs
              else fst (extr d defs vs ts Ts hs prf0)
          in
            if T = nullT andalso realizes_null vs' prop = prop then (defs, prf0)
            else case Symtab.lookup (realizers, name) of
              None => (case find vs' (find' name defs') of
                None =>
                  let
                    val _ = assert (T = nullT) "corr: internal error";
                    val _ = msg d ("Building correctness proof for " ^ quote name ^
                      (if null vs' then ""
                       else " (relevant variables: " ^ commas_quote vs' ^ ")"));
                    val prf' = prep (Reconstruct.reconstruct_proof sg prop prf);
                    val (defs'', corr_prf) =
                      corr (d + 1) defs' vs' [] [] [] prf' prf' None;
                    val args = vfs_of prop;
                    val corr_prf' = foldr forall_intr_prf (args, corr_prf);
                  in
                    ((name, (vs', ((nullt, nullt), corr_prf'))) :: defs',
                     prf_subst_TVars tye' corr_prf')
                  end
              | Some (_, prf') => (defs', prf_subst_TVars tye' prf'))
            | Some rs => (case find vs' rs of
                Some (_, prf') => (defs', prf_subst_TVars tye' prf')
              | None => error ("corr: no realizer for instance of theorem " ^
                  quote name ^ ":\n" ^ Sign.string_of_term sg (Envir.beta_norm
                    (Reconstruct.prop_of (proof_combt (prf0, ts))))))
          end

      | corr d defs vs ts Ts hs (prf0 as PAxm (s, prop, Some Ts')) _ _ =
          let
            val (vs', tye) = find_inst prop Ts ts vs;
            val tye' = (map fst (term_tvars prop) ~~ Ts') @ tye
          in
            case find vs' (Symtab.lookup_multi (realizers, s)) of
              Some (_, prf) => (defs, prf_subst_TVars tye' prf)
            | None => error ("corr: no realizer for instance of axiom " ^
                quote s ^ ":\n" ^ Sign.string_of_term sg (Envir.beta_norm
                  (Reconstruct.prop_of (proof_combt (prf0, ts)))))
          end

      | corr d defs vs ts Ts hs _ _ _ = error "corr: bad proof"

    and extr d defs vs ts Ts hs (PBound i) = (defs, Bound i)

      | extr d defs vs ts Ts hs (Abst (s, Some T, prf)) =
          let val (defs', t) = extr d defs vs []
            (T :: Ts) (dummyt :: hs) (incr_pboundvars 1 0 prf)
          in (defs', Abs (s, T, t)) end

      | extr d defs vs ts Ts hs (AbsP (s, Some t, prf)) =
          let
            val T = etype_of sg vs Ts t;
            val (defs', t) = extr d defs vs [] (T :: Ts) (t :: hs)
              (incr_pboundvars 0 1 prf)
          in (defs',
            if T = nullT then subst_bound (nullt, t) else Abs (s, T, t))
          end

      | extr d defs vs ts Ts hs (prf % Some t) =
          let val (defs', u) = extr d defs vs (t :: ts) Ts hs prf
          in (defs', u $ t) end

      | extr d defs vs ts Ts hs (prf1 %% prf2) =
          let
            val (defs', f) = extr d defs vs [] Ts hs prf1;
            val prop = Reconstruct.prop_of' hs prf2;
            val T = etype_of sg vs Ts prop
          in
            if T = nullT then (defs', f) else
              let val (defs'', t) = extr d defs' vs [] Ts hs prf2
              in (defs'', f $ t) end
          end

      | extr d defs vs ts Ts hs (prf0 as PThm ((s, _), prf, prop, Some Ts')) =
          let
            val (vs', tye) = find_inst prop Ts ts vs;
            val tye' = (map fst (term_tvars prop) ~~ Ts') @ tye
          in
            case Symtab.lookup (realizers, s) of
              None => (case find vs' (find' s defs) of
                None =>
                  let
                    val _ = msg d ("Extracting " ^ quote s ^
                      (if null vs' then ""
                       else " (relevant variables: " ^ commas_quote vs' ^ ")"));
                    val prf' = prep (Reconstruct.reconstruct_proof sg prop prf);
                    val (defs', t) = extr (d + 1) defs vs' [] [] [] prf';
                    val (defs'', corr_prf) =
                      corr (d + 1) defs' vs' [] [] [] prf' prf' (Some t);

                    val nt = Envir.beta_norm t;
                    val args = vfs_of prop;
                    val args' = filter (fn v => Logic.occs (v, nt)) args;
                    val t' = mkabs (args', nt);
                    val T = fastype_of t';
                    val cname = add_prefix "extr" (space_implode "_" (s :: vs'));
                    val c = Const (cname, T);
                    val u = mkabs (args, list_comb (c, args'));
                    val eqn = Logic.mk_equals (c, t');
                    val rlz =
                      Const ("realizes", fastype_of nt --> propT --> propT);
                    val lhs = rlz $ nt $ prop;
                    val rhs = rlz $ list_comb (c, args') $ prop;
                    val f = Abs ("x", T, rlz $ list_comb (Bound 0, args') $ prop);

                    val corr_prf' = foldr forall_intr_prf (args,
                      ProofRewriteRules.rewrite_terms
                        (freeze_thaw (condrew sg rrews [typroc vs', rlz_proc]))
                        (Proofterm.rewrite_proof_notypes ([], [])
                          (chtype [] equal_elim_axm %> lhs %> rhs %%
                            (chtype [propT] symmetric_axm %> rhs %> lhs %%
                              (chtype [propT, T] combination_axm %> f %> f %> c %> t' %%
                                (chtype [T --> propT] reflexive_axm %> f) %%
                                PAxm (cname ^ "_def", eqn,
                                  Some (map TVar (term_tvars eqn))))) %%
                            corr_prf)))
                  in
                    ((s, (vs', ((t', u), corr_prf'))) :: defs',
                     subst_TVars tye' u)
                  end
              | Some ((_, u), _) => (defs, subst_TVars tye' u))
            | Some rs => (case find vs' rs of
                Some (t, _) => (defs, subst_TVars tye' t)
              | None => error ("extr: no realizer for instance of theorem " ^
                  quote s ^ ":\n" ^ Sign.string_of_term sg (Envir.beta_norm
                    (Reconstruct.prop_of (proof_combt (prf0, ts))))))
          end

      | extr d defs vs ts Ts hs (prf0 as PAxm (s, prop, Some Ts')) =
          let
            val (vs', tye) = find_inst prop Ts ts vs;
            val tye' = (map fst (term_tvars prop) ~~ Ts') @ tye
          in
            case find vs' (Symtab.lookup_multi (realizers, s)) of
              Some (t, _) => (defs, subst_TVars tye' t)
            | None => error ("no realizer for instance of axiom " ^
                quote s ^ ":\n" ^ Sign.string_of_term sg (Envir.beta_norm
                  (Reconstruct.prop_of (proof_combt (prf0, ts)))))
          end

      | extr d defs vs ts Ts hs _ = error "extr: bad proof";

    fun prep_thm thm =
      let
        val {prop, der = (_, prf), sign, ...} = rep_thm thm;
        val name = Thm.name_of_thm thm;
        val _ = assert (name <> "") "extraction: unnamed theorem";
        val _ = assert (etype_of sg [] [] prop <> nullT) ("theorem " ^
          quote name ^ " has no computational content")
      in (name, Reconstruct.reconstruct_proof sign prop prf) end;

    val (names, prfs) = ListPair.unzip (map prep_thm thms);
    val defs = foldl (fn (defs, prf) =>
      fst (extr 0 defs [] [] [] [] prf)) ([], prfs);
    val {path, ...} = Sign.rep_sg sg;

    fun add_def ((s, (vs, ((t, u), _))), thy) = 
      let
        val ft = fst (Type.freeze_thaw t);
        val fu = fst (Type.freeze_thaw u);
        val name = add_prefix "extr" (space_implode "_" (s :: vs))
      in case Sign.const_type (sign_of thy) name of
          None => if t = nullt then thy else thy |>
            Theory.add_consts_i [(name, fastype_of ft, NoSyn)] |>
            fst o PureThy.add_defs_i false [((name ^ "_def",
              Logic.mk_equals (head_of (strip_abs_body fu), ft)), [])]
        | Some _ => thy
      end;

    fun add_thm ((s, (vs, (_, prf))), thy) = fst (PureThy.store_thm
          ((add_prefix "extr" (space_implode "_" (s :: vs)) ^
            "_correctness", standard (gen_all (ProofChecker.thm_of_proof thy
              (fst (Proofterm.freeze_thaw_prf (ProofRewriteRules.rewrite_terms
                (Pattern.rewrite_term (Sign.tsig_of (sign_of thy)) []
                  [rlz_proc']) prf)))))), []) thy)

  in thy |>
    Theory.absolute_path |>
    curry (foldr add_def) defs |>
    curry (foldr add_thm) (filter (fn (s, _) => s mem names) defs) |>
    Theory.add_path (NameSpace.pack (if_none path []))
  end;


(**** interface ****)

structure P = OuterParse and K = OuterSyntax.Keyword;

val realizersP =
  OuterSyntax.command "realizers"
  "specify realizers for primitive axioms / theorems, together with correctness proof"
  K.thy_decl
    (Scan.repeat1 (P.xname --
       Scan.optional (P.$$$ "(" |-- P.list1 P.name --| P.$$$ ")") [] --|
       P.$$$ ":" -- P.string -- P.string) >>
     (fn xs => Toplevel.theory (fn thy => add_realizers
       (map (fn (((a, vs), s1), s2) =>
         (PureThy.get_thm thy a, (vs, s1, s2))) xs) thy)));

val realizabilityP =
  OuterSyntax.command "realizability"
  "add equations characterizing realizability" K.thy_decl
  (Scan.repeat1 P.string >> (Toplevel.theory o add_realizes_eqns));

val typeofP =
  OuterSyntax.command "extract_type"
  "add equations characterizing type of extracted program" K.thy_decl
  (Scan.repeat1 P.string >> (Toplevel.theory o add_typeof_eqns));

val extractP =
  OuterSyntax.command "extract" "extract terms from proofs" K.thy_decl
    (Scan.repeat1 P.xname >> (fn xs => Toplevel.theory
      (fn thy => extract (map (PureThy.get_thm thy) xs) thy)));

val parsers = [realizersP, realizabilityP, typeofP, extractP];

val setup =
  [ExtractionData.init,

   add_typeof_eqns
     ["(typeof (PROP P)) == (Type (TYPE(Null))) ==>  \
    \  (typeof (PROP Q)) == (Type (TYPE('Q))) ==>  \
    \    (typeof (PROP P ==> PROP Q)) == (Type (TYPE('Q)))",

      "(typeof (PROP Q)) == (Type (TYPE(Null))) ==>  \
    \    (typeof (PROP P ==> PROP Q)) == (Type (TYPE(Null)))",

      "(typeof (PROP P)) == (Type (TYPE('P))) ==>  \
    \  (typeof (PROP Q)) == (Type (TYPE('Q))) ==>  \
    \    (typeof (PROP P ==> PROP Q)) == (Type (TYPE('P => 'Q)))",

      "(%x. typeof (PROP P (x))) == (%x. Type (TYPE(Null))) ==>  \
    \    (typeof (!!x. PROP P (x))) == (Type (TYPE(Null)))",

      "(%x. typeof (PROP P (x))) == (%x. Type (TYPE('P))) ==>  \
    \    (typeof (!!x::'a. PROP P (x))) == (Type (TYPE('a => 'P)))",

      "(%x. typeof (f (x))) == (%x. Type (TYPE('f))) ==>  \
    \    (typeof (f)) == (Type (TYPE('f)))"],

   add_realizes_eqns
     ["(typeof (PROP P)) == (Type (TYPE(Null))) ==>  \
    \    (realizes (r) (PROP P ==> PROP Q)) ==  \
    \    (PROP realizes (Null) (PROP P) ==> PROP realizes (r) (PROP Q))",

      "(typeof (PROP P)) == (Type (TYPE('P))) ==>  \
    \  (typeof (PROP Q)) == (Type (TYPE(Null))) ==>  \
    \    (realizes (r) (PROP P ==> PROP Q)) ==  \
    \    (!!x::'P. PROP realizes (x) (PROP P) ==> PROP realizes (Null) (PROP Q))",

      "(realizes (r) (PROP P ==> PROP Q)) ==  \
    \  (!!x. PROP realizes (x) (PROP P) ==> PROP realizes (r (x)) (PROP Q))",

      "(%x. typeof (PROP P (x))) == (%x. Type (TYPE(Null))) ==>  \
    \    (realizes (r) (!!x. PROP P (x))) ==  \
    \    (!!x. PROP realizes (Null) (PROP P (x)))",

      "(realizes (r) (!!x. PROP P (x))) ==  \
    \  (!!x. PROP realizes (r (x)) (PROP P (x)))"],

   Attrib.add_attributes
     [("extraction_expand",
       (Attrib.no_args add_expand_thm, K Attrib.undef_local_attribute),
       "specify theorems / definitions to be expanded during extraction")]];

end;

OuterSyntax.add_parsers Extraction.parsers;
