(*  Title:      HOL/Tools/inductive_realizer.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Porgram extraction from proofs involving inductive predicates:
Realizers for induction and elimination rules
*)

signature INDUCTIVE_REALIZER =
sig
  val add_ind_realizers: string -> string list -> theory -> theory
  val setup: (theory -> theory) list
end;

structure InductiveRealizer : INDUCTIVE_REALIZER =
struct

val all_simps = map (symmetric o mk_meta_eq) (thms "HOL.all_simps");

fun prf_of thm =
  let val {sign, prop, der = (_, prf), ...} = rep_thm thm
  in Reconstruct.reconstruct_proof sign prop prf end;

fun forall_intr_prf (t, prf) =
  let val (a, T) = (case t of Var ((a, _), T) => (a, T) | Free p => p)
  in Abst (a, Some T, Proofterm.prf_abstract_over t prf) end;

fun subsets [] = [[]]
  | subsets (x::xs) =
      let val ys = subsets xs
      in ys @ map (cons x) ys end;

val set_of = fst o dest_Const o head_of o snd o HOLogic.dest_mem;

fun strip_all t =
  let
    fun strip used (Const ("all", _) $ Abs (s, T, t)) =
          let val s' = variant used s
          in strip (s'::used) (subst_bound (Free (s', T), t)) end
      | strip used ((t as Const ("==>", _) $ P) $ Q) = t $ strip used Q
      | strip _ t = t;
  in strip (add_term_free_names (t, [])) t end;

fun relevant_vars prop = foldr (fn
      (Var ((a, i), T), vs) => (case strip_type T of
        (_, Type (s, _)) => if s mem ["bool", "set"] then (a, T) :: vs else vs
      | _ => vs)
    | (_, vs) => vs) (term_vars prop, []);

fun params_of intr = map (fst o fst o dest_Var) (term_vars
  (snd (HOLogic.dest_mem (HOLogic.dest_Trueprop
    (Logic.strip_imp_concl intr)))));

fun dt_of_intrs thy vs intrs =
  let
    val iTs = term_tvars (prop_of (hd intrs));
    val Tvs = map TVar iTs;
    val (_ $ (_ $ _ $ S)) = Logic.strip_imp_concl (prop_of (hd intrs));
    val (Const (s, _), ts) = strip_comb S;
    val params = map dest_Var ts;
    val tname = space_implode "_" (Sign.base_name s ^ "T" :: vs);
    fun constr_of_intr intr = (Sign.base_name (Thm.name_of_thm intr),
      map (Type.unvarifyT o snd) (rev (Term.add_vars ([], prop_of intr)) \\ params) @
        filter_out (equal Extraction.nullT) (map
          (Type.unvarifyT o Extraction.etype_of thy vs []) (prems_of intr)),
            NoSyn);
  in (map (fn a => "'" ^ a) vs @ map (fst o fst) iTs, tname, NoSyn,
    map constr_of_intr intrs)
  end;

fun gen_realizes (Const ("realizes", Type ("fun", [T, _])) $ t $
      (Const ("op :", Type ("fun", [U, _])) $ x $ Var (ixn, _))) =
        Var (ixn, [T, U] ---> HOLogic.boolT) $ t $ x
  | gen_realizes (Const ("op :", Type ("fun", [U, _])) $ x $ Var (ixn, _)) =
      Var (ixn, U --> HOLogic.boolT) $ x
  | gen_realizes (bla as Const ("realizes", Type ("fun", [T, _])) $ t $ P) =
      if T = Extraction.nullT then P
      else (case strip_comb P of
          (Var (ixn, U), ts) => list_comb (Var (ixn, T --> U), t :: ts)
        | _ => error "gen_realizes: variable expected")
  | gen_realizes (t $ u) = gen_realizes t $ gen_realizes u
  | gen_realizes (Abs (s, T, t)) = Abs (s, T, gen_realizes t)
  | gen_realizes t = t;

fun mk_rlz T = Const ("realizes", [T, HOLogic.boolT] ---> HOLogic.boolT);
fun mk_rlz' T = Const ("realizes", [T, propT] ---> propT);

(** turn "P" into "%r x. realizes r (P x)" or "%r x. realizes r (x : P)" **)

fun gen_rvar vs (t as Var ((a, 0), T)) =
      let val U = TVar (("'" ^ a, 0), HOLogic.typeS)
      in case try HOLogic.dest_setT T of
          None => if body_type T <> HOLogic.boolT then t else
            let
              val Ts = binder_types T;
              val i = length Ts;
              val xs = map (pair "x") Ts;
              val u = list_comb (t, map Bound (i - 1 downto 0))
            in 
              if a mem vs then
                list_abs (("r", U) :: xs, mk_rlz U $ Bound i $ u)
              else list_abs (xs, mk_rlz Extraction.nullT $ Extraction.nullt $ u)
            end
        | Some T' => if a mem vs then
              Abs ("r", U, Abs ("x", T', mk_rlz U $ Bound 1 $
                (HOLogic.mk_mem (Bound 0, t))))
            else Abs ("x", T', mk_rlz Extraction.nullT $ Extraction.nullt $
              (HOLogic.mk_mem (Bound 0, t)))
      end
  | gen_rvar _ t = t;

fun mk_realizes_eqn n vs intrs =
  let
    val iTs = term_tvars (prop_of (hd intrs));
    val Tvs = map TVar iTs;
    val _ $ (_ $ _ $ S) = concl_of (hd intrs);
    val (Const (s, T), ts') = strip_comb S;
    val setT = body_type T;
    val elT = HOLogic.dest_setT setT;
    val x = Var (("x", 0), elT);
    val rT = if n then Extraction.nullT
      else Type (space_implode "_" (s ^ "T" :: vs),
        map (fn a => TVar (("'" ^ a, 0), HOLogic.typeS)) vs @ Tvs);
    val r = if n then Extraction.nullt else Var ((Sign.base_name s, 0), rT);
    val rvs = relevant_vars S;
    val vs' = map fst rvs \\ vs;
    val rname = space_implode "_" (s ^ "R" :: vs);

    fun mk_Tprem n v =
      let val Some T = assoc (rvs, v)
      in (Const ("typeof", T --> Type ("Type", [])) $ Var ((v, 0), T),
        Extraction.mk_typ (if n then Extraction.nullT
          else TVar (("'" ^ v, 0), HOLogic.typeS)))
      end;

    val prems = map (mk_Tprem true) vs' @ map (mk_Tprem false) vs;
    val ts = map (gen_rvar vs) ts';
    val argTs = map fastype_of ts;

  in ((prems, (Const ("typeof", setT --> Type ("Type", [])) $ S,
       Extraction.mk_typ rT)),
    (prems, (mk_rlz rT $ r $ HOLogic.mk_mem (x, S),
       if n then
         HOLogic.mk_mem (x, list_comb (Const (rname, argTs ---> setT), ts))
       else HOLogic.mk_mem (HOLogic.mk_prod (r, x), list_comb (Const (rname,
         argTs ---> HOLogic.mk_setT (HOLogic.mk_prodT (rT, elT))), ts)))))
  end;

fun fun_of_prem thy rsets vs params rule intr =
  let
    (* add_term_vars and Term.add_vars may return variables in different order *)
    val args = map (Free o apfst fst o dest_Var)
      (add_term_vars (prop_of intr, []) \\ map Var params);
    val args' = map (Free o apfst fst)
      (Term.add_vars ([], prop_of intr) \\ params);
    val rule' = strip_all rule;
    val conclT = Extraction.etype_of thy vs [] (Logic.strip_imp_concl rule');
    val used = map (fst o dest_Free) args;

    fun is_rec t = not (null (term_consts t inter rsets));

    fun is_meta (Const ("all", _) $ Abs (s, _, P)) = is_meta P
      | is_meta (Const ("==>", _) $ _ $ Q) = is_meta Q
      | is_meta (Const ("Trueprop", _) $ (Const ("op :", _) $ _ $ _)) = true
      | is_meta _ = false;

    fun fun_of ts rts args used (prem :: prems) =
          let
            val T = Extraction.etype_of thy vs [] prem;
            val [x, r] = variantlist (["x", "r"], used)
          in if T = Extraction.nullT
            then fun_of ts rts args used prems
            else if is_rec prem then
              if is_meta prem then
                let
                  val prem' :: prems' = prems;
                  val U = Extraction.etype_of thy vs [] prem';
                in if U = Extraction.nullT
                  then fun_of (Free (x, T) :: ts)
                    (Free (r, binder_types T ---> HOLogic.unitT) :: rts)
                    (Free (x, T) :: args) (x :: r :: used) prems'
                  else fun_of (Free (x, T) :: ts) (Free (r, U) :: rts)
                    (Free (r, U) :: Free (x, T) :: args) (x :: r :: used) prems'
                end
              else (case strip_type T of
                  (Ts, Type ("*", [T1, T2])) =>
                    let
                      val fx = Free (x, Ts ---> T1);
                      val fr = Free (r, Ts ---> T2);
                      val bs = map Bound (length Ts - 1 downto 0);
                      val t = list_abs (map (pair "z") Ts,
                        HOLogic.mk_prod (list_comb (fx, bs), list_comb (fr, bs)))
                    in fun_of (fx :: ts) (fr :: rts) (t::args)
                      (x :: r :: used) prems
                    end
                | (Ts, U) => fun_of (Free (x, T) :: ts)
                    (Free (r, binder_types T ---> HOLogic.unitT) :: rts)
                    (Free (x, T) :: args) (x :: r :: used) prems)
            else fun_of (Free (x, T) :: ts) rts (Free (x, T) :: args)
              (x :: used) prems
          end
      | fun_of ts rts args used [] =
          let val xs = rev (rts @ ts)
          in if conclT = Extraction.nullT
            then list_abs_free (map dest_Free xs, HOLogic.unit)
            else list_abs_free (map dest_Free xs, list_comb
              (Free ("r" ^ Sign.base_name (Thm.name_of_thm intr),
                map fastype_of (rev args) ---> conclT), rev args))
          end

  in fun_of (rev args) [] args' used (Logic.strip_imp_prems rule') end;

fun indrule_realizer thy induct raw_induct rsets params vs rec_names rss intrs dummies =
  let
    val concls = HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of raw_induct));
    val premss = mapfilter (fn (s, rs) => if s mem rsets then
      Some (map (fn r => nth_elem (find_index_eq (prop_of r) (map prop_of intrs),
        prems_of raw_induct)) rs) else None) rss;
    val concls' = mapfilter (fn (s, _) => if s mem rsets then
        find_first (fn concl => s mem term_consts concl) concls
      else None) rss;
    val fs = flat (snd (foldl_map (fn (intrs, (prems, dummy)) =>
      let
        val (intrs1, intrs2) = splitAt (length prems, intrs);
        val fs = map (fn (rule, intr) =>
          fun_of_prem thy rsets vs params rule intr) (prems ~~ intrs1)
      in (intrs2, if dummy then Const ("arbitrary",
          HOLogic.unitT --> body_type (fastype_of (hd fs))) :: fs
        else fs)
      end) (intrs, (premss ~~ dummies))));
    val frees = foldl Term.add_frees ([], fs);
    val Ts = map fastype_of fs;
    val rlzs = mapfilter (fn (a, concl) =>
      let val T = Extraction.etype_of thy vs [] concl
      in if T = Extraction.nullT then None
        else Some (list_comb (Const (a, Ts ---> T), fs))
      end) (rec_names ~~ concls')
  in if null rlzs then Extraction.nullt else
    let
      val r = foldr1 HOLogic.mk_prod rlzs;
      val x = Free ("x", Extraction.etype_of thy vs [] (hd (prems_of induct)));
      fun name_of_fn intr = "r" ^ Sign.base_name (Thm.name_of_thm intr);
      val r' = list_abs_free (mapfilter (fn intr =>
        apsome (pair (name_of_fn intr)) (assoc (frees, name_of_fn intr))) intrs,
          if length concls = 1 then r $ x else r)
    in
      if length concls = 1 then lambda x r' else r'
    end
  end;

val nonempty_msg = explode "Nonemptiness check failed for datatype ";

fun add_dummy name dname (x as (_, (vs, s, mfx, cs))) =
  if name = s then (true, (vs, s, mfx, (dname, [HOLogic.unitT], NoSyn) :: cs))
  else x;

fun add_dummies f dts used thy =
  apsnd (pair (map fst dts)) (transform_error (f (map snd dts)) thy)
  handle ERROR_MESSAGE msg => if nonempty_msg prefix explode msg then
      let
        val name = Sign.base_name
          (implode (drop (length nonempty_msg, explode msg)));
        val dname = variant used "Dummy"
      in add_dummies f (map (add_dummy name dname) dts) (dname :: used) thy
      end
    else error msg;

fun mk_realizer thy vs params ((rule, rrule), rt) =
  let
    val prems = prems_of rule;
    val xs = rev (Term.add_vars ([], prop_of rule));
    val rs = gen_rems (op = o pairself fst)
      (rev (Term.add_vars ([], prop_of rrule)), xs);

    fun mk_prf _ [] prf = prf
      | mk_prf rs (prem :: prems) prf =
          let val T = Extraction.etype_of thy vs [] prem
          in if T = Extraction.nullT
            then AbsP ("H", Some (mk_rlz' T $ Extraction.nullt $ prem),
              mk_prf rs prems prf)
            else forall_intr_prf (Var (hd rs), AbsP ("H", Some (mk_rlz' T $
              Var (hd rs) $ prem), mk_prf (tl rs) prems prf))
          end;

    val subst = map (fn v as (ixn, _) => (ixn, gen_rvar vs (Var v))) xs;
    val prf = Proofterm.map_proof_terms
      (subst_vars ([], subst)) I (prf_of rrule);

  in (Thm.name_of_thm rule, (vs,
    if rt = Extraction.nullt then rt else
      foldr (uncurry lambda) (map Var xs, rt),
    foldr forall_intr_prf (map Var xs, mk_prf rs prems (Proofterm.proof_combP
      (prf, map PBound (length prems - 1 downto 0))))))
  end;

fun add_rule (rss, r) =
  let
    val _ $ (_ $ _ $ S) = concl_of r;
    val (Const (s, _), _) = strip_comb S;
    val rs = if_none (assoc (rss, s)) [];
  in overwrite (rss, (s, rs @ [r])) end;

fun add_ind_realizer rsets intrs induct raw_induct elims (thy, vs) =
  let
    val iTs = term_tvars (prop_of (hd intrs));
    val ar = length vs + length iTs;
    val (_ $ (_ $ _ $ S)) = Logic.strip_imp_concl (prop_of (hd intrs));
    val (_, params) = strip_comb S;
    val params' = map dest_Var params;
    val rss = foldl add_rule ([], intrs);
    val (prfx, _) = split_last (NameSpace.unpack (fst (hd rss)));
    val tnames = map (fn s => space_implode "_" (s ^ "T" :: vs)) rsets;
    val {path, ...} = Sign.rep_sg (sign_of thy);
    val thy1 = thy |>
      Theory.root_path |>
      Theory.add_path (NameSpace.pack prfx);
    val (ty_eqs, rlz_eqs) = split_list
      (map (fn (s, rs) => mk_realizes_eqn (not (s mem rsets)) vs rs) rss);

    val thy1' = thy1 |>
      Theory.copy |>
      Theory.add_types (map (fn s => (Sign.base_name s, ar, NoSyn)) tnames) |>
      Theory.add_arities_i (map (fn s =>
        (s, replicate ar HOLogic.typeS, HOLogic.typeS)) tnames) |>
        Extraction.add_typeof_eqns_i ty_eqs;
    val dts = mapfilter (fn (s, rs) => if s mem rsets then
      Some (dt_of_intrs thy1' vs rs) else None) rss;

    (** datatype representing computational content of inductive set **)

    val (thy2, (dummies, dt_info)) = thy1 |>
      (if null dts then rpair ([], None) else
        apsnd (apsnd Some) o add_dummies (DatatypePackage.add_datatype_i false
          (map #2 dts)) (map (pair false) dts) []) |>>
      Extraction.add_typeof_eqns_i ty_eqs |>>
      Extraction.add_realizes_eqns_i rlz_eqs;
    fun get f x = if_none (apsome f x) [];
    val rec_names = distinct (map (fst o dest_Const o head_of o fst o
      HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) (get #rec_thms dt_info));
    val (_, constrss) = foldl_map (fn ((recs, dummies), (s, rs)) =>
      if s mem rsets then
        let
          val (d :: dummies') = dummies;
          val (recs1, recs2) = splitAt (length rs, if d then tl recs else recs)
        in ((recs2, dummies'), map (head_of o hd o rev o snd o strip_comb o
          fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) recs1)
        end
      else ((recs, dummies), replicate (length rs) Extraction.nullt))
        ((get #rec_thms dt_info, dummies), rss);
    val rintrs = map (fn (intr, c) => Pattern.eta_contract (gen_realizes
      (Extraction.realizes_of thy2 vs
        c (prop_of (forall_intr_list (map (cterm_of (sign_of thy2) o Var)
          (rev (Term.add_vars ([], prop_of intr)) \\ params')) intr)))))
            (intrs ~~ flat constrss);
    val rlzsets = distinct (map (fn rintr => snd (HOLogic.dest_mem
      (HOLogic.dest_Trueprop (Logic.strip_assums_concl rintr)))) rintrs);

    (** realizability predicate **)

    val (thy3', ind_info) = thy2 |>
      InductivePackage.add_inductive_i false true "" false false false
        (map Logic.unvarify rlzsets) (map (fn (rintr, intr) =>
          ((Sign.base_name (Thm.name_of_thm intr), strip_all
            (Logic.unvarify rintr)), [])) (rintrs ~~ intrs)) [] |>>
      Theory.absolute_path;
    val thy3 = PureThy.hide_thms false
      (map Thm.name_of_thm (#intrs ind_info)) thy3';

    (** realizer for induction rule **)

    val Ps = mapfilter (fn _ $ M $ P => if set_of M mem rsets then
      Some (fst (fst (dest_Var (head_of P)))) else None)
        (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of raw_induct)));

    fun add_ind_realizer (thy, Ps) =
      let
        val r = indrule_realizer thy induct raw_induct rsets params'
          (vs @ Ps) rec_names rss intrs dummies;
        val rlz = strip_all (Logic.unvarify (gen_realizes
          (Extraction.realizes_of thy (vs @ Ps) r (prop_of induct))));
        val rews = map mk_meta_eq
          (fst_conv :: snd_conv :: get #rec_thms dt_info);
        val thm = simple_prove_goal_cterm (cterm_of (sign_of thy) rlz) (fn prems =>
          [if length rss = 1 then
             cut_facts_tac [hd prems] 1 THEN etac (#induct ind_info) 1
           else EVERY [rewrite_goals_tac (rews @ all_simps),
             REPEAT (rtac allI 1), rtac (#induct ind_info) 1],
           rewrite_goals_tac rews,
           REPEAT ((resolve_tac prems THEN_ALL_NEW EVERY'
             [K (rewrite_goals_tac rews), ObjectLogic.atomize_tac,
              DEPTH_SOLVE_1 o FIRST' [atac, etac allE, etac impE]]) 1)]);
        val (thy', thm') = PureThy.store_thm ((space_implode "_"
          (Thm.name_of_thm induct :: vs @ Ps @ ["correctness"]), thm), []) thy
      in
        Extraction.add_realizers_i
          [mk_realizer thy' (vs @ Ps) params' ((induct, thm'), r)] thy'
      end;

    (** realizer for elimination rules **)

    val case_names = map (fst o dest_Const o head_of o fst o HOLogic.dest_eq o
      HOLogic.dest_Trueprop o prop_of o hd) (get #case_thms dt_info);

    fun add_elim_realizer Ps ((((elim, elimR), case_thms), case_name), dummy) thy =
      let
        val (prem :: prems) = prems_of elim;
        val p = Logic.list_implies (prems @ [prem], concl_of elim);
        val T' = Extraction.etype_of thy (vs @ Ps) [] p;
        val T = if dummy then (HOLogic.unitT --> body_type T') --> T' else T';
        val Ts = filter_out (equal Extraction.nullT)
          (map (Extraction.etype_of thy (vs @ Ps) []) (prems_of elim));
        val r = if null Ps then Extraction.nullt
          else list_abs (map (pair "x") Ts, list_comb (Const (case_name, T),
            (if dummy then
               [Abs ("x", HOLogic.unitT, Const ("arbitrary", body_type T))]
             else []) @
            map Bound ((length prems - 1 downto 0) @ [length prems])));
        val rlz = strip_all (Logic.unvarify (gen_realizes
          (Extraction.realizes_of thy (vs @ Ps) r (prop_of elim))));
        val rews = map mk_meta_eq case_thms;
        val thm = simple_prove_goal_cterm (cterm_of (sign_of thy) rlz) (fn prems =>
          [cut_facts_tac [hd prems] 1,
           etac elimR 1,
           ALLGOALS (EVERY' [etac Pair_inject, asm_simp_tac HOL_basic_ss]),
           rewrite_goals_tac rews,
           REPEAT ((resolve_tac prems THEN_ALL_NEW (ObjectLogic.atomize_tac THEN'
             DEPTH_SOLVE_1 o FIRST' [atac, etac allE, etac impE])) 1)]);
        val (thy', thm') = PureThy.store_thm ((space_implode "_"
          (Thm.name_of_thm elim :: vs @ Ps @ ["correctness"]), thm), []) thy
      in
        Extraction.add_realizers_i
          [mk_realizer thy' (vs @ Ps) params' ((elim, thm'), r)] thy'
      end;

    (** add realizers to theory **)

    val rintr_thms = flat (map (fn (_, rs) => map (fn r => nth_elem
      (find_index_eq r intrs, #intrs ind_info)) rs) rss);
    val thy4 = foldl add_ind_realizer (thy3, subsets Ps);
    val thy5 = Extraction.add_realizers_i
      (map (mk_realizer thy4 vs params')
         (map (fn ((rule, rrule), c) => ((rule, rrule), list_comb (c,
            map Var (rev (Term.add_vars ([], prop_of rule)) \\ params')))) 
              (flat (map snd rss) ~~ rintr_thms ~~ flat constrss))) thy4;
    val elimps = mapfilter (fn (s, _) => if s mem rsets then
        find_first (fn (thm, _) => s mem term_consts (hd (prems_of thm)))
          (elims ~~ #elims ind_info)
      else None) rss;
    val thy6 = foldl (fn (thy, p as ((((elim, _), _), _), _)) => thy |>
      add_elim_realizer [] p |> add_elim_realizer [fst (fst (dest_Var
        (HOLogic.dest_Trueprop (concl_of elim))))] p) (thy5,
           elimps ~~ get #case_thms dt_info ~~ case_names ~~ dummies)

  in Theory.add_path (NameSpace.pack (if_none path [])) thy6 end;

fun add_ind_realizers name rsets thy =
  let
    val (_, {intrs, induct, raw_induct, elims, ...}) =
      (case InductivePackage.get_inductive thy name of
         None => error ("Unknown inductive set " ^ quote name)
       | Some info => info);
    val _ $ (_ $ _ $ S) = concl_of (hd intrs);
    val vss = sort (int_ord o pairself length)
      (subsets (map fst (relevant_vars S)))
  in
    foldl (add_ind_realizer rsets intrs induct raw_induct elims) (thy, vss)
  end

fun rlz_attrib arg (thy, thm) =
  let
    fun err () = error "ind_realizer: bad rule";
    val sets =
      (case HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of thm)) of
           [_] => [set_of (HOLogic.dest_Trueprop (hd (prems_of thm)))]
         | xs => map (set_of o fst o HOLogic.dest_imp) xs)
         handle TERM _ => err () | LIST _ => err ();
  in 
    (add_ind_realizers (hd sets) (case arg of
        None => sets | Some None => []
      | Some (Some sets') => sets \\ map (Sign.intern_const (sign_of thy)) sets')
      thy, thm)
  end;

val rlz_attrib_global = Attrib.syntax (Scan.lift
  (Scan.option (Args.$$$ "irrelevant" |--
    Scan.option (Args.colon |-- Scan.repeat1 Args.name))) >> rlz_attrib);

val setup = [Attrib.add_attributes [("ind_realizer",
  (rlz_attrib_global, K Attrib.undef_local_attribute),
  "add realizers for inductive set")]];

end;
