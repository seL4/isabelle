fun inst_cterm inst ct = fst (Drule.dest_equals
  (Thm.cprop_of (Thm.instantiate inst (reflexive ct))));
fun tyinst_cterm tyinst = inst_cterm (tyinst, []);

val bla = ref ([] : term list);

(******************************************************)
(*        Code generator for equational proofs        *)
(******************************************************)
fun my_mk_meta_eq thm =
  let
    val (_, eq) = Thm.dest_comb (cprop_of thm);
    val (ct, rhs) = Thm.dest_comb eq;
    val (_, lhs) = Thm.dest_comb ct
  in Thm.implies_elim (Drule.instantiate' [SOME (ctyp_of_term lhs)]
    [SOME lhs, SOME rhs] eq_reflection) thm
  end; 

structure SimprocsCodegen =
struct

val simp_thms = ref ([] : thm list);

fun parens b = if b then Pretty.enclose "(" ")" else Pretty.block;

fun gen_mk_val f xs ps = Pretty.block ([Pretty.str "val ",
  f (length xs > 1) (List.concat
    (separate [Pretty.str ",", Pretty.brk 1] (map (single o Pretty.str) xs))),
  Pretty.str " =", Pretty.brk 1] @ ps @ [Pretty.str ";"]);

val mk_val = gen_mk_val parens;
val mk_vall = gen_mk_val (K (Pretty.enclose "[" "]"));

fun rename s = if s mem ThmDatabase.ml_reserved then s ^ "'" else s;

fun mk_decomp_name (Var ((s, i), _)) = rename (if i=0 then s else s ^ string_of_int i)
  | mk_decomp_name (Const (s, _)) = rename (Codegen.mk_id (Sign.base_name s))
  | mk_decomp_name _ = "ct";

fun decomp_term_code cn ((vs, bs, ps), (v, t)) =
  if exists (equal t o fst) bs then (vs, bs, ps)
  else (case t of
      Var _ => (vs, bs @ [(t, v)], ps)
    | Const _ => (vs, if cn then bs @ [(t, v)] else bs, ps)
    | Bound _ => (vs, bs, ps)
    | Abs (s, T, t) =>
      let
        val v1 = variant vs s;
        val v2 = variant (v1 :: vs) (mk_decomp_name t)
      in
        decomp_term_code cn ((v1 :: v2 :: vs,
          bs @ [(Free (s, T), v1)],
          ps @ [mk_val [v1, v2] [Pretty.str "Thm.dest_abs", Pretty.brk 1,
            Pretty.str "NONE", Pretty.brk 1, Pretty.str v]]), (v2, t))
      end
    | t $ u =>
      let
        val v1 = variant vs (mk_decomp_name t);
        val v2 = variant (v1 :: vs) (mk_decomp_name u);
        val (vs', bs', ps') = decomp_term_code cn ((v1 :: v2 :: vs, bs,
          ps @ [mk_val [v1, v2] [Pretty.str "Thm.dest_comb", Pretty.brk 1,
            Pretty.str v]]), (v1, t));
        val (vs'', bs'', ps'') = decomp_term_code cn ((vs', bs', ps'), (v2, u))
      in
        if bs'' = bs then (vs, bs, ps) else (vs'', bs'', ps'')
      end);

val strip_tv = implode o tl o explode;

fun mk_decomp_tname (TVar ((s, i), _)) =
      strip_tv ((if i=0 then s else s ^ string_of_int i) ^ "T")
  | mk_decomp_tname (Type (s, _)) = Codegen.mk_id (Sign.base_name s) ^ "T"
  | mk_decomp_tname _ = "cT";

fun decomp_type_code ((vs, bs, ps), (v, TVar (ixn, _))) =
      if exists (equal ixn o fst) bs then (vs, bs, ps)
      else (vs, bs @ [(ixn, v)], ps)
  | decomp_type_code ((vs, bs, ps), (v, Type (_, Ts))) =
      let
        val vs' = variantlist (map mk_decomp_tname Ts, vs);
        val (vs'', bs', ps') =
          Library.foldl decomp_type_code ((vs @ vs', bs, ps @
            [mk_vall vs' [Pretty.str "Thm.dest_ctyp", Pretty.brk 1,
              Pretty.str v]]), vs' ~~ Ts)
      in
        if bs' = bs then (vs, bs, ps) else (vs'', bs', ps')
      end;

fun gen_mk_bindings s dest decomp ((vs, bs, ps), (v, x)) =
  let
    val s' = variant vs s;
    val (vs', bs', ps') = decomp ((s' :: vs, bs, ps @
      [mk_val [s'] (dest v)]), (s', x))
  in
    if bs' = bs then (vs, bs, ps) else (vs', bs', ps')
  end;

val mk_term_bindings = gen_mk_bindings "ct"
  (fn s => [Pretty.str "cprop_of", Pretty.brk 1, Pretty.str s])
  (decomp_term_code true);

val mk_type_bindings = gen_mk_bindings "cT"
  (fn s => [Pretty.str "Thm.ctyp_of_term", Pretty.brk 1, Pretty.str s])
  decomp_type_code;

fun pretty_pattern b (Const (s, _)) = Pretty.block [Pretty.str "Const",
      Pretty.brk 1, Pretty.str ("(\"" ^ s ^ "\", _)")]
  | pretty_pattern b (t as _ $ _) = parens b
      (List.concat (separate [Pretty.str " $", Pretty.brk 1]
        (map (single o pretty_pattern true) (op :: (strip_comb t)))))
  | pretty_pattern b _ = Pretty.str "_";

fun term_consts' t = foldl_aterms
  (fn (cs, c as Const _) => c ins cs | (cs, _) => cs) ([], t);

fun mk_apps s b p [] = p
  | mk_apps s b p (q :: qs) = 
      mk_apps s b (parens (b orelse not (null qs))
        [Pretty.str s, Pretty.brk 1, p, Pretty.brk 1, q]) qs;

fun mk_refleq eq ct = mk_val [eq] [Pretty.str ("Thm.reflexive " ^ ct)];

fun mk_tyinst ((s, i), s') =
  Pretty.block [Pretty.str ("((" ^ quote s ^ ","), Pretty.brk 1,
    Pretty.str (string_of_int i ^ "),"), Pretty.brk 1,
    Pretty.str (s' ^ ")")];

fun inst_ty b ty_bs t s = (case term_tvars t of
    [] => Pretty.str s
  | Ts => parens b [Pretty.str "tyinst_cterm", Pretty.brk 1,
      Pretty.list "[" "]" (map (fn (ixn, _) => mk_tyinst
        (ixn, valOf (assoc (ty_bs, ixn)))) Ts),
      Pretty.brk 1, Pretty.str s]);

fun mk_cterm_code b ty_bs ts xs (vals, t $ u) =
      let
        val (vals', p1) = mk_cterm_code true ty_bs ts xs (vals, t);
        val (vals'', p2) = mk_cterm_code true ty_bs ts xs (vals', u)
      in
        (vals'', parens b [Pretty.str "Thm.capply", Pretty.brk 1,
          p1, Pretty.brk 1, p2])
      end
  | mk_cterm_code b ty_bs ts xs (vals, Abs (s, T, t)) =
      let
        val u = Free (s, T);
        val SOME s' = assoc (ts, u);
        val p = Pretty.str s';
        val (vals', p') = mk_cterm_code true ty_bs ts (p :: xs)
          (if null (typ_tvars T) then vals
           else vals @ [(u, (("", s'), [mk_val [s'] [inst_ty true ty_bs u s']]))], t)
      in (vals',
        parens b [Pretty.str "Thm.cabs", Pretty.brk 1, p, Pretty.brk 1, p'])
      end
  | mk_cterm_code b ty_bs ts xs (vals, Bound i) = (vals, List.nth (xs, i))
  | mk_cterm_code b ty_bs ts xs (vals, t) = (case assoc (vals, t) of
        NONE =>
          let val SOME s = assoc (ts, t)
          in (if is_Const t andalso not (null (term_tvars t)) then
              vals @ [(t, (("", s), [mk_val [s] [inst_ty true ty_bs t s]]))]
            else vals, Pretty.str s)
          end
      | SOME ((_, s), _) => (vals, Pretty.str s));

fun get_cases sg =
  Symtab.foldl (fn (tab, (k, {case_rewrites, ...})) => Symtab.update_new
    ((fst (dest_Const (head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop
      (prop_of (hd case_rewrites))))))), map my_mk_meta_eq case_rewrites), tab))
        (Symtab.empty, DatatypePackage.get_datatypes_sg sg);

fun decomp_case th =
  let
    val (lhs, _) = Logic.dest_equals (prop_of th);
    val (f, ts) = strip_comb lhs;
    val (us, u) = split_last ts;
    val (Const (s, _), vs) = strip_comb u
  in (us, s, vs, u) end;

fun rename vs t =
  let
    fun mk_subst ((vs, subs), Var ((s, i), T)) =
      let val s' = variant vs s
      in if s = s' then (vs, subs)
        else (s' :: vs, ((s, i), Var ((s', i), T)) :: subs)
      end;
    val (vs', subs) = Library.foldl mk_subst ((vs, []), term_vars t)
  in (vs', subst_Vars subs t) end;

fun is_instance sg t u = t = subst_TVars_Vartab
  (Type.typ_match (Sign.tsig_of sg) (Vartab.empty,
    (fastype_of u, fastype_of t))) u handle Type.TYPE_MATCH => false;

(*
fun lookup sg fs t = Option.map snd (Library.find_first
  (is_instance sg t o fst) fs);
*)

fun lookup sg fs t = (case Library.find_first (is_instance sg t o fst) fs of
    NONE => (bla := (t ins !bla); NONE)
  | SOME (_, x) => SOME x);

fun unint sg fs t = forall (is_none o lookup sg fs) (term_consts' t);

fun mk_let s i xs ys =
  Pretty.blk (0, [Pretty.blk (i, separate Pretty.fbrk (Pretty.str s :: xs)),
    Pretty.fbrk,
    Pretty.blk (i, ([Pretty.str "in", Pretty.fbrk] @ ys)),
    Pretty.fbrk, Pretty.str "end"]);

(*****************************************************************************)
(* Generate bindings for simplifying term t                                  *)
(* mkeq: whether to generate reflexivity theorem for uninterpreted terms     *)
(* fs:   interpreted functions                                               *)
(* ts:   atomic terms                                                        *)
(* vs:   used identifiers                                                    *)
(* vals: list of bindings of the form ((eq, ct), ps) where                   *)
(*       eq: name of equational theorem                                      *)
(*       ct: name of simplified cterm                                        *)
(*       ps: ML code for creating the above two items                        *)
(*****************************************************************************)

fun mk_simpl_code sg case_tab mkeq fs ts ty_bs thm_bs ((vs, vals), t) =
  (case assoc (vals, t) of
    SOME ((eq, ct), ps) =>  (* binding already generated *) 
      if mkeq andalso eq="" then
        let val eq' = variant vs "eq"
        in ((eq' :: vs, overwrite (vals,
          (t, ((eq', ct), ps @ [mk_refleq eq' ct])))), (eq', ct))
        end
      else ((vs, vals), (eq, ct))
  | NONE => (case assoc (ts, t) of
      SOME v =>  (* atomic term *)
        let val xs = if not (null (term_tvars t)) andalso is_Const t then
          [mk_val [v] [inst_ty false ty_bs t v]] else []
        in
          if mkeq then
            let val eq = variant vs "eq"
            in ((eq :: vs, vals @
              [(t, ((eq, v), xs @ [mk_refleq eq v]))]), (eq, v))
            end
          else ((vs, if null xs then vals else vals @
            [(t, (("", v), xs))]), ("", v))
        end
    | NONE =>  (* complex term *)
        let val (f as Const (cname, _), us) = strip_comb t
        in case Symtab.lookup (case_tab, cname) of
            SOME cases =>  (* case expression *)
              let
                val (us', u) = split_last us;
                val b = unint sg fs u;
                val ((vs1, vals1), (eq, ct)) =
                  mk_simpl_code sg case_tab (not b) fs ts ty_bs thm_bs ((vs, vals), u);
                val xs = variantlist (replicate (length us') "f", vs1);
                val (vals2, ps) = foldl_map
                  (mk_cterm_code false ty_bs ts []) (vals1, us');
                val fvals = map (fn (x, p) => mk_val [x] [p]) (xs ~~ ps);
                val uT = fastype_of u;
                val (us'', _, _, u') = decomp_case (hd cases);
                val (vs2, ty_bs', ty_vals) = mk_type_bindings
                  (mk_type_bindings ((vs1 @ xs, [], []),
                    (hd xs, fastype_of (hd us''))), (ct, fastype_of u'));
                val insts1 = map mk_tyinst ty_bs';
                val i = length vals2;
   
                fun mk_case_code ((vs, vals), (f, (name, eqn))) =
                  let
                    val (fvs, cname, cvs, _) = decomp_case eqn;
                    val Ts = binder_types (fastype_of f);
                    val ys = variantlist (map (fst o fst o dest_Var) cvs, vs);
                    val cvs' = map Var (map (rpair 0) ys ~~ Ts);
                    val rs = cvs' ~~ cvs;
                    val lhs = list_comb (Const (cname, Ts ---> uT), cvs');
                    val rhs = Library.foldl betapply (f, cvs');
                    val (vs', tm_bs, tm_vals) = decomp_term_code false
                      ((vs @ ys, [], []), (ct, lhs));
                    val ((vs'', all_vals), (eq', ct')) = mk_simpl_code sg case_tab
                      false fs (tm_bs @ ts) ty_bs thm_bs ((vs', vals), rhs);
                    val (old_vals, eq_vals) = splitAt (i, all_vals);
                    val vs''' = vs @ List.filter (fn v => exists
                      (fn (_, ((v', _), _)) => v = v') old_vals) (vs'' \\ vs');
                    val insts2 = map (fn (t, s) => Pretty.block [Pretty.str "(",
                      inst_ty false ty_bs' t (valOf (assoc (thm_bs, t))), Pretty.str ",",
                      Pretty.brk 1, Pretty.str (s ^ ")")]) ((fvs ~~ xs) @
                        (map (fn (v, s) => (valOf (assoc (rs, v)), s)) tm_bs));
                    val eq'' = if null insts1 andalso null insts2 then Pretty.str name
                      else parens (eq' <> "") [Pretty.str
                          (if null cvs then "Thm.instantiate" else "Drule.instantiate"),
                        Pretty.brk 1, Pretty.str "(", Pretty.list "[" "]" insts1,
                        Pretty.str ",", Pretty.brk 1, Pretty.list "[" "]" insts2,
                        Pretty.str ")", Pretty.brk 1, Pretty.str name];
                    val eq''' = if eq' = "" then eq'' else
                      Pretty.block [Pretty.str "Thm.transitive", Pretty.brk 1,
                        eq'', Pretty.brk 1, Pretty.str eq']
                  in
                    ((vs''', old_vals), Pretty.block [pretty_pattern false lhs,
                      Pretty.str " =>",
                      Pretty.brk 1, mk_let "let" 2 (tm_vals @ List.concat (map (snd o snd) eq_vals))
                        [Pretty.str ("(" ^ ct' ^ ","), Pretty.brk 1, eq''', Pretty.str ")"]])
                  end;

                val case_names = map (fn i => Sign.base_name cname ^ "_" ^
                  string_of_int i) (1 upto length cases);
                val ((vs3, vals3), case_ps) = foldl_map mk_case_code
                  ((vs2, vals2), us' ~~ (case_names ~~ cases));
                val eq' = variant vs3 "eq";
                val ct' = variant (eq' :: vs3) "ct";
                val eq'' = variant (eq' :: ct' :: vs3) "eq";
                val case_vals =
                  fvals @ ty_vals @
                  [mk_val [ct', eq'] ([Pretty.str "(case", Pretty.brk 1,
                    Pretty.str ("term_of " ^ ct ^ " of"), Pretty.brk 1] @
                    List.concat (separate [Pretty.brk 1, Pretty.str "| "]
                      (map single case_ps)) @ [Pretty.str ")"])]
              in
                if b then
                  ((eq' :: ct' :: vs3, vals3 @
                     [(t, ((eq', ct'), case_vals))]), (eq', ct'))
                else
                  let val ((vs4, vals4), (_, ctcase)) = mk_simpl_code sg case_tab false
                    fs ts ty_bs thm_bs ((eq' :: eq'' :: ct' :: vs3, vals3), f)
                  in
                    ((vs4, vals4 @ [(t, ((eq'', ct'), case_vals @
                       [mk_val [eq''] [Pretty.str "Thm.transitive", Pretty.brk 1,
                          Pretty.str "(Thm.combination", Pretty.brk 1,
                          Pretty.str "(Thm.reflexive", Pretty.brk 1,
                          mk_apps "Thm.capply" true (Pretty.str ctcase)
                            (map Pretty.str xs),
                          Pretty.str ")", Pretty.brk 1, Pretty.str (eq ^ ")"),
                          Pretty.brk 1, Pretty.str eq']]))]), (eq'', ct'))
                  end
              end
          
          | NONE =>
            let
              val b = forall (unint sg fs) us;
              val (q, eqs) = foldl_map
                (mk_simpl_code sg case_tab (not b) fs ts ty_bs thm_bs) ((vs, vals), us);
              val ((vs', vals'), (eqf, ctf)) = if isSome (lookup sg fs f) andalso b
                then (q, ("", ""))
                else mk_simpl_code sg case_tab (not b) fs ts ty_bs thm_bs (q, f);
              val ct = variant vs' "ct";
              val eq = variant (ct :: vs') "eq";
              val ctv = mk_val [ct] [mk_apps "Thm.capply" false
                (Pretty.str ctf) (map (Pretty.str o snd) eqs)];
              fun combp b = mk_apps "Thm.combination" b
                (Pretty.str eqf) (map (Pretty.str o fst) eqs)
            in
              case (lookup sg fs f, b) of
                (NONE, true) =>  (* completely uninterpreted *)
                  if mkeq then ((ct :: eq :: vs', vals' @
                    [(t, ((eq, ct), [ctv, mk_refleq eq ct]))]), (eq, ct))
                  else ((ct :: vs', vals' @ [(t, (("", ct), [ctv]))]), ("", ct))
              | (NONE, false) =>  (* function uninterpreted *)
                  ((eq :: ct :: vs', vals' @
                     [(t, ((eq, ct), [ctv, mk_val [eq] [combp false]]))]), (eq, ct))
              | (SOME (s, _, _), true) =>  (* arguments uninterpreted *)
                  ((eq :: ct :: vs', vals' @
                     [(t, ((eq, ct), [mk_val [ct, eq] (separate (Pretty.brk 1)
                       (Pretty.str s :: map (Pretty.str o snd) eqs))]))]), (eq, ct))
              | (SOME (s, _, _), false) =>  (* function and arguments interpreted *)
                  let val eq' = variant (eq :: ct :: vs') "eq"
                  in ((eq' :: eq :: ct :: vs', vals' @ [(t, ((eq', ct),
                    [mk_val [ct, eq] (separate (Pretty.brk 1)
                       (Pretty.str s :: map (Pretty.str o snd) eqs)),
                     mk_val [eq'] [Pretty.str "Thm.transitive", Pretty.brk 1,
                       combp true, Pretty.brk 1, Pretty.str eq]]))]), (eq', ct))
                  end
            end
        end));

fun lhs_of thm = fst (Logic.dest_equals (prop_of thm));
fun rhs_of thm = snd (Logic.dest_equals (prop_of thm));

fun mk_funs_code sg case_tab fs fs' =
  let
    val case_thms = List.mapPartial (fn s => (case Symtab.lookup (case_tab, s) of
        NONE => NONE
      | SOME thms => SOME (unsuffix "_case" (Sign.base_name s) ^ ".cases",
          map (fn i => Sign.base_name s ^ "_" ^ string_of_int i)
            (1 upto length thms) ~~ thms)))
      (Library.foldr add_term_consts (map (prop_of o snd)
        (List.concat (map (#3 o snd) fs')), []));
    val case_vals = map (fn (s, cs) => mk_vall (map fst cs)
      [Pretty.str "map my_mk_meta_eq", Pretty.brk 1,
       Pretty.str ("(thms \"" ^ s ^ "\")")]) case_thms;
    val (vs, thm_bs, thm_vals) = Library.foldl mk_term_bindings (([], [], []),
      List.concat (map (map (apsnd prop_of) o #3 o snd) fs') @
      map (apsnd prop_of) (List.concat (map snd case_thms)));

    fun mk_fun_code (prfx, (fname, d, eqns)) =
      let
        val (f, ts) = strip_comb (lhs_of (snd (hd eqns)));
        val args = variantlist (replicate (length ts) "ct", vs);
        val (vs', ty_bs, ty_vals) = Library.foldl mk_type_bindings
          ((vs @ args, [], []), args ~~ map fastype_of ts);
        val insts1 = map mk_tyinst ty_bs;

        fun mk_eqn_code (name, eqn) =
          let
            val (_, argts) = strip_comb (lhs_of eqn);
            val (vs'', tm_bs, tm_vals) = Library.foldl (decomp_term_code false)
              ((vs', [], []), args ~~ argts);
            val ((vs''', eq_vals), (eq, ct)) = mk_simpl_code sg case_tab false fs
              (tm_bs @ filter_out (is_Var o fst) thm_bs) ty_bs thm_bs
              ((vs'', []), rhs_of eqn);
            val insts2 = map (fn (t, s) => Pretty.block [Pretty.str "(",
              inst_ty false ty_bs t (valOf (assoc (thm_bs, t))), Pretty.str ",", Pretty.brk 1,
              Pretty.str (s ^ ")")]) tm_bs
            val eq' = if null insts1 andalso null insts2 then Pretty.str name
              else parens (eq <> "") [Pretty.str "Thm.instantiate",
                Pretty.brk 1, Pretty.str "(", Pretty.list "[" "]" insts1,
                Pretty.str ",", Pretty.brk 1, Pretty.list "[" "]" insts2,
                Pretty.str ")", Pretty.brk 1, Pretty.str name];
            val eq'' = if eq = "" then eq' else
              Pretty.block [Pretty.str "Thm.transitive", Pretty.brk 1,
                eq', Pretty.brk 1, Pretty.str eq]
          in
            Pretty.block [parens (length argts > 1)
                (Pretty.commas (map (pretty_pattern false) argts)),
              Pretty.str " =>",
              Pretty.brk 1, mk_let "let" 2 (ty_vals @ tm_vals @ List.concat (map (snd o snd) eq_vals))
                [Pretty.str ("(" ^ ct ^ ","), Pretty.brk 1, eq'', Pretty.str ")"]]
          end;

        val default = if d then
            let
              val SOME s = assoc (thm_bs, f);
              val ct = variant vs' "ct"
            in [Pretty.brk 1, Pretty.str "handle", Pretty.brk 1,
              Pretty.str "Match =>", Pretty.brk 1, mk_let "let" 2
                (ty_vals @ (if null (term_tvars f) then [] else
                   [mk_val [s] [inst_ty false ty_bs f s]]) @
                 [mk_val [ct] [mk_apps "Thm.capply" false (Pretty.str s)
                    (map Pretty.str args)]])
                [Pretty.str ("(" ^ ct ^ ","), Pretty.brk 1,
                 Pretty.str "Thm.reflexive", Pretty.brk 1, Pretty.str (ct ^ ")")]]
            end
          else []
      in
        ("and ", Pretty.block (separate (Pretty.brk 1)
            (Pretty.str (prfx ^ fname) :: map Pretty.str args) @
          [Pretty.str " =", Pretty.brk 1, Pretty.str "(case", Pretty.brk 1,
           Pretty.list "(" ")" (map (fn s => Pretty.str ("term_of " ^ s)) args),
           Pretty.str " of", Pretty.brk 1] @
          List.concat (separate [Pretty.brk 1, Pretty.str "| "]
            (map (single o mk_eqn_code) eqns)) @ [Pretty.str ")"] @ default))
      end;

    val (_, decls) = foldl_map mk_fun_code ("fun ", map snd fs')
  in
    mk_let "local" 2 (case_vals @ thm_vals) (separate Pretty.fbrk decls)
  end;

fun mk_simprocs_code sg eqns =
  let
    val case_tab = get_cases sg;
    fun get_head th = head_of (fst (Logic.dest_equals (prop_of th)));
    fun attach_term (x as (_, _, (_, th) :: _)) = (get_head th, x);
    val eqns' = map attach_term eqns;
    fun mk_node (s, _, (_, th) :: _) = (s, get_head th);
    fun mk_edges (s, _, ths) = map (pair s) (distinct
      (List.mapPartial (fn t => Option.map #1 (lookup sg eqns' t))
        (List.concat (map (term_consts' o prop_of o snd) ths))));
    val gr = Library.foldr (uncurry Graph.add_edge)
      (map (pair "" o #1) eqns @ List.concat (map mk_edges eqns),
       Library.foldr (uncurry Graph.new_node)
         (("", Bound 0) :: map mk_node eqns, Graph.empty));
    val keys = rev (Graph.all_succs gr [""] \ "");
    fun gr_ord (x :: _, y :: _) =
      int_ord (find_index (equal x) keys, find_index (equal y) keys);
    val scc = map (fn xs => List.filter (fn (_, (s, _, _)) => s mem xs) eqns')
      (sort gr_ord (Graph.strong_conn gr \ [""]));
  in
    List.concat (separate [Pretty.str ";", Pretty.fbrk, Pretty.str " ", Pretty.fbrk]
      (map (fn eqns'' => [mk_funs_code sg case_tab eqns' eqns'']) scc)) @
    [Pretty.str ";", Pretty.fbrk]
  end;

fun use_simprocs_code sg eqns =
  let
    fun attach_name (i, x) = (i+1, ("simp_thm_" ^ string_of_int i, x));
    fun attach_names (i, (s, b, eqs)) =
      let val (i', eqs') = foldl_map attach_name (i, eqs)
      in (i', (s, b, eqs')) end;
    val (_, eqns') = foldl_map attach_names (1, eqns);
    val (names, thms) = split_list (List.concat (map #3 eqns'));
    val s = setmp print_mode [] Pretty.string_of
      (mk_let "local" 2 [mk_vall names [Pretty.str "!SimprocsCodegen.simp_thms"]]
        (mk_simprocs_code sg eqns'))
  in
    (simp_thms := thms; use_text Context.ml_output false s)
  end;

end;
