(*  Title:      HOL/Tools/inductive_package.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
                Stefan Berghofer,   TU Muenchen
    Copyright   1994  University of Cambridge
                1998  TU Muenchen     

(Co)Inductive Definition module for HOL.

Features:
  * least or greatest fixedpoints
  * user-specified product and sum constructions
  * mutually recursive definitions
  * definitions involving arbitrary monotone operators
  * automatically proves introduction and elimination rules

The recursive sets must *already* be declared as constants in the
current theory!

  Introduction rules have the form
  [| ti:M(Sj), ..., P(x), ... |] ==> t: Sk
  where M is some monotone operator (usually the identity)
  P(x) is any side condition on the free variables
  ti, t are any terms
  Sj, Sk are two of the sets being defined in mutual recursion

Sums are used only for mutual recursion.  Products are used only to
derive "streamlined" induction rules for relations.
*)

signature INDUCTIVE_PACKAGE =
sig
  val quiet_mode: bool ref
  val unify_consts: Sign.sg -> term list -> term list -> term list * term list
  val get_inductive: theory -> string ->
    {names: string list, coind: bool} * {defs: thm list, elims: thm list, raw_induct: thm,
      induct: thm, intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm}
  val print_inductives: theory -> unit
  val mono_add_global: theory attribute
  val mono_del_global: theory attribute
  val get_monos: theory -> thm list
  val add_inductive_i: bool -> bool -> bstring -> bool -> bool -> bool -> term list ->
    theory attribute list -> ((bstring * term) * theory attribute list) list ->
      thm list -> thm list -> theory -> theory *
      {defs: thm list, elims: thm list, raw_induct: thm, induct: thm,
       intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm}
  val add_inductive: bool -> bool -> string list -> Args.src list ->
    ((bstring * string) * Args.src list) list -> (xstring * Args.src list) list ->
      (xstring * Args.src list) list -> theory -> theory *
      {defs: thm list, elims: thm list, raw_induct: thm, induct: thm,
       intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm}
  val inductive_cases: (((bstring * Args.src list) * xstring) * string list) * Comment.text
    -> theory -> theory
  val inductive_cases_i: (((bstring * theory attribute list) * string) * term list) * Comment.text
    -> theory -> theory
  val setup: (theory -> theory) list
end;

structure InductivePackage: INDUCTIVE_PACKAGE =
struct

(*** theory data ***)

(* data kind 'HOL/inductive' *)

type inductive_info =
  {names: string list, coind: bool} * {defs: thm list, elims: thm list, raw_induct: thm,
    induct: thm, intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm};

structure InductiveArgs =
struct
  val name = "HOL/inductive";
  type T = inductive_info Symtab.table * thm list;

  val empty = (Symtab.empty, []);
  val copy = I;
  val prep_ext = I;
  fun merge ((tab1, monos1), (tab2, monos2)) = (Symtab.merge (K true) (tab1, tab2),
    Library.generic_merge Thm.eq_thm I I monos1 monos2);

  fun print sg (tab, monos) =
    (Pretty.writeln (Pretty.strs ("(co)inductives:" ::
       map #1 (Sign.cond_extern_table sg Sign.constK tab)));
     Pretty.writeln (Pretty.big_list "monotonicity rules:" (map Display.pretty_thm monos)));
end;

structure InductiveData = TheoryDataFun(InductiveArgs);
val print_inductives = InductiveData.print;


(* get and put data *)

fun get_inductive thy name =
  (case Symtab.lookup (fst (InductiveData.get thy), name) of
    Some info => info
  | None => error ("Unknown (co)inductive set " ^ quote name));

fun put_inductives names info thy =
  let
    fun upd ((tab, monos), name) = (Symtab.update_new ((name, info), tab), monos);
    val tab_monos = foldl upd (InductiveData.get thy, names)
      handle Symtab.DUP name => error ("Duplicate definition of (co)inductive set " ^ quote name);
  in InductiveData.put tab_monos thy end;



(** monotonicity rules **)

val get_monos = snd o InductiveData.get;
fun put_monos thms thy = InductiveData.put (fst (InductiveData.get thy), thms) thy;

fun mk_mono thm =
  let
    fun eq2mono thm' = [standard (thm' RS (thm' RS eq_to_mono))] @
      (case concl_of thm of
          (_ $ (_ $ (Const ("Not", _) $ _) $ _)) => []
        | _ => [standard (thm' RS (thm' RS eq_to_mono2))]);
    val concl = concl_of thm
  in
    if Logic.is_equals concl then
      eq2mono (thm RS meta_eq_to_obj_eq)
    else if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) concl then
      eq2mono thm
    else [thm]
  end;

(* mono add/del *)

local

fun map_rules_global f thy = put_monos (f (get_monos thy)) thy;

fun add_mono thm rules = Library.gen_union Thm.eq_thm (mk_mono thm, rules);
fun del_mono thm rules = Library.gen_rems Thm.eq_thm (rules, mk_mono thm);

fun mk_att f g (x, thm) = (f (g thm) x, thm);

in

val mono_add_global = mk_att map_rules_global add_mono;
val mono_del_global = mk_att map_rules_global del_mono;

end;


(* concrete syntax *)

val monoN = "mono";
val addN = "add";
val delN = "del";

fun mono_att add del =
  Attrib.syntax (Scan.lift (Args.$$$ addN >> K add || Args.$$$ delN >> K del || Scan.succeed add));

val mono_attr =
  (mono_att mono_add_global mono_del_global, mono_att Attrib.undef_local_attribute Attrib.undef_local_attribute);



(** utilities **)

(* messages *)

val quiet_mode = ref false;
fun message s = if !quiet_mode then () else writeln s;

fun coind_prefix true = "co"
  | coind_prefix false = "";


(* the following code ensures that each recursive set *)
(* always has the same type in all introduction rules *)

fun unify_consts sign cs intr_ts =
  (let
    val {tsig, ...} = Sign.rep_sg sign;
    val add_term_consts_2 =
      foldl_aterms (fn (cs, Const c) => c ins cs | (cs, _) => cs);
    fun varify (t, (i, ts)) =
      let val t' = map_term_types (incr_tvar (i + 1)) (Type.varify (t, []))
      in (maxidx_of_term t', t'::ts) end;
    val (i, cs') = foldr varify (cs, (~1, []));
    val (i', intr_ts') = foldr varify (intr_ts, (i, []));
    val rec_consts = foldl add_term_consts_2 ([], cs');
    val intr_consts = foldl add_term_consts_2 ([], intr_ts');
    fun unify (env, (cname, cT)) =
      let val consts = map snd (filter (fn c => fst c = cname) intr_consts)
      in foldl (fn ((env', j'), Tp) => (Type.unify tsig j' env' Tp))
          (env, (replicate (length consts) cT) ~~ consts)
      end;
    val (env, _) = foldl unify (([], i'), rec_consts);
    fun typ_subst_TVars_2 env T = let val T' = typ_subst_TVars env T
      in if T = T' then T else typ_subst_TVars_2 env T' end;
    val subst = fst o Type.freeze_thaw o
      (map_term_types (typ_subst_TVars_2 env))

  in (map subst cs', map subst intr_ts')
  end) handle Type.TUNIFY =>
    (warning "Occurrences of recursive constant have non-unifiable types"; (cs, intr_ts));


(* misc *)

val Const _ $ (vimage_f $ _) $ _ = HOLogic.dest_Trueprop (concl_of vimageD);

val vimage_name = Sign.intern_const (Theory.sign_of Vimage.thy) "op -``";
val mono_name = Sign.intern_const (Theory.sign_of Ord.thy) "mono";

(* make injections needed in mutually recursive definitions *)

fun mk_inj cs sumT c x =
  let
    fun mk_inj' T n i =
      if n = 1 then x else
      let val n2 = n div 2;
          val Type (_, [T1, T2]) = T
      in
        if i <= n2 then
          Const ("Inl", T1 --> T) $ (mk_inj' T1 n2 i)
        else
          Const ("Inr", T2 --> T) $ (mk_inj' T2 (n - n2) (i - n2))
      end
  in mk_inj' sumT (length cs) (1 + find_index_eq c cs)
  end;

(* make "vimage" terms for selecting out components of mutually rec.def. *)

fun mk_vimage cs sumT t c = if length cs < 2 then t else
  let
    val cT = HOLogic.dest_setT (fastype_of c);
    val vimageT = [cT --> sumT, HOLogic.mk_setT sumT] ---> HOLogic.mk_setT cT
  in
    Const (vimage_name, vimageT) $
      Abs ("y", cT, mk_inj cs sumT c (Bound 0)) $ t
  end;



(** well-formedness checks **)

fun err_in_rule sign t msg = error ("Ill-formed introduction rule\n" ^
  (Sign.string_of_term sign t) ^ "\n" ^ msg);

fun err_in_prem sign t p msg = error ("Ill-formed premise\n" ^
  (Sign.string_of_term sign p) ^ "\nin introduction rule\n" ^
  (Sign.string_of_term sign t) ^ "\n" ^ msg);

val msg1 = "Conclusion of introduction rule must have form\
          \ ' t : S_i '";
val msg2 = "Non-atomic premise";
val msg3 = "Recursion term on left of member symbol";

fun check_rule sign cs r =
  let
    fun check_prem prem = if can HOLogic.dest_Trueprop prem then ()
      else err_in_prem sign r prem msg2;

  in (case HOLogic.dest_Trueprop (Logic.strip_imp_concl r) of
        (Const ("op :", _) $ t $ u) =>
          if u mem cs then
            if exists (Logic.occs o (rpair t)) cs then
              err_in_rule sign r msg3
            else
              seq check_prem (Logic.strip_imp_prems r)
          else err_in_rule sign r msg1
      | _ => err_in_rule sign r msg1)
  end;

fun try' f msg sign t = (case (try f t) of
      Some x => x
    | None => error (msg ^ Sign.string_of_term sign t));



(*** properties of (co)inductive sets ***)

(** elimination rules **)

fun mk_elims cs cTs params intr_ts =
  let
    val used = foldr add_term_names (intr_ts, []);
    val [aname, pname] = variantlist (["a", "P"], used);
    val P = HOLogic.mk_Trueprop (Free (pname, HOLogic.boolT));

    fun dest_intr r =
      let val Const ("op :", _) $ t $ u =
        HOLogic.dest_Trueprop (Logic.strip_imp_concl r)
      in (u, t, Logic.strip_imp_prems r) end;

    val intrs = map dest_intr intr_ts;

    fun mk_elim (c, T) =
      let
        val a = Free (aname, T);

        fun mk_elim_prem (_, t, ts) =
          list_all_free (map dest_Free ((foldr add_term_frees (t::ts, [])) \\ params),
            Logic.list_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (a, t)) :: ts, P));
      in
        Logic.list_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (a, c)) ::
          map mk_elim_prem (filter (equal c o #1) intrs), P)
      end
  in
    map mk_elim (cs ~~ cTs)
  end;
        


(** premises and conclusions of induction rules **)

fun mk_indrule cs cTs params intr_ts =
  let
    val used = foldr add_term_names (intr_ts, []);

    (* predicates for induction rule *)

    val preds = map Free (variantlist (if length cs < 2 then ["P"] else
      map (fn i => "P" ^ string_of_int i) (1 upto length cs), used) ~~
        map (fn T => T --> HOLogic.boolT) cTs);

    (* transform an introduction rule into a premise for induction rule *)

    fun mk_ind_prem r =
      let
        val frees = map dest_Free ((add_term_frees (r, [])) \\ params);

        val pred_of = curry (Library.gen_assoc (op aconv)) (cs ~~ preds);

        fun subst (s as ((m as Const ("op :", T)) $ t $ u)) =
              (case pred_of u of
                  None => (m $ fst (subst t) $ fst (subst u), None)
                | Some P => (HOLogic.conj $ s $ (P $ t), Some (s, P $ t)))
          | subst s =
              (case pred_of s of
                  Some P => (HOLogic.mk_binop "op Int"
                    (s, HOLogic.Collect_const (HOLogic.dest_setT
                      (fastype_of s)) $ P), None)
                | None => (case s of
                     (t $ u) => (fst (subst t) $ fst (subst u), None)
                   | (Abs (a, T, t)) => (Abs (a, T, fst (subst t)), None)
                   | _ => (s, None)));

        fun mk_prem (s, prems) = (case subst s of
              (_, Some (t, u)) => t :: u :: prems
            | (t, _) => t :: prems);
          
        val Const ("op :", _) $ t $ u =
          HOLogic.dest_Trueprop (Logic.strip_imp_concl r)

      in list_all_free (frees,
           Logic.list_implies (map HOLogic.mk_Trueprop (foldr mk_prem
             (map HOLogic.dest_Trueprop (Logic.strip_imp_prems r), [])),
               HOLogic.mk_Trueprop (the (pred_of u) $ t)))
      end;

    val ind_prems = map mk_ind_prem intr_ts;

    (* make conclusions for induction rules *)

    fun mk_ind_concl ((c, P), (ts, x)) =
      let val T = HOLogic.dest_setT (fastype_of c);
          val Ts = HOLogic.prodT_factors T;
          val (frees, x') = foldr (fn (T', (fs, s)) =>
            ((Free (s, T'))::fs, bump_string s)) (Ts, ([], x));
          val tuple = HOLogic.mk_tuple T frees;
      in ((HOLogic.mk_binop "op -->"
        (HOLogic.mk_mem (tuple, c), P $ tuple))::ts, x')
      end;

    val mutual_ind_concl = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (fst (foldr mk_ind_concl (cs ~~ preds, ([], "xa")))))

  in (preds, ind_prems, mutual_ind_concl)
  end;



(** prepare cases and induct rules **)

(*
  transform mutual rule:
    HH ==> (x1:A1 --> P1 x1) & ... & (xn:An --> Pn xn)
  into i-th projection:
    xi:Ai ==> HH ==> Pi xi
*)

fun project_rules [name] rule = [(name, rule)]
  | project_rules names mutual_rule =
      let
        val n = length names;
        fun proj i =
          (if i < n then (fn th => th RS conjunct1) else I)
            (Library.funpow (i - 1) (fn th => th RS conjunct2) mutual_rule)
            RS mp |> Thm.permute_prems 0 ~1 |> Drule.standard;
      in names ~~ map proj (1 upto n) end;

fun add_cases_induct no_elim no_ind names elims induct =
  let
    val cases_specs =
      if no_elim then []
      else map2 (fn (name, elim) => (("", elim), [InductMethod.cases_set_global name]))
        (names, elims);

    val induct_specs =
      if no_ind then []
      else map (fn (name, th) => (("", th), [InductMethod.induct_set_global name]))
        (project_rules names induct);
  in PureThy.add_thms (cases_specs @ induct_specs) end;



(*** proofs for (co)inductive sets ***)

(** prove monotonicity **)

fun prove_mono setT fp_fun monos thy =
  let
    val _ = message "  Proving monotonicity ...";

    val mono = prove_goalw_cterm [] (cterm_of (Theory.sign_of thy) (HOLogic.mk_Trueprop
      (Const (mono_name, (setT --> setT) --> HOLogic.boolT) $ fp_fun)))
        (fn _ => [rtac monoI 1, REPEAT (ares_tac (get_monos thy @ flat (map mk_mono monos)) 1)])

  in mono end;



(** prove introduction rules **)

fun prove_intrs coind mono fp_def intr_ts con_defs rec_sets_defs thy =
  let
    val _ = message "  Proving the introduction rules ...";

    val unfold = standard (mono RS (fp_def RS
      (if coind then def_gfp_Tarski else def_lfp_Tarski)));

    fun select_disj 1 1 = []
      | select_disj _ 1 = [rtac disjI1]
      | select_disj n i = (rtac disjI2)::(select_disj (n - 1) (i - 1));

    val intrs = map (fn (i, intr) => prove_goalw_cterm rec_sets_defs
      (cterm_of (Theory.sign_of thy) intr) (fn prems =>
       [(*insert prems and underlying sets*)
       cut_facts_tac prems 1,
       stac unfold 1,
       REPEAT (resolve_tac [vimageI2, CollectI] 1),
       (*Now 1-2 subgoals: the disjunction, perhaps equality.*)
       EVERY1 (select_disj (length intr_ts) i),
       (*Not ares_tac, since refl must be tried before any equality assumptions;
         backtracking may occur if the premises have extra variables!*)
       DEPTH_SOLVE_1 (resolve_tac [refl,exI,conjI] 1 APPEND assume_tac 1),
       (*Now solve the equations like Inl 0 = Inl ?b2*)
       rewrite_goals_tac con_defs,
       REPEAT (rtac refl 1)])) (1 upto (length intr_ts) ~~ intr_ts)

  in (intrs, unfold) end;



(** prove elimination rules **)

fun prove_elims cs cTs params intr_ts unfold rec_sets_defs thy =
  let
    val _ = message "  Proving the elimination rules ...";

    val rules1 = [CollectE, disjE, make_elim vimageD, exE];
    val rules2 = [conjE, Inl_neq_Inr, Inr_neq_Inl] @
      map make_elim [Inl_inject, Inr_inject];

    val elims = map (fn t => prove_goalw_cterm rec_sets_defs
      (cterm_of (Theory.sign_of thy) t) (fn prems =>
        [cut_facts_tac [hd prems] 1,
         dtac (unfold RS subst) 1,
         REPEAT (FIRSTGOAL (eresolve_tac rules1)),
         REPEAT (FIRSTGOAL (eresolve_tac rules2)),
         EVERY (map (fn prem =>
           DEPTH_SOLVE_1 (ares_tac [prem, conjI] 1)) (tl prems))]))
      (mk_elims cs cTs params intr_ts)

  in elims end;


(** derivation of simplified elimination rules **)

(*Applies freeness of the given constructors, which *must* be unfolded by
  the given defs.  Cannot simply use the local con_defs because con_defs=[] 
  for inference systems.
 *)

(*cprop should have the form t:Si where Si is an inductive set*)
fun mk_cases_i solved elims ss cprop =
  let
    val prem = Thm.assume cprop;
    val tac = if solved then InductMethod.con_elim_solved_tac else InductMethod.con_elim_tac;
    fun mk_elim rl = Drule.standard (Tactic.rule_by_tactic (tac ss) (prem RS rl));
  in
    (case get_first (try mk_elim) elims of
      Some r => r
    | None => error (Pretty.string_of (Pretty.block
        [Pretty.str "mk_cases: proposition not of form 't : S_i'", Pretty.fbrk,
          Display.pretty_cterm cprop])))
  end;

fun mk_cases elims s =
  mk_cases_i false elims (simpset()) (Thm.read_cterm (Thm.sign_of_thm (hd elims)) (s, propT));


(* inductive_cases(_i) *)

fun gen_inductive_cases prep_att prep_const prep_prop
    ((((name, raw_atts), raw_set), raw_props), comment) thy =
  let
    val sign = Theory.sign_of thy;

    val atts = map (prep_att thy) raw_atts;
    val (_, {elims, ...}) = get_inductive thy (prep_const sign raw_set);
    val cprops = map (Thm.cterm_of sign o prep_prop (ProofContext.init thy)) raw_props;
    val thms = map (mk_cases_i true elims (Simplifier.simpset_of thy)) cprops;
  in
    thy
    |> IsarThy.have_theorems_i (((name, atts), map Thm.no_attributes thms), comment)
  end;

val inductive_cases =
  gen_inductive_cases Attrib.global_attribute Sign.intern_const ProofContext.read_prop;

val inductive_cases_i = gen_inductive_cases (K I) (K I) ProofContext.cert_prop;



(** prove induction rule **)

fun prove_indrule cs cTs sumT rec_const params intr_ts mono
    fp_def rec_sets_defs thy =
  let
    val _ = message "  Proving the induction rule ...";

    val sign = Theory.sign_of thy;

    val sum_case_rewrites = (case ThyInfo.lookup_theory "Datatype" of
        None => []
      | Some thy' => map mk_meta_eq (PureThy.get_thms thy' "sum.cases"));

    val (preds, ind_prems, mutual_ind_concl) = mk_indrule cs cTs params intr_ts;

    (* make predicate for instantiation of abstract induction rule *)

    fun mk_ind_pred _ [P] = P
      | mk_ind_pred T Ps =
         let val n = (length Ps) div 2;
             val Type (_, [T1, T2]) = T
         in Const ("Datatype.sum.sum_case",
           [T1 --> HOLogic.boolT, T2 --> HOLogic.boolT, T] ---> HOLogic.boolT) $
             mk_ind_pred T1 (take (n, Ps)) $ mk_ind_pred T2 (drop (n, Ps))
         end;

    val ind_pred = mk_ind_pred sumT preds;

    val ind_concl = HOLogic.mk_Trueprop
      (HOLogic.all_const sumT $ Abs ("x", sumT, HOLogic.mk_binop "op -->"
        (HOLogic.mk_mem (Bound 0, rec_const), ind_pred $ Bound 0)));

    (* simplification rules for vimage and Collect *)

    val vimage_simps = if length cs < 2 then [] else
      map (fn c => prove_goalw_cterm [] (cterm_of sign
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (mk_vimage cs sumT (HOLogic.Collect_const sumT $ ind_pred) c,
           HOLogic.Collect_const (HOLogic.dest_setT (fastype_of c)) $
             nth_elem (find_index_eq c cs, preds)))))
        (fn _ => [rtac vimage_Collect 1, rewrite_goals_tac sum_case_rewrites,
          rtac refl 1])) cs;

    val induct = prove_goalw_cterm [] (cterm_of sign
      (Logic.list_implies (ind_prems, ind_concl))) (fn prems =>
        [rtac (impI RS allI) 1,
         DETERM (etac (mono RS (fp_def RS def_induct)) 1),
         rewrite_goals_tac (map mk_meta_eq (vimage_Int::Int_Collect::vimage_simps)),
         fold_goals_tac rec_sets_defs,
         (*This CollectE and disjE separates out the introduction rules*)
         REPEAT (FIRSTGOAL (eresolve_tac [CollectE, disjE, exE])),
         (*Now break down the individual cases.  No disjE here in case
           some premise involves disjunction.*)
         REPEAT (FIRSTGOAL (etac conjE ORELSE' hyp_subst_tac)),
         rewrite_goals_tac sum_case_rewrites,
         EVERY (map (fn prem =>
           DEPTH_SOLVE_1 (ares_tac [prem, conjI, refl] 1)) prems)]);

    val lemma = prove_goalw_cterm rec_sets_defs (cterm_of sign
      (Logic.mk_implies (ind_concl, mutual_ind_concl))) (fn prems =>
        [cut_facts_tac prems 1,
         REPEAT (EVERY
           [REPEAT (resolve_tac [conjI, impI] 1),
            TRY (dtac vimageD 1), etac allE 1, dtac mp 1, atac 1,
            rewrite_goals_tac sum_case_rewrites,
            atac 1])])

  in standard (split_rule (induct RS lemma))
  end;



(*** specification of (co)inductive sets ****)

(** definitional introduction of (co)inductive sets **)

fun add_ind_def verbose declare_consts alt_name coind no_elim no_ind cs
    atts intros monos con_defs thy params paramTs cTs cnames =
  let
    val _ = if verbose then message ("Proofs for " ^ coind_prefix coind ^ "inductive set(s) " ^
      commas_quote cnames) else ();

    val sumT = fold_bal (fn (T, U) => Type ("+", [T, U])) cTs;
    val setT = HOLogic.mk_setT sumT;

    val fp_name = if coind then Sign.intern_const (Theory.sign_of Gfp.thy) "gfp"
      else Sign.intern_const (Theory.sign_of Lfp.thy) "lfp";

    val ((intr_names, intr_ts), intr_atts) = apfst split_list (split_list intros);

    val used = foldr add_term_names (intr_ts, []);
    val [sname, xname] = variantlist (["S", "x"], used);

    (* transform an introduction rule into a conjunction  *)
    (*   [| t : ... S_i ... ; ... |] ==> u : S_j          *)
    (* is transformed into                                *)
    (*   x = Inj_j u & t : ... Inj_i -`` S ... & ...      *)

    fun transform_rule r =
      let
        val frees = map dest_Free ((add_term_frees (r, [])) \\ params);
        val subst = subst_free
          (cs ~~ (map (mk_vimage cs sumT (Free (sname, setT))) cs));
        val Const ("op :", _) $ t $ u =
          HOLogic.dest_Trueprop (Logic.strip_imp_concl r)

      in foldr (fn ((x, T), P) => HOLogic.mk_exists (x, T, P))
        (frees, foldr1 HOLogic.mk_conj
          (((HOLogic.eq_const sumT) $ Free (xname, sumT) $ (mk_inj cs sumT u t))::
            (map (subst o HOLogic.dest_Trueprop)
              (Logic.strip_imp_prems r))))
      end

    (* make a disjunction of all introduction rules *)

    val fp_fun = absfree (sname, setT, (HOLogic.Collect_const sumT) $
      absfree (xname, sumT, foldr1 HOLogic.mk_disj (map transform_rule intr_ts)));

    (* add definiton of recursive sets to theory *)

    val rec_name = if alt_name = "" then space_implode "_" cnames else alt_name;
    val full_rec_name = Sign.full_name (Theory.sign_of thy) rec_name;

    val rec_const = list_comb
      (Const (full_rec_name, paramTs ---> setT), params);

    val fp_def_term = Logic.mk_equals (rec_const,
      Const (fp_name, (setT --> setT) --> setT) $ fp_fun)

    val def_terms = fp_def_term :: (if length cs < 2 then [] else
      map (fn c => Logic.mk_equals (c, mk_vimage cs sumT rec_const c)) cs);

    val thy' = thy |>
      (if declare_consts then
        Theory.add_consts_i (map (fn (c, n) =>
          (n, paramTs ---> fastype_of c, NoSyn)) (cs ~~ cnames))
       else I) |>
      (if length cs < 2 then I else
       Theory.add_consts_i [(rec_name, paramTs ---> setT, NoSyn)]) |>
      Theory.add_path rec_name |>
      PureThy.add_defss_i [(("defs", def_terms), [])];

    (* get definitions from theory *)

    val fp_def::rec_sets_defs = PureThy.get_thms thy' "defs";

    (* prove and store theorems *)

    val mono = prove_mono setT fp_fun monos thy';
    val (intrs, unfold) = prove_intrs coind mono fp_def intr_ts con_defs
      rec_sets_defs thy';
    val elims = if no_elim then [] else
      prove_elims cs cTs params intr_ts unfold rec_sets_defs thy';
    val raw_induct = if no_ind then Drule.asm_rl else
      if coind then standard (rule_by_tactic
        (rewrite_tac [mk_meta_eq vimage_Un] THEN
          fold_tac rec_sets_defs) (mono RS (fp_def RS def_Collect_coinduct)))
      else
        prove_indrule cs cTs sumT rec_const params intr_ts mono fp_def
          rec_sets_defs thy';
    val induct = if coind orelse no_ind orelse length cs > 1 then raw_induct
      else standard (raw_induct RSN (2, rev_mp));

    val thy'' = thy'
      |> PureThy.add_thmss [(("intrs", intrs), atts)]
      |> PureThy.add_thms ((intr_names ~~ intrs) ~~ intr_atts)
      |> (if no_elim then I else PureThy.add_thmss [(("elims", elims), [])])
      |> (if no_ind then I else PureThy.add_thms
        [((coind_prefix coind ^ "induct", induct), [])])
      |> Theory.parent_path;
    val intrs' = PureThy.get_thms thy'' "intrs";
    val elims' = if no_elim then elims else PureThy.get_thms thy'' "elims";  (* FIXME improve *)
    val induct' = if no_ind then induct else PureThy.get_thm thy'' (coind_prefix coind ^ "induct");  (* FIXME improve *)
  in (thy'',
    {defs = fp_def::rec_sets_defs,
     mono = mono,
     unfold = unfold,
     intrs = intrs',
     elims = elims',
     mk_cases = mk_cases elims',
     raw_induct = raw_induct,
     induct = induct'})
  end;



(** axiomatic introduction of (co)inductive sets **)

fun add_ind_axm verbose declare_consts alt_name coind no_elim no_ind cs
    atts intros monos con_defs thy params paramTs cTs cnames =
  let
    val rec_name = if alt_name = "" then space_implode "_" cnames else alt_name;

    val ((intr_names, intr_ts), intr_atts) = apfst split_list (split_list intros);
    val elim_ts = mk_elims cs cTs params intr_ts;

    val (_, ind_prems, mutual_ind_concl) = mk_indrule cs cTs params intr_ts;
    val ind_t = Logic.list_implies (ind_prems, mutual_ind_concl);
    
    val thy' = thy
      |> (if declare_consts then
            Theory.add_consts_i
              (map (fn (c, n) => (n, paramTs ---> fastype_of c, NoSyn)) (cs ~~ cnames))
         else I)
      |> Theory.add_path rec_name
      |> PureThy.add_axiomss_i [(("intrs", intr_ts), atts), (("elims", elim_ts), [])]
      |> (if coind then I else
            PureThy.add_axioms_i [(("raw_induct", ind_t), [apsnd (standard o split_rule)])]);

    val intrs = PureThy.get_thms thy' "intrs";
    val elims = PureThy.get_thms thy' "elims";
    val raw_induct = if coind then Drule.asm_rl else PureThy.get_thm thy' "raw_induct";
    val induct = if coind orelse length cs > 1 then raw_induct
      else standard (raw_induct RSN (2, rev_mp));

    val thy'' =
      thy'
      |> (if coind then I else PureThy.add_thms [(("induct", induct), [])])
      |> PureThy.add_thms ((intr_names ~~ intrs) ~~ intr_atts)
      |> Theory.parent_path;
    val induct' = if coind then raw_induct else PureThy.get_thm thy'' "induct";
  in (thy'',
    {defs = [],
     mono = Drule.asm_rl,
     unfold = Drule.asm_rl,
     intrs = intrs,
     elims = elims,
     mk_cases = mk_cases elims,
     raw_induct = raw_induct,
     induct = induct'})
  end;



(** introduction of (co)inductive sets **)

fun add_inductive_i verbose declare_consts alt_name coind no_elim no_ind cs
    atts intros monos con_defs thy =
  let
    val _ = Theory.requires thy "Inductive" (coind_prefix coind ^ "inductive definitions");
    val sign = Theory.sign_of thy;

    (*parameters should agree for all mutually recursive components*)
    val (_, params) = strip_comb (hd cs);
    val paramTs = map (try' (snd o dest_Free) "Parameter in recursive\
      \ component is not a free variable: " sign) params;

    val cTs = map (try' (HOLogic.dest_setT o fastype_of)
      "Recursive component not of type set: " sign) cs;

    val full_cnames = map (try' (fst o dest_Const o head_of)
      "Recursive set not previously declared as constant: " sign) cs;
    val cnames = map Sign.base_name full_cnames;

    val _ = seq (check_rule sign cs o snd o fst) intros;

    val (thy1, result) =
      (if ! quick_and_dirty then add_ind_axm else add_ind_def)
        verbose declare_consts alt_name coind no_elim no_ind cs atts intros monos
        con_defs thy params paramTs cTs cnames;
    val thy2 = thy1
      |> put_inductives full_cnames ({names = full_cnames, coind = coind}, result)
      |> add_cases_induct no_elim no_ind full_cnames (#elims result) (#induct result);
  in (thy2, result) end;



(** external interface **)

fun add_inductive verbose coind c_strings srcs intro_srcs raw_monos raw_con_defs thy =
  let
    val sign = Theory.sign_of thy;
    val cs = map (term_of o Thm.read_cterm sign o rpair HOLogic.termT) c_strings;

    val atts = map (Attrib.global_attribute thy) srcs;
    val intr_names = map (fst o fst) intro_srcs;
    val intr_ts = map (term_of o Thm.read_cterm sign o rpair propT o snd o fst) intro_srcs;
    val intr_atts = map (map (Attrib.global_attribute thy) o snd) intro_srcs;
    val (cs', intr_ts') = unify_consts sign cs intr_ts;

    val ((thy', con_defs), monos) = thy
      |> IsarThy.apply_theorems raw_monos
      |> apfst (IsarThy.apply_theorems raw_con_defs);
  in
    add_inductive_i verbose false "" coind false false cs'
      atts ((intr_names ~~ intr_ts') ~~ intr_atts) monos con_defs thy'
  end;



(** package setup **)

(* setup theory *)

val setup = [InductiveData.init,
             Attrib.add_attributes [(monoN, mono_attr, "monotonicity rule")]];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

fun mk_ind coind (((sets, (atts, intrs)), monos), con_defs) =
  #1 o add_inductive true coind sets atts (map P.triple_swap intrs) monos con_defs;

fun ind_decl coind =
  (Scan.repeat1 P.term --| P.marg_comment) --
  (P.$$$ "intrs" |--
    P.!!! (P.opt_attribs -- Scan.repeat1 (P.opt_thm_name ":" -- P.prop --| P.marg_comment))) --
  Scan.optional (P.$$$ "monos" |-- P.!!! P.xthms1 --| P.marg_comment) [] --
  Scan.optional (P.$$$ "con_defs" |-- P.!!! P.xthms1 --| P.marg_comment) []
  >> (Toplevel.theory o mk_ind coind);

val inductiveP =
  OuterSyntax.command "inductive" "define inductive sets" K.thy_decl (ind_decl false);

val coinductiveP =
  OuterSyntax.command "coinductive" "define coinductive sets" K.thy_decl (ind_decl true);


val ind_cases =
  P.opt_thm_name "=" -- P.xname --| P.$$$ ":" -- Scan.repeat1 P.prop -- P.marg_comment
  >> (Toplevel.theory o inductive_cases);

val inductive_casesP =
  OuterSyntax.command "inductive_cases" "create simplified instances of elimination rules"
    K.thy_decl ind_cases;

val _ = OuterSyntax.add_keywords ["intrs", "monos", "con_defs"];
val _ = OuterSyntax.add_parsers [inductiveP, coinductiveP, inductive_casesP];

end;


end;
