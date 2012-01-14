(*  Title:      HOL/Tools/inductive.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

(Co)Inductive Definition module for HOL.

Features:
  * least or greatest fixedpoints
  * mutually recursive definitions
  * definitions involving arbitrary monotone operators
  * automatically proves introduction and elimination rules

  Introduction rules have the form
  [| M Pj ti, ..., Q x, ... |] ==> Pk t
  where M is some monotone operator (usually the identity)
  Q x is any side condition on the free variables
  ti, t are any terms
  Pj, Pk are two of the predicates being defined in mutual recursion
*)

signature BASIC_INDUCTIVE =
sig
  type inductive_result =
    {preds: term list, elims: thm list, raw_induct: thm,
     induct: thm, inducts: thm list, intrs: thm list, eqs: thm list}
  val transform_result: morphism -> inductive_result -> inductive_result
  type inductive_info = {names: string list, coind: bool} * inductive_result
  val the_inductive: Proof.context -> string -> inductive_info
  val print_inductives: Proof.context -> unit
  val get_monos: Proof.context -> thm list
  val mono_add: attribute
  val mono_del: attribute
  val mk_cases: Proof.context -> term -> thm
  val inductive_forall_def: thm
  val rulify: thm -> thm
  val inductive_cases: (Attrib.binding * string list) list -> local_theory ->
    thm list list * local_theory
  val inductive_cases_i: (Attrib.binding * term list) list -> local_theory ->
    thm list list * local_theory
  type inductive_flags =
    {quiet_mode: bool, verbose: bool, alt_name: binding, coind: bool,
      no_elim: bool, no_ind: bool, skip_mono: bool, fork_mono: bool}
  val add_inductive_i:
    inductive_flags -> ((binding * typ) * mixfix) list ->
    (string * typ) list -> (Attrib.binding * term) list -> thm list -> local_theory ->
    inductive_result * local_theory
  val add_inductive: bool -> bool ->
    (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list ->
    (Attrib.binding * string) list ->
    (Facts.ref * Attrib.src list) list ->
    bool -> local_theory -> inductive_result * local_theory
  val add_inductive_global: inductive_flags ->
    ((binding * typ) * mixfix) list -> (string * typ) list -> (Attrib.binding * term) list ->
    thm list -> theory -> inductive_result * theory
  val arities_of: thm -> (string * int) list
  val params_of: thm -> term list
  val partition_rules: thm -> thm list -> (string * thm list) list
  val partition_rules': thm -> (thm * 'a) list -> (string * (thm * 'a) list) list
  val unpartition_rules: thm list -> (string * 'a list) list -> 'a list
  val infer_intro_vars: thm -> int -> thm list -> term list list
  val setup: theory -> theory
end;

signature INDUCTIVE =
sig
  include BASIC_INDUCTIVE
  type add_ind_def =
    inductive_flags ->
    term list -> (Attrib.binding * term) list -> thm list ->
    term list -> (binding * mixfix) list ->
    local_theory -> inductive_result * local_theory
  val declare_rules: binding -> bool -> bool -> string list -> term list ->
    thm list -> binding list -> Attrib.src list list -> (thm * string list * int) list ->
    thm list -> thm -> local_theory -> thm list * thm list * thm list * thm * thm list * local_theory
  val add_ind_def: add_ind_def
  val gen_add_inductive_i: add_ind_def -> inductive_flags ->
    ((binding * typ) * mixfix) list -> (string * typ) list -> (Attrib.binding * term) list ->
    thm list -> local_theory -> inductive_result * local_theory
  val gen_add_inductive: add_ind_def -> bool -> bool ->
    (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> (Facts.ref * Attrib.src list) list ->
    bool -> local_theory -> inductive_result * local_theory
  val gen_ind_decl: add_ind_def -> bool -> (bool -> local_theory -> local_theory) parser
end;

structure Inductive: INDUCTIVE =
struct

(** theory context references **)

val inductive_forall_def = @{thm induct_forall_def};
val inductive_conj_name = "HOL.induct_conj";
val inductive_conj_def = @{thm induct_conj_def};
val inductive_conj = @{thms induct_conj};
val inductive_atomize = @{thms induct_atomize};
val inductive_rulify = @{thms induct_rulify};
val inductive_rulify_fallback = @{thms induct_rulify_fallback};

val simp_thms1 =
  map mk_meta_eq
    @{lemma "(~ True) = False" "(~ False) = True"
        "(True --> P) = P" "(False --> P) = True"
        "(P & True) = P" "(True & P) = P"
      by (fact simp_thms)+};

val simp_thms2 =
  map mk_meta_eq [@{thm inf_fun_def}, @{thm inf_bool_def}] @ simp_thms1;

val simp_thms3 =
  map mk_meta_eq [@{thm le_fun_def}, @{thm le_bool_def}, @{thm sup_fun_def}, @{thm sup_bool_def}];



(** misc utilities **)

fun message quiet_mode s = if quiet_mode then () else writeln s;
fun clean_message quiet_mode s = if ! quick_and_dirty then () else message quiet_mode s;

fun coind_prefix true = "co"
  | coind_prefix false = "";

fun log (b: int) m n = if m >= n then 0 else 1 + log b (b * m) n;

fun make_bool_args f g [] i = []
  | make_bool_args f g (x :: xs) i =
      (if i mod 2 = 0 then f x else g x) :: make_bool_args f g xs (i div 2);

fun make_bool_args' xs =
  make_bool_args (K @{term False}) (K @{term True}) xs;

fun arg_types_of k c = drop k (binder_types (fastype_of c));

fun find_arg T x [] = raise Fail "find_arg"
  | find_arg T x ((p as (_, (SOME _, _))) :: ps) =
      apsnd (cons p) (find_arg T x ps)
  | find_arg T x ((p as (U, (NONE, y))) :: ps) =
      if (T: typ) = U then (y, (U, (SOME x, y)) :: ps)
      else apsnd (cons p) (find_arg T x ps);

fun make_args Ts xs =
  map (fn (T, (NONE, ())) => Const (@{const_name undefined}, T) | (_, (SOME t, ())) => t)
    (fold (fn (t, T) => snd o find_arg T t) xs (map (rpair (NONE, ())) Ts));

fun make_args' Ts xs Us =
  fst (fold_map (fn T => find_arg T ()) Us (Ts ~~ map (pair NONE) xs));

fun dest_predicate cs params t =
  let
    val k = length params;
    val (c, ts) = strip_comb t;
    val (xs, ys) = chop k ts;
    val i = find_index (fn c' => c' = c) cs;
  in
    if xs = params andalso i >= 0 then
      SOME (c, i, ys, chop (length ys) (arg_types_of k c))
    else NONE
  end;

fun mk_names a 0 = []
  | mk_names a 1 = [a]
  | mk_names a n = map (fn i => a ^ string_of_int i) (1 upto n);

fun select_disj 1 1 = []
  | select_disj _ 1 = [rtac disjI1]
  | select_disj n i = rtac disjI2 :: select_disj (n - 1) (i - 1);



(** context data **)

type inductive_result =
  {preds: term list, elims: thm list, raw_induct: thm,
   induct: thm, inducts: thm list, intrs: thm list, eqs: thm list};

fun transform_result phi {preds, elims, raw_induct: thm, induct, inducts, intrs, eqs} =
  let
    val term = Morphism.term phi;
    val thm = Morphism.thm phi;
    val fact = Morphism.fact phi;
  in
   {preds = map term preds, elims = fact elims, raw_induct = thm raw_induct,
    induct = thm induct, inducts = fact inducts, intrs = fact intrs, eqs = fact eqs}
  end;

type inductive_info = {names: string list, coind: bool} * inductive_result;

val empty_equations =
  Item_Net.init Thm.eq_thm_prop
    (single o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of);

datatype data = Data of
 {infos: inductive_info Symtab.table,
  monos: thm list,
  equations: thm Item_Net.T};

fun make_data (infos, monos, equations) =
  Data {infos = infos, monos = monos, equations = equations};

structure Data = Generic_Data
(
  type T = data;
  val empty = make_data (Symtab.empty, [], empty_equations);
  val extend = I;
  fun merge (Data {infos = infos1, monos = monos1, equations = equations1},
      Data {infos = infos2, monos = monos2, equations = equations2}) =
    make_data (Symtab.merge (K true) (infos1, infos2),
      Thm.merge_thms (monos1, monos2),
      Item_Net.merge (equations1, equations2));
);

fun map_data f =
  Data.map (fn Data {infos, monos, equations} => make_data (f (infos, monos, equations)));

fun rep_data ctxt = Data.get (Context.Proof ctxt) |> (fn Data rep => rep);

fun print_inductives ctxt =
  let
    val {infos, monos, ...} = rep_data ctxt;
    val space = Consts.space_of (Proof_Context.consts_of ctxt);
  in
    [Pretty.strs ("(co)inductives:" :: map #1 (Name_Space.extern_table ctxt (space, infos))),
     Pretty.big_list "monotonicity rules:" (map (Display.pretty_thm ctxt) monos)]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* inductive info *)

fun the_inductive ctxt name =
  (case Symtab.lookup (#infos (rep_data ctxt)) name of
    NONE => error ("Unknown (co)inductive predicate " ^ quote name)
  | SOME info => info);

fun put_inductives names info =
  map_data (fn (infos, monos, equations) =>
    (fold (fn name => Symtab.update (name, info)) names infos, monos, equations));


(* monotonicity rules *)

val get_monos = #monos o rep_data;

fun mk_mono ctxt thm =
  let
    fun eq_to_mono thm' = thm' RS (thm' RS @{thm eq_to_mono});
    fun dest_less_concl thm = dest_less_concl (thm RS @{thm le_funD})
      handle THM _ => thm RS @{thm le_boolD}
  in
    (case concl_of thm of
      Const ("==", _) $ _ $ _ => eq_to_mono (thm RS meta_eq_to_obj_eq)
    | _ $ (Const (@{const_name HOL.eq}, _) $ _ $ _) => eq_to_mono thm
    | _ $ (Const (@{const_name Orderings.less_eq}, _) $ _ $ _) =>
      dest_less_concl (Seq.hd (REPEAT (FIRSTGOAL
        (resolve_tac [@{thm le_funI}, @{thm le_boolI'}])) thm))
    | _ => thm)
  end handle THM _ => error ("Bad monotonicity theorem:\n" ^ Display.string_of_thm ctxt thm);

val mono_add =
  Thm.declaration_attribute (fn thm => fn context =>
    map_data (fn (infos, monos, equations) =>
      (infos, Thm.add_thm (mk_mono (Context.proof_of context) thm) monos, equations)) context);

val mono_del =
  Thm.declaration_attribute (fn thm => fn context =>
    map_data (fn (infos, monos, equations) =>
      (infos, Thm.del_thm (mk_mono (Context.proof_of context) thm) monos, equations)) context);


(* equations *)

val get_equations = #equations o rep_data;

val equation_add_permissive =
  Thm.declaration_attribute (fn thm =>
    map_data (fn (infos, monos, equations) =>
      (infos, monos, perhaps (try (Item_Net.update thm)) equations)));



(** process rules **)

local

fun err_in_rule ctxt name t msg =
  error (cat_lines ["Ill-formed introduction rule " ^ Binding.print name,
    Syntax.string_of_term ctxt t, msg]);

fun err_in_prem ctxt name t p msg =
  error (cat_lines ["Ill-formed premise", Syntax.string_of_term ctxt p,
    "in introduction rule " ^ Binding.print name, Syntax.string_of_term ctxt t, msg]);

val bad_concl = "Conclusion of introduction rule must be an inductive predicate";

val bad_ind_occ = "Inductive predicate occurs in argument of inductive predicate";

val bad_app = "Inductive predicate must be applied to parameter(s) ";

fun atomize_term thy = Raw_Simplifier.rewrite_term thy inductive_atomize [];

in

fun check_rule ctxt cs params ((binding, att), rule) =
  let
    val params' = Term.variant_frees rule (Logic.strip_params rule);
    val frees = rev (map Free params');
    val concl = subst_bounds (frees, Logic.strip_assums_concl rule);
    val prems = map (curry subst_bounds frees) (Logic.strip_assums_hyp rule);
    val rule' = Logic.list_implies (prems, concl);
    val aprems = map (atomize_term (Proof_Context.theory_of ctxt)) prems;
    val arule = fold_rev (Logic.all o Free) params' (Logic.list_implies (aprems, concl));

    fun check_ind err t =
      (case dest_predicate cs params t of
        NONE => err (bad_app ^
          commas (map (Syntax.string_of_term ctxt) params))
      | SOME (_, _, ys, _) =>
          if exists (fn c => exists (fn t => Logic.occs (c, t)) ys) cs
          then err bad_ind_occ else ());

    fun check_prem' prem t =
      if member (op =) cs (head_of t) then
        check_ind (err_in_prem ctxt binding rule prem) t
      else
        (case t of
          Abs (_, _, t) => check_prem' prem t
        | t $ u => (check_prem' prem t; check_prem' prem u)
        | _ => ());

    fun check_prem (prem, aprem) =
      if can HOLogic.dest_Trueprop aprem then check_prem' prem prem
      else err_in_prem ctxt binding rule prem "Non-atomic premise";

    val _ =
      (case concl of
        Const (@{const_name Trueprop}, _) $ t =>
          if member (op =) cs (head_of t) then
           (check_ind (err_in_rule ctxt binding rule') t;
            List.app check_prem (prems ~~ aprems))
          else err_in_rule ctxt binding rule' bad_concl
       | _ => err_in_rule ctxt binding rule' bad_concl);
  in
    ((binding, att), arule)
  end;

val rulify =
  hol_simplify inductive_conj
  #> hol_simplify inductive_rulify
  #> hol_simplify inductive_rulify_fallback
  #> Simplifier.norm_hhf;

end;



(** proofs for (co)inductive predicates **)

(* prove monotonicity *)

fun prove_mono quiet_mode skip_mono fork_mono predT fp_fun monos ctxt =
 (message (quiet_mode orelse skip_mono andalso !quick_and_dirty orelse fork_mono)
    "  Proving monotonicity ...";
  (if skip_mono then Skip_Proof.prove else if fork_mono then Goal.prove_future else Goal.prove) ctxt
    [] []
    (HOLogic.mk_Trueprop
      (Const (@{const_name Orderings.mono}, (predT --> predT) --> HOLogic.boolT) $ fp_fun))
    (fn _ => EVERY [rtac @{thm monoI} 1,
      REPEAT (resolve_tac [@{thm le_funI}, @{thm le_boolI'}] 1),
      REPEAT (FIRST
        [atac 1,
         resolve_tac (map (mk_mono ctxt) monos @ get_monos ctxt) 1,
         etac @{thm le_funE} 1, dtac @{thm le_boolD} 1])]));


(* prove introduction rules *)

fun prove_intrs quiet_mode coind mono fp_def k intr_ts rec_preds_defs ctxt ctxt' =
  let
    val _ = clean_message quiet_mode "  Proving the introduction rules ...";

    val unfold = funpow k (fn th => th RS fun_cong)
      (mono RS (fp_def RS
        (if coind then @{thm def_gfp_unfold} else @{thm def_lfp_unfold})));

    val rules = [refl, TrueI, @{lemma "~ False" by (rule notI)}, exI, conjI];

    val intrs = map_index (fn (i, intr) =>
      Skip_Proof.prove ctxt [] [] intr (fn _ => EVERY
       [rewrite_goals_tac rec_preds_defs,
        rtac (unfold RS iffD2) 1,
        EVERY1 (select_disj (length intr_ts) (i + 1)),
        (*Not ares_tac, since refl must be tried before any equality assumptions;
          backtracking may occur if the premises have extra variables!*)
        DEPTH_SOLVE_1 (resolve_tac rules 1 APPEND assume_tac 1)])
       |> singleton (Proof_Context.export ctxt ctxt')) intr_ts

  in (intrs, unfold) end;


(* prove elimination rules *)

fun prove_elims quiet_mode cs params intr_ts intr_names unfold rec_preds_defs ctxt ctxt''' =
  let
    val _ = clean_message quiet_mode "  Proving the elimination rules ...";

    val ([pname], ctxt') = Variable.variant_fixes ["P"] ctxt;
    val P = HOLogic.mk_Trueprop (Free (pname, HOLogic.boolT));

    fun dest_intr r =
      (the (dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r))),
       Logic.strip_assums_hyp r, Logic.strip_params r);

    val intrs = map dest_intr intr_ts ~~ intr_names;

    val rules1 = [disjE, exE, FalseE];
    val rules2 = [conjE, FalseE, @{lemma "~ True ==> R" by (rule notE [OF _ TrueI])}];

    fun prove_elim c =
      let
        val Ts = arg_types_of (length params) c;
        val (anames, ctxt'') = Variable.variant_fixes (mk_names "a" (length Ts)) ctxt';
        val frees = map Free (anames ~~ Ts);

        fun mk_elim_prem ((_, _, us, _), ts, params') =
          Logic.list_all (params',
            Logic.list_implies (map (HOLogic.mk_Trueprop o HOLogic.mk_eq)
              (frees ~~ us) @ ts, P));
        val c_intrs = filter (equal c o #1 o #1 o #1) intrs;
        val prems = HOLogic.mk_Trueprop (list_comb (c, params @ frees)) ::
           map mk_elim_prem (map #1 c_intrs)
      in
        (Skip_Proof.prove ctxt'' [] prems P
          (fn {prems, ...} => EVERY
            [cut_facts_tac [hd prems] 1,
             rewrite_goals_tac rec_preds_defs,
             dtac (unfold RS iffD1) 1,
             REPEAT (FIRSTGOAL (eresolve_tac rules1)),
             REPEAT (FIRSTGOAL (eresolve_tac rules2)),
             EVERY (map (fn prem =>
               DEPTH_SOLVE_1 (ares_tac [rewrite_rule rec_preds_defs prem, conjI] 1)) (tl prems))])
          |> singleton (Proof_Context.export ctxt'' ctxt'''),
         map #2 c_intrs, length Ts)
      end

   in map prove_elim cs end;


(* prove simplification equations *)

fun prove_eqs quiet_mode cs params intr_ts intrs
    (elims: (thm * bstring list * int) list) ctxt ctxt'' =  (* FIXME ctxt'' ?? *)
  let
    val _ = clean_message quiet_mode "  Proving the simplification rules ...";

    fun dest_intr r =
      (the (dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r))),
       Logic.strip_assums_hyp r, Logic.strip_params r);
    val intr_ts' = map dest_intr intr_ts;

    fun prove_eq c (elim: thm * 'a * 'b) =
      let
        val Ts = arg_types_of (length params) c;
        val (anames, ctxt') = Variable.variant_fixes (mk_names "a" (length Ts)) ctxt;
        val frees = map Free (anames ~~ Ts);
        val c_intrs = filter (equal c o #1 o #1 o #1) (intr_ts' ~~ intrs);
        fun mk_intr_conj (((_, _, us, _), ts, params'), _) =
          let
            fun list_ex ([], t) = t
              | list_ex ((a, T) :: vars, t) =
                  HOLogic.exists_const T $ Abs (a, T, list_ex (vars, t));
            val conjs = map2 (curry HOLogic.mk_eq) frees us @ (map HOLogic.dest_Trueprop ts);
          in
            list_ex (params', if null conjs then @{term True} else foldr1 HOLogic.mk_conj conjs)
          end;
        val lhs = list_comb (c, params @ frees);
        val rhs =
          if null c_intrs then @{term False}
          else foldr1 HOLogic.mk_disj (map mk_intr_conj c_intrs);
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
        fun prove_intr1 (i, _) = Subgoal.FOCUS_PREMS (fn {params, prems, ...} =>
            let
              val (prems', last_prem) = split_last prems;
            in
              EVERY1 (select_disj (length c_intrs) (i + 1)) THEN
              EVERY (replicate (length params) (rtac @{thm exI} 1)) THEN
              EVERY (map (fn prem => (rtac @{thm conjI} 1 THEN rtac prem 1)) prems') THEN
              rtac last_prem 1
            end) ctxt' 1;
        fun prove_intr2 (((_, _, us, _), ts, params'), intr) =
          EVERY (replicate (length params') (etac @{thm exE} 1)) THEN
          EVERY (replicate (length ts + length us - 1) (etac @{thm conjE} 1)) THEN
          Subgoal.FOCUS_PREMS (fn {params, prems, ...} =>
            let
              val (eqs, prems') = chop (length us) prems;
              val rew_thms = map (fn th => th RS @{thm eq_reflection}) eqs;
            in
              rewrite_goal_tac rew_thms 1 THEN
              rtac intr 1 THEN
              EVERY (map (fn p => rtac p 1) prems')
            end) ctxt' 1;
      in
        Skip_Proof.prove ctxt' [] [] eq (fn _ =>
          rtac @{thm iffI} 1 THEN etac (#1 elim) 1 THEN
          EVERY (map_index prove_intr1 c_intrs) THEN
          (if null c_intrs then etac @{thm FalseE} 1
           else
            let val (c_intrs', last_c_intr) = split_last c_intrs in
              EVERY (map (fn ci => etac @{thm disjE} 1 THEN prove_intr2 ci) c_intrs') THEN
              prove_intr2 last_c_intr
            end))
        |> rulify
        |> singleton (Proof_Context.export ctxt' ctxt'')
      end;
  in
    map2 prove_eq cs elims
  end;


(* derivation of simplified elimination rules *)

local

(*delete needless equality assumptions*)
val refl_thin = Goal.prove_global @{theory HOL} [] [] @{prop "!!P. a = a ==> P ==> P"}
  (fn _ => assume_tac 1);
val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE];
val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

fun simp_case_tac ss i =
  EVERY' [elim_tac, asm_full_simp_tac ss, elim_tac, REPEAT o bound_hyp_subst_tac] i;

in

fun mk_cases ctxt prop =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ss = simpset_of ctxt;

    fun err msg =
      error (Pretty.string_of (Pretty.block
        [Pretty.str msg, Pretty.fbrk, Syntax.pretty_term ctxt prop]));

    val elims = Induct.find_casesP ctxt prop;

    val cprop = Thm.cterm_of thy prop;
    val tac = ALLGOALS (simp_case_tac ss) THEN prune_params_tac;
    fun mk_elim rl =
      Thm.implies_intr cprop (Tactic.rule_by_tactic ctxt tac (Thm.assume cprop RS rl))
      |> singleton (Variable.export (Variable.auto_fixes prop ctxt) ctxt);
  in
    (case get_first (try mk_elim) elims of
      SOME r => r
    | NONE => err "Proposition not an inductive predicate:")
  end;

end;


(* inductive_cases *)

fun gen_inductive_cases prep_att prep_prop args lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val facts = args |> Par_List.map (fn ((a, atts), props) =>
      ((a, map (prep_att thy) atts),
        Par_List.map (Thm.no_attributes o single o mk_cases lthy o prep_prop lthy) props));
  in lthy |> Local_Theory.notes facts |>> map snd end;

val inductive_cases = gen_inductive_cases Attrib.intern_src Syntax.read_prop;
val inductive_cases_i = gen_inductive_cases (K I) Syntax.check_prop;


val ind_cases_setup =
  Method.setup @{binding ind_cases}
    (Scan.lift (Scan.repeat1 Args.name_source --
      Scan.optional (Args.$$$ "for" |-- Scan.repeat1 Args.binding) []) >>
      (fn (raw_props, fixes) => fn ctxt =>
        let
          val (_, ctxt') = Variable.add_fixes_binding fixes ctxt;
          val props = Syntax.read_props ctxt' raw_props;
          val ctxt'' = fold Variable.declare_term props ctxt';
          val rules = Proof_Context.export ctxt'' ctxt (map (mk_cases ctxt'') props)
        in Method.erule 0 rules end))
    "dynamic case analysis on predicates";


(* derivation of simplified equation *)

fun mk_simp_eq ctxt prop =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ctxt' = Variable.auto_fixes prop ctxt;
    val lhs_of = fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of;
    val substs =
      Item_Net.retrieve (get_equations ctxt) (HOLogic.dest_Trueprop prop)
      |> map_filter
        (fn eq => SOME (Pattern.match thy (lhs_of eq, HOLogic.dest_Trueprop prop)
            (Vartab.empty, Vartab.empty), eq)
          handle Pattern.MATCH => NONE);
    val (subst, eq) =
      (case substs of
        [s] => s
      | _ => error
        ("equations matching pattern " ^ Syntax.string_of_term ctxt prop ^ " is not unique"));
    val inst =
      map (fn v => (cterm_of thy (Var v), cterm_of thy (Envir.subst_term subst (Var v))))
        (Term.add_vars (lhs_of eq) []);
  in
    Drule.cterm_instantiate inst eq
    |> Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (Simplifier.full_rewrite (simpset_of ctxt))))
    |> singleton (Variable.export ctxt' ctxt)
  end


(* inductive simps *)

fun gen_inductive_simps prep_att prep_prop args lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val facts = args |> map (fn ((a, atts), props) =>
      ((a, map (prep_att thy) atts),
        map (Thm.no_attributes o single o mk_simp_eq lthy o prep_prop lthy) props));
  in lthy |> Local_Theory.notes facts |>> map snd end;

val inductive_simps = gen_inductive_simps Attrib.intern_src Syntax.read_prop;
val inductive_simps_i = gen_inductive_simps (K I) Syntax.check_prop;


(* prove induction rule *)

fun prove_indrule quiet_mode cs argTs bs xs rec_const params intr_ts mono
    fp_def rec_preds_defs ctxt ctxt''' =  (* FIXME ctxt''' ?? *)
  let
    val _ = clean_message quiet_mode "  Proving the induction rule ...";

    (* predicates for induction rule *)

    val (pnames, ctxt') = Variable.variant_fixes (mk_names "P" (length cs)) ctxt;
    val preds =
      map2 (curry Free) pnames
        (map (fn c => arg_types_of (length params) c ---> HOLogic.boolT) cs);

    (* transform an introduction rule into a premise for induction rule *)

    fun mk_ind_prem r =
      let
        fun subst s =
          (case dest_predicate cs params s of
            SOME (_, i, ys, (_, Ts)) =>
              let
                val k = length Ts;
                val bs = map Bound (k - 1 downto 0);
                val P = list_comb (nth preds i, map (incr_boundvars k) ys @ bs);
                val Q =
                  fold_rev Term.abs (mk_names "x" k ~~ Ts)
                    (HOLogic.mk_binop inductive_conj_name
                      (list_comb (incr_boundvars k s, bs), P));
              in (Q, case Ts of [] => SOME (s, P) | _ => NONE) end
          | NONE =>
              (case s of
                t $ u => (fst (subst t) $ fst (subst u), NONE)
              | Abs (a, T, t) => (Abs (a, T, fst (subst t)), NONE)
              | _ => (s, NONE)));

        fun mk_prem s prems =
          (case subst s of
            (_, SOME (t, u)) => t :: u :: prems
          | (t, _) => t :: prems);

        val SOME (_, i, ys, _) =
          dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r));
      in
        fold_rev (Logic.all o Free) (Logic.strip_params r)
          (Logic.list_implies (map HOLogic.mk_Trueprop (fold_rev mk_prem
            (map HOLogic.dest_Trueprop (Logic.strip_assums_hyp r)) []),
              HOLogic.mk_Trueprop (list_comb (nth preds i, ys))))
      end;

    val ind_prems = map mk_ind_prem intr_ts;


    (* make conclusions for induction rules *)

    val Tss = map (binder_types o fastype_of) preds;
    val (xnames, ctxt'') = Variable.variant_fixes (mk_names "x" (length (flat Tss))) ctxt';
    val mutual_ind_concl =
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (map (fn (((xnames, Ts), c), P) =>
          let val frees = map Free (xnames ~~ Ts)
          in HOLogic.mk_imp (list_comb (c, params @ frees), list_comb (P, frees)) end)
        (unflat Tss xnames ~~ Tss ~~ cs ~~ preds)));


    (* make predicate for instantiation of abstract induction rule *)

    val ind_pred =
      fold_rev lambda (bs @ xs) (foldr1 HOLogic.mk_conj
        (map_index (fn (i, P) => fold_rev (curry HOLogic.mk_imp)
           (make_bool_args HOLogic.mk_not I bs i)
           (list_comb (P, make_args' argTs xs (binder_types (fastype_of P))))) preds));

    val ind_concl =
      HOLogic.mk_Trueprop
        (HOLogic.mk_binrel @{const_name Orderings.less_eq} (rec_const, ind_pred));

    val raw_fp_induct = mono RS (fp_def RS @{thm def_lfp_induct});

    val induct = Skip_Proof.prove ctxt'' [] ind_prems ind_concl
      (fn {prems, ...} => EVERY
        [rewrite_goals_tac [inductive_conj_def],
         DETERM (rtac raw_fp_induct 1),
         REPEAT (resolve_tac [@{thm le_funI}, @{thm le_boolI}] 1),
         rewrite_goals_tac simp_thms2,
         (*This disjE separates out the introduction rules*)
         REPEAT (FIRSTGOAL (eresolve_tac [disjE, exE, FalseE])),
         (*Now break down the individual cases.  No disjE here in case
           some premise involves disjunction.*)
         REPEAT (FIRSTGOAL (etac conjE ORELSE' bound_hyp_subst_tac)),
         REPEAT (FIRSTGOAL
           (resolve_tac [conjI, impI] ORELSE' (etac notE THEN' atac))),
         EVERY (map (fn prem => DEPTH_SOLVE_1 (ares_tac [rewrite_rule
             (inductive_conj_def :: rec_preds_defs @ simp_thms2) prem,
           conjI, refl] 1)) prems)]);

    val lemma = Skip_Proof.prove ctxt'' [] []
      (Logic.mk_implies (ind_concl, mutual_ind_concl)) (fn _ => EVERY
        [rewrite_goals_tac rec_preds_defs,
         REPEAT (EVERY
           [REPEAT (resolve_tac [conjI, impI] 1),
            REPEAT (eresolve_tac [@{thm le_funE}, @{thm le_boolE}] 1),
            atac 1,
            rewrite_goals_tac simp_thms1,
            atac 1])]);

  in singleton (Proof_Context.export ctxt'' ctxt''') (induct RS lemma) end;



(** specification of (co)inductive predicates **)

fun mk_ind_def quiet_mode skip_mono fork_mono alt_name coind
    cs intr_ts monos params cnames_syn lthy =
  let
    val fp_name = if coind then @{const_name Inductive.gfp} else @{const_name Inductive.lfp};

    val argTs = fold (combine (op =) o arg_types_of (length params)) cs [];
    val k = log 2 1 (length cs);
    val predT = replicate k HOLogic.boolT ---> argTs ---> HOLogic.boolT;
    val p :: xs =
      map Free (Variable.variant_frees lthy intr_ts
        (("p", predT) :: (mk_names "x" (length argTs) ~~ argTs)));
    val bs =
      map Free (Variable.variant_frees lthy (p :: xs @ intr_ts)
        (map (rpair HOLogic.boolT) (mk_names "b" k)));

    fun subst t =
      (case dest_predicate cs params t of
        SOME (_, i, ts, (Ts, Us)) =>
          let
            val l = length Us;
            val zs = map Bound (l - 1 downto 0);
          in
            fold_rev (Term.abs o pair "z") Us
              (list_comb (p,
                make_bool_args' bs i @ make_args argTs
                  ((map (incr_boundvars l) ts ~~ Ts) @ (zs ~~ Us))))
          end
      | NONE =>
          (case t of
            t1 $ t2 => subst t1 $ subst t2
          | Abs (x, T, u) => Abs (x, T, subst u)
          | _ => t));

    (* transform an introduction rule into a conjunction  *)
    (*   [| p_i t; ... |] ==> p_j u                       *)
    (* is transformed into                                *)
    (*   b_j & x_j = u & p b_j t & ...                    *)

    fun transform_rule r =
      let
        val SOME (_, i, ts, (Ts, _)) =
          dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r));
        val ps =
          make_bool_args HOLogic.mk_not I bs i @
          map HOLogic.mk_eq (make_args' argTs xs Ts ~~ ts) @
          map (subst o HOLogic.dest_Trueprop) (Logic.strip_assums_hyp r);
      in
        fold_rev (fn (x, T) => fn P => HOLogic.exists_const T $ Abs (x, T, P))
          (Logic.strip_params r)
          (if null ps then @{term True} else foldr1 HOLogic.mk_conj ps)
      end;

    (* make a disjunction of all introduction rules *)

    val fp_fun =
      fold_rev lambda (p :: bs @ xs)
        (if null intr_ts then @{term False}
         else foldr1 HOLogic.mk_disj (map transform_rule intr_ts));

    (* add definiton of recursive predicates to theory *)

    val rec_name =
      if Binding.is_empty alt_name then
        Binding.name (space_implode "_" (map (Binding.name_of o fst) cnames_syn))
      else alt_name;

    val ((rec_const, (_, fp_def)), lthy') = lthy
      |> Local_Theory.conceal
      |> Local_Theory.define
        ((rec_name, case cnames_syn of [(_, syn)] => syn | _ => NoSyn),
         ((Binding.empty, @{attributes [nitpick_unfold]}),
           fold_rev lambda params
             (Const (fp_name, (predT --> predT) --> predT) $ fp_fun)))
      ||> Local_Theory.restore_naming lthy;
    val fp_def' =
      Simplifier.rewrite (HOL_basic_ss addsimps [fp_def])
        (cterm_of (Proof_Context.theory_of lthy') (list_comb (rec_const, params)));
    val specs =
      if length cs < 2 then []
      else
        map_index (fn (i, (name_mx, c)) =>
          let
            val Ts = arg_types_of (length params) c;
            val xs =
              map Free (Variable.variant_frees lthy intr_ts (mk_names "x" (length Ts) ~~ Ts));
          in
            (name_mx, (apfst Binding.conceal Attrib.empty_binding, fold_rev lambda (params @ xs)
              (list_comb (rec_const, params @ make_bool_args' bs i @
                make_args argTs (xs ~~ Ts)))))
          end) (cnames_syn ~~ cs);
    val (consts_defs, lthy'') = lthy'
      |> fold_map Local_Theory.define specs;
    val preds = (case cs of [_] => [rec_const] | _ => map #1 consts_defs);

    val (_, lthy''') = Variable.add_fixes (map (fst o dest_Free) params) lthy'';
    val mono = prove_mono quiet_mode skip_mono fork_mono predT fp_fun monos lthy''';
    val (_, lthy'''') =
      Local_Theory.note (apfst Binding.conceal Attrib.empty_binding,
        Proof_Context.export lthy''' lthy'' [mono]) lthy'';

  in (lthy'''', lthy''', rec_name, mono, fp_def', map (#2 o #2) consts_defs,
    list_comb (rec_const, params), preds, argTs, bs, xs)
  end;

fun declare_rules rec_binding coind no_ind cnames
    preds intrs intr_bindings intr_atts elims eqs raw_induct lthy =
  let
    val rec_name = Binding.name_of rec_binding;
    fun rec_qualified qualified = Binding.qualify qualified rec_name;
    val intr_names = map Binding.name_of intr_bindings;
    val ind_case_names = Rule_Cases.case_names intr_names;
    val induct =
      if coind then
        (raw_induct, [Rule_Cases.case_names [rec_name],
          Rule_Cases.case_conclusion (rec_name, intr_names),
          Rule_Cases.consumes 1, Induct.coinduct_pred (hd cnames)])
      else if no_ind orelse length cnames > 1 then
        (raw_induct, [ind_case_names, Rule_Cases.consumes 0])
      else (raw_induct RSN (2, rev_mp), [ind_case_names, Rule_Cases.consumes 1]);

    val (intrs', lthy1) =
      lthy |>
      Spec_Rules.add
        (if coind then Spec_Rules.Co_Inductive else Spec_Rules.Inductive) (preds, intrs) |>
      Local_Theory.notes
        (map (rec_qualified false) intr_bindings ~~ intr_atts ~~
          map (fn th => [([th],
           [Attrib.internal (K (Context_Rules.intro_query NONE))])]) intrs) |>>
      map (hd o snd);
    val (((_, elims'), (_, [induct'])), lthy2) =
      lthy1 |>
      Local_Theory.note ((rec_qualified true (Binding.name "intros"), []), intrs') ||>>
      fold_map (fn (name, (elim, cases, k)) =>
        Local_Theory.note
          ((Binding.qualify true (Long_Name.base_name name) (Binding.name "cases"),
            [Attrib.internal (K (Rule_Cases.case_names cases)),
             Attrib.internal (K (Rule_Cases.consumes 1)),
             Attrib.internal (K (Rule_Cases.constraints k)),
             Attrib.internal (K (Induct.cases_pred name)),
             Attrib.internal (K (Context_Rules.elim_query NONE))]), [elim]) #>
        apfst (hd o snd)) (if null elims then [] else cnames ~~ elims) ||>>
      Local_Theory.note
        ((rec_qualified true (Binding.name (coind_prefix coind ^ "induct")),
          map (Attrib.internal o K) (#2 induct)), [rulify (#1 induct)]);

    val (eqs', lthy3) = lthy2 |>
      fold_map (fn (name, eq) => Local_Theory.note
          ((Binding.qualify true (Long_Name.base_name name) (Binding.name "simps"),
            [Attrib.internal (K equation_add_permissive)]), [eq])
          #> apfst (hd o snd))
        (if null eqs then [] else (cnames ~~ eqs))
    val (inducts, lthy4) =
      if no_ind orelse coind then ([], lthy3)
      else
        let val inducts = cnames ~~ Project_Rule.projects lthy3 (1 upto length cnames) induct' in
          lthy3 |>
          Local_Theory.notes [((rec_qualified true (Binding.name "inducts"), []),
            inducts |> map (fn (name, th) => ([th],
              [Attrib.internal (K ind_case_names),
               Attrib.internal (K (Rule_Cases.consumes 1)),
               Attrib.internal (K (Induct.induct_pred name))])))] |>> snd o hd
        end;
  in (intrs', elims', eqs', induct', inducts, lthy4) end;

type inductive_flags =
  {quiet_mode: bool, verbose: bool, alt_name: binding, coind: bool,
    no_elim: bool, no_ind: bool, skip_mono: bool, fork_mono: bool};

type add_ind_def =
  inductive_flags ->
  term list -> (Attrib.binding * term) list -> thm list ->
  term list -> (binding * mixfix) list ->
  local_theory -> inductive_result * local_theory;

fun add_ind_def {quiet_mode, verbose, alt_name, coind, no_elim, no_ind, skip_mono, fork_mono}
    cs intros monos params cnames_syn lthy =
  let
    val _ = null cnames_syn andalso error "No inductive predicates given";
    val names = map (Binding.name_of o fst) cnames_syn;
    val _ = message (quiet_mode andalso not verbose)
      ("Proofs for " ^ coind_prefix coind ^ "inductive predicate(s) " ^ commas_quote names);

    val cnames = map (Local_Theory.full_name lthy o #1) cnames_syn;  (* FIXME *)
    val ((intr_names, intr_atts), intr_ts) =
      apfst split_list (split_list (map (check_rule lthy cs params) intros));

    val (lthy1, lthy2, rec_name, mono, fp_def, rec_preds_defs, rec_const, preds,
      argTs, bs, xs) = mk_ind_def quiet_mode skip_mono fork_mono alt_name coind cs intr_ts
        monos params cnames_syn lthy;

    val (intrs, unfold) = prove_intrs quiet_mode coind mono fp_def (length bs + length xs)
      intr_ts rec_preds_defs lthy2 lthy1;
    val elims =
      if no_elim then []
      else
        prove_elims quiet_mode cs params intr_ts (map Binding.name_of intr_names)
          unfold rec_preds_defs lthy2 lthy1;
    val raw_induct = zero_var_indexes
      (if no_ind then Drule.asm_rl
       else if coind then
         singleton (Proof_Context.export lthy2 lthy1)
           (rotate_prems ~1 (Object_Logic.rulify
             (fold_rule rec_preds_defs
               (rewrite_rule simp_thms3
                (mono RS (fp_def RS @{thm def_coinduct}))))))
       else
         prove_indrule quiet_mode cs argTs bs xs rec_const params intr_ts mono fp_def
           rec_preds_defs lthy2 lthy1);
    val eqs =
      if no_elim then [] else prove_eqs quiet_mode cs params intr_ts intrs elims lthy2 lthy1;

    val elims' = map (fn (th, ns, i) => (rulify th, ns, i)) elims;
    val intrs' = map rulify intrs;

    val (intrs'', elims'', eqs', induct, inducts, lthy3) =
      declare_rules rec_name coind no_ind
        cnames preds intrs' intr_names intr_atts elims' eqs raw_induct lthy1;

    val result =
      {preds = preds,
       intrs = intrs'',
       elims = elims'',
       raw_induct = rulify raw_induct,
       induct = induct,
       inducts = inducts,
       eqs = eqs'};

    val lthy4 = lthy3
      |> Local_Theory.declaration {syntax = false, pervasive = false} (fn phi =>
        let val result' = transform_result phi result;
        in put_inductives cnames (*global names!?*) ({names = cnames, coind = coind}, result') end);
  in (result, lthy4) end;


(* external interfaces *)

fun gen_add_inductive_i mk_def
    (flags as {quiet_mode, verbose, alt_name, coind, no_elim, no_ind, skip_mono, fork_mono})
    cnames_syn pnames spec monos lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val _ = Theory.requires thy "Inductive" (coind_prefix coind ^ "inductive definitions");


    (* abbrevs *)

    val (_, ctxt1) = Variable.add_fixes (map (Binding.name_of o fst o fst) cnames_syn) lthy;

    fun get_abbrev ((name, atts), t) =
      if can (Logic.strip_assums_concl #> Logic.dest_equals) t then
        let
          val _ = Binding.is_empty name andalso null atts orelse
            error "Abbreviations may not have names or attributes";
          val ((x, T), rhs) = Local_Defs.abs_def (snd (Local_Defs.cert_def ctxt1 t));
          val var =
            (case find_first (fn ((c, _), _) => Binding.name_of c = x) cnames_syn of
              NONE => error ("Undeclared head of abbreviation " ^ quote x)
            | SOME ((b, T'), mx) =>
                if T <> T' then error ("Bad type specification for abbreviation " ^ quote x)
                else (b, mx));
        in SOME (var, rhs) end
      else NONE;

    val abbrevs = map_filter get_abbrev spec;
    val bs = map (Binding.name_of o fst o fst) abbrevs;


    (* predicates *)

    val pre_intros = filter_out (is_some o get_abbrev) spec;
    val cnames_syn' = filter_out (member (op =) bs o Binding.name_of o fst o fst) cnames_syn;
    val cs = map (Free o apfst Binding.name_of o fst) cnames_syn';
    val ps = map Free pnames;

    val (_, ctxt2) = lthy |> Variable.add_fixes (map (Binding.name_of o fst o fst) cnames_syn');
    val _ = map (fn abbr => Local_Defs.fixed_abbrev abbr ctxt2) abbrevs;
    val ctxt3 = ctxt2 |> fold (snd oo Local_Defs.fixed_abbrev) abbrevs;
    val expand = Assumption.export_term ctxt3 lthy #> Proof_Context.cert_term lthy;

    fun close_rule r =
      fold (Logic.all o Free) (fold_aterms
        (fn t as Free (v as (s, _)) =>
            if Variable.is_fixed ctxt1 s orelse
              member (op =) ps t then I else insert (op =) v
          | _ => I) r []) r;

    val intros = map (apsnd (Syntax.check_term lthy #> close_rule #> expand)) pre_intros;
    val preds = map (fn ((c, _), mx) => (c, mx)) cnames_syn';
  in
    lthy
    |> mk_def flags cs intros monos ps preds
    ||> fold (snd oo Local_Theory.abbrev Syntax.mode_default) abbrevs
  end;

fun gen_add_inductive mk_def verbose coind cnames_syn pnames_syn intro_srcs raw_monos int lthy =
  let
    val ((vars, intrs), _) = lthy
      |> Proof_Context.set_mode Proof_Context.mode_abbrev
      |> Specification.read_spec (cnames_syn @ pnames_syn) intro_srcs;
    val (cs, ps) = chop (length cnames_syn) vars;
    val monos = Attrib.eval_thms lthy raw_monos;
    val flags = {quiet_mode = false, verbose = verbose, alt_name = Binding.empty,
      coind = coind, no_elim = false, no_ind = false, skip_mono = false, fork_mono = not int};
  in
    lthy
    |> gen_add_inductive_i mk_def flags cs (map (apfst Binding.name_of o fst) ps) intrs monos
  end;

val add_inductive_i = gen_add_inductive_i add_ind_def;
val add_inductive = gen_add_inductive add_ind_def;

fun add_inductive_global flags cnames_syn pnames pre_intros monos thy =
  let
    val name = Sign.full_name thy (fst (fst (hd cnames_syn)));
    val ctxt' = thy
      |> Named_Target.theory_init
      |> add_inductive_i flags cnames_syn pnames pre_intros monos |> snd
      |> Local_Theory.exit;
    val info = #2 (the_inductive ctxt' name);
  in (info, Proof_Context.theory_of ctxt') end;


(* read off arities of inductive predicates from raw induction rule *)
fun arities_of induct =
  map (fn (_ $ t $ u) =>
      (fst (dest_Const (head_of t)), length (snd (strip_comb u))))
    (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of induct)));

(* read off parameters of inductive predicate from raw induction rule *)
fun params_of induct =
  let
    val (_ $ t $ u :: _) = HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of induct));
    val (_, ts) = strip_comb t;
    val (_, us) = strip_comb u;
  in
    List.take (ts, length ts - length us)
  end;

val pname_of_intr =
  concl_of #> HOLogic.dest_Trueprop #> head_of #> dest_Const #> fst;

(* partition introduction rules according to predicate name *)
fun gen_partition_rules f induct intros =
  fold_rev (fn r => AList.map_entry op = (pname_of_intr (f r)) (cons r)) intros
    (map (rpair [] o fst) (arities_of induct));

val partition_rules = gen_partition_rules I;
fun partition_rules' induct = gen_partition_rules fst induct;

fun unpartition_rules intros xs =
  fold_map (fn r => AList.map_entry_yield op = (pname_of_intr r)
    (fn x :: xs => (x, xs)) #>> the) intros xs |> fst;

(* infer order of variables in intro rules from order of quantifiers in elim rule *)
fun infer_intro_vars elim arity intros =
  let
    val thy = theory_of_thm elim;
    val _ :: cases = prems_of elim;
    val used = map (fst o fst) (Term.add_vars (prop_of elim) []);
    fun mtch (t, u) =
      let
        val params = Logic.strip_params t;
        val vars =
          map (Var o apfst (rpair 0))
            (Name.variant_list used (map fst params) ~~ map snd params);
        val ts =
          map (curry subst_bounds (rev vars))
            (List.drop (Logic.strip_assums_hyp t, arity));
        val us = Logic.strip_imp_prems u;
        val tab =
          fold (Pattern.first_order_match thy) (ts ~~ us) (Vartab.empty, Vartab.empty);
      in
        map (Envir.subst_term tab) vars
      end
  in
    map (mtch o apsnd prop_of) (cases ~~ intros)
  end;



(** package setup **)

(* setup theory *)

val setup =
  ind_cases_setup #>
  Attrib.setup @{binding mono} (Attrib.add_del mono_add mono_del)
    "declaration of monotonicity rule";


(* outer syntax *)

val _ = Keyword.keyword "monos";

fun gen_ind_decl mk_def coind =
  Parse.fixes -- Parse.for_fixes --
  Scan.optional Parse_Spec.where_alt_specs [] --
  Scan.optional (Parse.$$$ "monos" |-- Parse.!!! Parse_Spec.xthms1) []
  >> (fn (((preds, params), specs), monos) =>
      (snd oo gen_add_inductive mk_def true coind preds params specs monos));

val ind_decl = gen_ind_decl add_ind_def;

val _ =
  Outer_Syntax.local_theory' "inductive" "define inductive predicates" Keyword.thy_decl
    (ind_decl false);

val _ =
  Outer_Syntax.local_theory' "coinductive" "define coinductive predicates" Keyword.thy_decl
    (ind_decl true);

val _ =
  Outer_Syntax.local_theory "inductive_cases"
    "create simplified instances of elimination rules (improper)" Keyword.thy_script
    (Parse.and_list1 Parse_Spec.specs >> (snd oo inductive_cases));

val _ =
  Outer_Syntax.local_theory "inductive_simps"
    "create simplification rules for inductive predicates" Keyword.thy_script
    (Parse.and_list1 Parse_Spec.specs >> (snd oo inductive_simps));

end;
