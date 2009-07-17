(*  Title:      Tools/induct.ML
    Author:     Markus Wenzel, TU Muenchen

Proof by cases, induction, and coinduction.
*)

signature INDUCT_DATA =
sig
  val cases_default: thm
  val atomize: thm list
  val rulify: thm list
  val rulify_fallback: thm list
end;

signature INDUCT =
sig
  (*rule declarations*)
  val vars_of: term -> term list
  val dest_rules: Proof.context ->
    {type_cases: (string * thm) list, pred_cases: (string * thm) list,
      type_induct: (string * thm) list, pred_induct: (string * thm) list,
      type_coinduct: (string * thm) list, pred_coinduct: (string * thm) list}
  val print_rules: Proof.context -> unit
  val lookup_casesT: Proof.context -> string -> thm option
  val lookup_casesP: Proof.context -> string -> thm option
  val lookup_inductT: Proof.context -> string -> thm option
  val lookup_inductP: Proof.context -> string -> thm option
  val lookup_coinductT: Proof.context -> string -> thm option
  val lookup_coinductP: Proof.context -> string -> thm option
  val find_casesT: Proof.context -> typ -> thm list
  val find_casesP: Proof.context -> term -> thm list
  val find_inductT: Proof.context -> typ -> thm list
  val find_inductP: Proof.context -> term -> thm list
  val find_coinductT: Proof.context -> typ -> thm list
  val find_coinductP: Proof.context -> term -> thm list
  val cases_type: string -> attribute
  val cases_pred: string -> attribute
  val cases_del: attribute
  val induct_type: string -> attribute
  val induct_pred: string -> attribute
  val induct_del: attribute
  val coinduct_type: string -> attribute
  val coinduct_pred: string -> attribute
  val coinduct_del: attribute
  val casesN: string
  val inductN: string
  val coinductN: string
  val typeN: string
  val predN: string
  val setN: string
  (*proof methods*)
  val fix_tac: Proof.context -> int -> (string * typ) list -> int -> tactic
  val add_defs: (binding option * term) option list -> Proof.context ->
    (term option list * thm list) * Proof.context
  val atomize_term: theory -> term -> term
  val atomize_tac: int -> tactic
  val inner_atomize_tac: int -> tactic
  val rulified_term: thm -> theory * term
  val rulify_tac: int -> tactic
  val internalize: int -> thm -> thm
  val guess_instance: Proof.context -> thm -> int -> thm -> thm Seq.seq
  val cases_tac: Proof.context -> term option list list -> thm option ->
    thm list -> int -> cases_tactic
  val get_inductT: Proof.context -> term option list list -> thm list list
  val induct_tac: Proof.context -> (binding option * term) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> cases_tactic
  val coinduct_tac: Proof.context -> term option list -> term option list -> thm option ->
    thm list -> int -> cases_tactic
  val setup: theory -> theory
end;

functor InductFun(Data: INDUCT_DATA): INDUCT =
struct


(** misc utils **)

(* encode_type -- for indexing purposes *)

fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);


(* variables -- ordered left-to-right, preferring right *)

fun vars_of tm =
  rev (distinct (op =) (Term.fold_aterms (fn (t as Var _) => cons t | _ => I) tm []));

local

val mk_var = encode_type o #2 o Term.dest_Var;

fun concl_var which thm = mk_var (which (vars_of (Thm.concl_of thm))) handle Empty =>
  raise THM ("No variables in conclusion of rule", 0, [thm]);

in

fun left_var_prem thm = mk_var (hd (vars_of (hd (Thm.prems_of thm)))) handle Empty =>
  raise THM ("No variables in major premise of rule", 0, [thm]);

val left_var_concl = concl_var hd;
val right_var_concl = concl_var List.last;

end;



(** induct data **)

(* rules *)

type rules = (string * thm) Item_Net.T;

val init_rules =
  Item_Net.init (fn ((s1: string, th1), (s2, th2)) => s1 = s2 andalso
    Thm.eq_thm_prop (th1, th2));

fun filter_rules (rs: rules) th =
  filter (fn (_, th') => Thm.eq_thm_prop (th, th')) (Item_Net.content rs);

fun lookup_rule (rs: rules) = AList.lookup (op =) (Item_Net.content rs);

fun pretty_rules ctxt kind rs =
  let val thms = map snd (Item_Net.content rs)
  in Pretty.big_list kind (map (ProofContext.pretty_thm ctxt) thms) end;


(* context data *)

structure InductData = GenericDataFun
(
  type T = (rules * rules) * (rules * rules) * (rules * rules);
  val empty =
    ((init_rules (left_var_prem o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (right_var_concl o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (left_var_concl o #2), init_rules (Thm.concl_of o #2)));
  val extend = I;
  fun merge _ (((casesT1, casesP1), (inductT1, inductP1), (coinductT1, coinductP1)),
      ((casesT2, casesP2), (inductT2, inductP2), (coinductT2, coinductP2))) =
    ((Item_Net.merge (casesT1, casesT2), Item_Net.merge (casesP1, casesP2)),
      (Item_Net.merge (inductT1, inductT2), Item_Net.merge (inductP1, inductP2)),
      (Item_Net.merge (coinductT1, coinductT2), Item_Net.merge (coinductP1, coinductP2)));
);

val get_local = InductData.get o Context.Proof;

fun dest_rules ctxt =
  let val ((casesT, casesP), (inductT, inductP), (coinductT, coinductP)) = get_local ctxt in
    {type_cases = Item_Net.content casesT,
     pred_cases = Item_Net.content casesP,
     type_induct = Item_Net.content inductT,
     pred_induct = Item_Net.content inductP,
     type_coinduct = Item_Net.content coinductT,
     pred_coinduct = Item_Net.content coinductP}
  end;

fun print_rules ctxt =
  let val ((casesT, casesP), (inductT, inductP), (coinductT, coinductP)) = get_local ctxt in
   [pretty_rules ctxt "coinduct type:" coinductT,
    pretty_rules ctxt "coinduct pred:" coinductP,
    pretty_rules ctxt "induct type:" inductT,
    pretty_rules ctxt "induct pred:" inductP,
    pretty_rules ctxt "cases type:" casesT,
    pretty_rules ctxt "cases pred:" casesP]
    |> Pretty.chunks |> Pretty.writeln
  end;

val _ =
  OuterSyntax.improper_command "print_induct_rules" "print induction and cases rules"
    OuterKeyword.diag (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_rules o Toplevel.context_of)));


(* access rules *)

val lookup_casesT = lookup_rule o #1 o #1 o get_local;
val lookup_casesP = lookup_rule o #2 o #1 o get_local;
val lookup_inductT = lookup_rule o #1 o #2 o get_local;
val lookup_inductP = lookup_rule o #2 o #2 o get_local;
val lookup_coinductT = lookup_rule o #1 o #3 o get_local;
val lookup_coinductP = lookup_rule o #2 o #3 o get_local;


fun find_rules which how ctxt x =
  map snd (Item_Net.retrieve (which (get_local ctxt)) (how x));

val find_casesT = find_rules (#1 o #1) encode_type;
val find_casesP = find_rules (#2 o #1) I;
val find_inductT = find_rules (#1 o #2) encode_type;
val find_inductP = find_rules (#2 o #2) I;
val find_coinductT = find_rules (#1 o #3) encode_type;
val find_coinductP = find_rules (#2 o #3) I;



(** attributes **)

local

fun mk_att f g name arg =
  let val (x, thm) = g arg in (InductData.map (f (name, thm)) x, thm) end;

fun del_att which = Thm.declaration_attribute (fn th => InductData.map (which (pairself (fn rs =>
  fold Item_Net.delete (filter_rules rs th) rs))));

fun map1 f (x, y, z) = (f x, y, z);
fun map2 f (x, y, z) = (x, f y, z);
fun map3 f (x, y, z) = (x, y, f z);

fun add_casesT rule x = map1 (apfst (Item_Net.insert rule)) x;
fun add_casesP rule x = map1 (apsnd (Item_Net.insert rule)) x;
fun add_inductT rule x = map2 (apfst (Item_Net.insert rule)) x;
fun add_inductP rule x = map2 (apsnd (Item_Net.insert rule)) x;
fun add_coinductT rule x = map3 (apfst (Item_Net.insert rule)) x;
fun add_coinductP rule x = map3 (apsnd (Item_Net.insert rule)) x;

val consumes0 = RuleCases.consumes_default 0;
val consumes1 = RuleCases.consumes_default 1;

in

val cases_type = mk_att add_casesT consumes0;
val cases_pred = mk_att add_casesP consumes1;
val cases_del = del_att map1;

val induct_type = mk_att add_inductT consumes0;
val induct_pred = mk_att add_inductP consumes1;
val induct_del = del_att map2;

val coinduct_type = mk_att add_coinductT consumes0;
val coinduct_pred = mk_att add_coinductP consumes1;
val coinduct_del = del_att map3;

end;



(** attribute syntax **)

val casesN = "cases";
val inductN = "induct";
val coinductN = "coinduct";

val typeN = "type";
val predN = "pred";
val setN = "set";

local

fun spec k arg =
  Scan.lift (Args.$$$ k -- Args.colon) |-- arg ||
  Scan.lift (Args.$$$ k) >> K "";

fun attrib add_type add_pred del =
  spec typeN Args.tyname >> add_type ||
  spec predN Args.const >> add_pred ||
  spec setN Args.const >> add_pred ||
  Scan.lift Args.del >> K del;

in

val attrib_setup =
  Attrib.setup @{binding cases} (attrib cases_type cases_pred cases_del)
    "declaration of cases rule" #>
  Attrib.setup @{binding induct} (attrib induct_type induct_pred induct_del)
    "declaration of induction rule" #>
  Attrib.setup @{binding coinduct} (attrib coinduct_type coinduct_pred coinduct_del)
    "declaration of coinduction rule";

end;



(** method utils **)

(* alignment *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.take (n, xs) ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.drop (m - n, xs) ~~ ys) end;


(* prep_inst *)

fun prep_inst thy align tune (tm, ts) =
  let
    val cert = Thm.cterm_of thy;
    fun prep_var (x, SOME t) =
          let
            val cx = cert x;
            val xT = #T (Thm.rep_cterm cx);
            val ct = cert (tune t);
            val tT = Thm.ctyp_of_term ct;
          in
            if Type.could_unify (Thm.typ_of tT, xT) then SOME (cx, ct)
            else error (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Display.pretty_cterm ct, Pretty.str " ::", Pretty.brk 1,
              Display.pretty_ctyp (#T (Thm.crep_cterm ct))]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end;


(* trace_rules *)

fun trace_rules _ kind [] = error ("Unable to figure out " ^ kind ^ " rule")
  | trace_rules ctxt _ rules = Method.trace ctxt rules;



(** cases method **)

(*
  rule selection scheme:
          cases         - default case split
    `A t` cases ...     - predicate/set cases
          cases t       - type cases
    ...   cases ... r   - explicit rule
*)

local

fun get_casesT ctxt ((SOME t :: _) :: _) = find_casesT ctxt (Term.fastype_of t)
  | get_casesT _ _ = [];

fun get_casesP ctxt (fact :: _) = find_casesP ctxt (Thm.concl_of fact)
  | get_casesP _ _ = [];

in

fun cases_tac ctxt insts opt_rule facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    fun inst_rule r =
      if null insts then `RuleCases.get r
      else (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
        |> maps (prep_inst thy align_left I)
        |> Drule.cterm_instantiate) r |> pair (RuleCases.get r);

    val ruleq =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_casesP ctxt facts @ get_casesT ctxt insts @ [Data.cases_default])
          |> tap (trace_rules ctxt casesN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
  in
    fn i => fn st =>
      ruleq
      |> Seq.maps (RuleCases.consume [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        CASES (RuleCases.make_common false (thy, Thm.prop_of rule) cases)
          (Method.insert_tac more_facts i THEN Tactic.rtac rule i) st)
  end;

end;



(** induct method **)

val conjunction_congs = [@{thm Pure.all_conjunction}, @{thm imp_conjunction}];


(* atomize *)

fun atomize_term thy =
  MetaSimplifier.rewrite_term thy Data.atomize []
  #> ObjectLogic.drop_judgment thy;

val atomize_cterm = MetaSimplifier.rewrite true Data.atomize;

val atomize_tac = Simplifier.rewrite_goal_tac Data.atomize;

val inner_atomize_tac =
  Simplifier.rewrite_goal_tac (map Thm.symmetric conjunction_congs) THEN' atomize_tac;


(* rulify *)

fun rulify_term thy =
  MetaSimplifier.rewrite_term thy (Data.rulify @ conjunction_congs) [] #>
  MetaSimplifier.rewrite_term thy Data.rulify_fallback [];

fun rulified_term thm =
  let
    val thy = Thm.theory_of_thm thm;
    val rulify = rulify_term thy;
    val (As, B) = Logic.strip_horn (Thm.prop_of thm);
  in (thy, Logic.list_implies (map rulify As, rulify B)) end;

val rulify_tac =
  Simplifier.rewrite_goal_tac (Data.rulify @ conjunction_congs) THEN'
  Simplifier.rewrite_goal_tac Data.rulify_fallback THEN'
  Goal.conjunction_tac THEN_ALL_NEW
  (Simplifier.rewrite_goal_tac [@{thm Pure.conjunction_imp}] THEN' Goal.norm_hhf_tac);


(* prepare rule *)

fun rule_instance thy inst rule =
  Drule.cterm_instantiate (prep_inst thy align_left I (Thm.prop_of rule, inst)) rule;

fun internalize k th =
  th |> Thm.permute_prems 0 k
  |> Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of th - k) atomize_cterm);


(* guess rule instantiation -- cannot handle pending goal parameters *)

local

fun dest_env thy env =
  let
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val pairs = Vartab.dest (Envir.term_env env);
    val types = Vartab.dest (Envir.type_env env);
    val ts = map (cert o Envir.norm_term env o #2 o #2) pairs;
    val xs = map2 (curry (cert o Var)) (map #1 pairs) (map (#T o Thm.rep_cterm) ts);
  in (map (fn (xi, (S, T)) => (certT (TVar (xi, S)), certT T)) types, xs ~~ ts) end;

in

fun guess_instance ctxt rule i st =
  let
    val thy = ProofContext.theory_of ctxt;
    val maxidx = Thm.maxidx_of st;
    val goal = Thm.term_of (Thm.cprem_of st i);  (*exception Subscript*)
    val params = rev (Term.rename_wrt_term goal (Logic.strip_params goal));
  in
    if not (null params) then
      (warning ("Cannot determine rule instantiation due to pending parameter(s): " ^
        commas_quote (map (Syntax.string_of_term ctxt o Syntax.mark_boundT) params));
      Seq.single rule)
    else
      let
        val rule' = Thm.incr_indexes (maxidx + 1) rule;
        val concl = Logic.strip_assums_concl goal;
      in
        Unify.smash_unifiers thy [(Thm.concl_of rule', concl)] (Envir.empty (Thm.maxidx_of rule'))
        |> Seq.map (fn env => Drule.instantiate (dest_env thy env) rule')
      end
  end handle Subscript => Seq.empty;

end;


(* special renaming of rule parameters *)

fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = Name.clean (ProofContext.revert_skolem ctxt z);
        fun index i [] = []
          | index i (y :: ys) =
              if x = y then x ^ string_of_int i :: index (i + 1) ys
              else y :: index i ys;
        fun rename_params [] = []
          | rename_params ((y, Type (U, _)) :: ys) =
              (if U = T then x else y) :: rename_params ys
          | rename_params ((y, _) :: ys) = y :: rename_params ys;
        fun rename_asm A =
          let
            val xs = rename_params (Logic.strip_params A);
            val xs' =
              (case filter (fn x' => x' = x) xs of
                [] => xs | [_] => xs | _ => index 1 xs);
          in Logic.list_rename_params (xs', A) end;
        fun rename_prop p =
          let val (As, C) = Logic.strip_horn p
          in Logic.list_implies (map rename_asm As, C) end;
        val cp' = cterm_fun rename_prop (Thm.cprop_of thm);
        val thm' = Thm.equal_elim (Thm.reflexive cp') thm;
      in [RuleCases.save thm thm'] end
  | special_rename_params _ _ ths = ths;


(* fix_tac *)

local

fun goal_prefix k ((c as Const ("all", _)) $ Abs (a, T, B)) = c $ Abs (a, T, goal_prefix k B)
  | goal_prefix 0 _ = Term.dummy_pattern propT
  | goal_prefix k ((c as Const ("==>", _)) $ A $ B) = c $ A $ goal_prefix (k - 1) B
  | goal_prefix _ _ = Term.dummy_pattern propT;

fun goal_params k (Const ("all", _) $ Abs (_, _, B)) = goal_params k B + 1
  | goal_params 0 _ = 0
  | goal_params k (Const ("==>", _) $ _ $ B) = goal_params (k - 1) B
  | goal_params _ _ = 0;

fun meta_spec_tac ctxt n (x, T) = SUBGOAL (fn (goal, i) =>
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;

    val v = Free (x, T);
    fun spec_rule prfx (xs, body) =
      @{thm Pure.meta_spec}
      |> Thm.rename_params_rule ([Name.clean (ProofContext.revert_skolem ctxt x)], 1)
      |> Thm.lift_rule (cert prfx)
      |> `(Thm.prop_of #> Logic.strip_assums_concl)
      |-> (fn pred $ arg =>
        Drule.cterm_instantiate
          [(cert (Term.head_of pred), cert (Logic.rlist_abs (xs, body))),
           (cert (Term.head_of arg), cert (Logic.rlist_abs (xs, v)))]);

    fun goal_concl k xs (Const ("all", _) $ Abs (a, T, B)) = goal_concl k ((a, T) :: xs) B
      | goal_concl 0 xs B =
          if not (Term.exists_subterm (fn t => t aconv v) B) then NONE
          else SOME (xs, Term.absfree (x, T, Term.incr_boundvars 1 B))
      | goal_concl k xs (Const ("==>", _) $ _ $ B) = goal_concl (k - 1) xs B
      | goal_concl _ _ _ = NONE;
  in
    (case goal_concl n [] goal of
      SOME concl =>
        (compose_tac (false, spec_rule (goal_prefix n goal) concl, 1) THEN' rtac asm_rl) i
    | NONE => all_tac)
  end);

fun miniscope_tac p = CONVERSION o
  Conv.params_conv p (K (MetaSimplifier.rewrite true [Thm.symmetric Drule.norm_hhf_eq]));

in

fun fix_tac _ _ [] = K all_tac
  | fix_tac ctxt n xs = SUBGOAL (fn (goal, i) =>
     (EVERY' (map (meta_spec_tac ctxt n) xs) THEN'
      (miniscope_tac (goal_params n goal) ctxt)) i);

end;


(* add_defs *)

fun add_defs def_insts =
  let
    fun add (SOME (SOME x, t)) ctxt =
          let val ([(lhs, (_, th))], ctxt') =
            LocalDefs.add_defs [((x, NoSyn), (Thm.empty_binding, t))] ctxt
          in ((SOME lhs, [th]), ctxt') end
      | add (SOME (NONE, t)) ctxt = ((SOME t, []), ctxt)
      | add NONE ctxt = ((NONE, []), ctxt);
  in fold_map add def_insts #> apfst (split_list #> apsnd flat) end;


(* induct_tac *)

(*
  rule selection scheme:
    `A x` induct ...     - predicate/set induction
          induct x       - type induction
    ...   induct ... r   - explicit rule
*)

fun get_inductT ctxt insts =
  fold_rev multiply (insts |> map
      ((fn [] => NONE | ts => List.last ts) #>
        (fn NONE => TVar (("'a", 0), []) | SOME t => Term.fastype_of t) #>
        find_inductT ctxt)) [[]]
  |> filter_out (forall Thm.is_internal);

fun get_inductP ctxt (fact :: _) = map single (find_inductP ctxt (Thm.concl_of fact))
  | get_inductP _ _ = [];

fun induct_tac ctxt def_insts arbitrary taking opt_rule facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list;
    val atomized_defs = map (map (Conv.fconv_rule ObjectLogic.atomize)) defs;

    fun inst_rule (concls, r) =
      (if null insts then `RuleCases.get r
       else (align_left "Rule has fewer conclusions than arguments given"
          (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
        |> maps (prep_inst thy align_right (atomize_term thy))
        |> Drule.cterm_instantiate) r |> pair (RuleCases.get r))
      |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th));

    val ruleq =
      (case opt_rule of
        SOME rs => Seq.single (inst_rule (RuleCases.strict_mutual_rule ctxt rs))
      | NONE =>
          (get_inductP ctxt facts @
            map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts))
          |> map_filter (RuleCases.mutual_rule ctxt)
          |> tap (trace_rules ctxt inductN o map #2)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));

    fun rule_cases rule =
      RuleCases.make_nested false (Thm.prop_of rule) (rulified_term rule);
  in
    (fn i => fn st =>
      ruleq
      |> Seq.maps (RuleCases.consume (flat defs) facts)
      |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            (Method.insert_tac (more_facts @ nth_list atomized_defs (j - 1))
              THEN' fix_tac defs_ctxt
                (nth concls (j - 1) + more_consumes)
                (nth_list arbitrary (j - 1))))
          THEN' inner_atomize_tac) j))
        THEN' atomize_tac) i st |> Seq.maps (fn st' =>
            guess_instance ctxt (internalize more_consumes rule) i st'
            |> Seq.map (rule_instance thy (burrow_options (Variable.polymorphic ctxt) taking))
            |> Seq.maps (fn rule' =>
              CASES (rule_cases rule' cases)
                (Tactic.rtac rule' i THEN
                  PRIMITIVE (singleton (ProofContext.export defs_ctxt ctxt))) st'))))
    THEN_ALL_NEW_CASES rulify_tac
  end;



(** coinduct method **)

(*
  rule selection scheme:
    goal "A x" coinduct ...   - predicate/set coinduction
               coinduct x     - type coinduction
               coinduct ... r - explicit rule
*)

local

fun get_coinductT ctxt (SOME t :: _) = find_coinductT ctxt (Term.fastype_of t)
  | get_coinductT _ _ = [];

fun get_coinductP ctxt goal = find_coinductP ctxt (Logic.strip_assums_concl goal);

fun main_prop_of th =
  if RuleCases.get_consumes th > 0 then Thm.major_prem_of th else Thm.concl_of th;

in

fun coinduct_tac ctxt inst taking opt_rule facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    fun inst_rule r =
      if null inst then `RuleCases.get r
      else Drule.cterm_instantiate (prep_inst thy align_right I (main_prop_of r, inst)) r
        |> pair (RuleCases.get r);

    fun ruleq goal =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_coinductP ctxt goal @ get_coinductT ctxt inst)
          |> tap (trace_rules ctxt coinductN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
  in
    SUBGOAL_CASES (fn (goal, i) => fn st =>
      ruleq goal
      |> Seq.maps (RuleCases.consume [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        guess_instance ctxt rule i st
        |> Seq.map (rule_instance thy (burrow_options (Variable.polymorphic ctxt) taking))
        |> Seq.maps (fn rule' =>
          CASES (RuleCases.make_common false (thy, Thm.prop_of rule') cases)
            (Method.insert_tac more_facts i THEN Tactic.rtac rule' i) st)))
  end;

end;



(** concrete syntax **)

structure P = OuterParse;

val arbitraryN = "arbitrary";
val takingN = "taking";
val ruleN = "rule";

local

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_pred =
  named_rule typeN Args.tyname get_type ||
  named_rule predN Args.const get_pred ||
  named_rule setN Args.const get_pred ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

val cases_rule = rule lookup_casesT lookup_casesP >> single_rule;
val induct_rule = rule lookup_inductT lookup_inductP;
val coinduct_rule = rule lookup_coinductT lookup_coinductP >> single_rule;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val def_inst =
  ((Scan.lift (Args.binding --| (Args.$$$ "\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ arbitraryN || Args.$$$ takingN || Args.$$$ typeN ||
    Args.$$$ predN || Args.$$$ setN || Args.$$$ ruleN) -- Args.colon)) scan;

val arbitrary = Scan.optional (Scan.lift (Args.$$$ arbitraryN -- Args.colon) |--
  P.and_list1' (Scan.repeat (unless_more_args free))) [];

val taking = Scan.optional (Scan.lift (Args.$$$ takingN -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

in

val cases_setup =
  Method.setup @{binding cases}
    (P.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule >>
      (fn (insts, opt_rule) => fn ctxt =>
        METHOD_CASES (fn facts => Seq.DETERM (HEADGOAL (cases_tac ctxt insts opt_rule facts)))))
    "case analysis on types or predicates/sets";

val induct_setup =
  Method.setup @{binding induct}
    (P.and_list' (Scan.repeat (unless_more_args def_inst)) --
      (arbitrary -- taking -- Scan.option induct_rule) >>
      (fn (insts, ((arbitrary, taking), opt_rule)) => fn ctxt =>
        RAW_METHOD_CASES (fn facts =>
          Seq.DETERM (HEADGOAL (induct_tac ctxt insts arbitrary taking opt_rule facts)))))
    "induction on types or predicates/sets";

val coinduct_setup =
  Method.setup @{binding coinduct}
    (Scan.repeat (unless_more_args inst) -- taking -- Scan.option coinduct_rule >>
      (fn ((insts, taking), opt_rule) => fn ctxt =>
        RAW_METHOD_CASES (fn facts =>
          Seq.DETERM (HEADGOAL (coinduct_tac ctxt insts taking opt_rule facts)))))
    "coinduction on types or predicates/sets";

end;



(** theory setup **)

val setup = attrib_setup #> cases_setup  #> induct_setup #> coinduct_setup;

end;
