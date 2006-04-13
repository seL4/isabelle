(*  Title:      Pure/tactic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics.
*)

signature BASIC_TACTIC =
sig
  val ares_tac          : thm list -> int -> tactic
  val assume_tac        : int -> tactic
  val atac      : int ->tactic
  val bimatch_from_nets_tac:
      (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net -> int -> tactic
  val bimatch_tac       : (bool*thm)list -> int -> tactic
  val biresolution_from_nets_tac:
        ('a list -> (bool * thm) list) ->
        bool -> 'a Net.net * 'a Net.net -> int -> tactic
  val biresolve_from_nets_tac:
      (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net -> int -> tactic
  val biresolve_tac     : (bool*thm)list -> int -> tactic
  val build_net : thm list -> (int*thm) Net.net
  val build_netpair:    (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net ->
      (bool*thm)list -> (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net
  val compose_inst_tac  : (string*string)list -> (bool*thm*int) ->
                          int -> tactic
  val compose_tac       : (bool * thm * int) -> int -> tactic
  val cut_facts_tac     : thm list -> int -> tactic
  val cut_rules_tac     : thm list -> int -> tactic
  val cut_inst_tac      : (string*string)list -> thm -> int -> tactic
  val datac             : thm -> int -> int -> tactic
  val defer_tac         : int -> tactic
  val distinct_subgoals_tac     : tactic
  val dmatch_tac        : thm list -> int -> tactic
  val dresolve_tac      : thm list -> int -> tactic
  val dres_inst_tac     : (string*string)list -> thm -> int -> tactic
  val dtac              : thm -> int ->tactic
  val eatac             : thm -> int -> int -> tactic
  val etac              : thm -> int ->tactic
  val eq_assume_tac     : int -> tactic
  val ematch_tac        : thm list -> int -> tactic
  val eresolve_tac      : thm list -> int -> tactic
  val eres_inst_tac     : (string*string)list -> thm -> int -> tactic
  val fatac             : thm -> int -> int -> tactic
  val filter_prems_tac  : (term -> bool) -> int -> tactic
  val filter_thms       : (term*term->bool) -> int*term*thm list -> thm list
  val filt_resolve_tac  : thm list -> int -> int -> tactic
  val flexflex_tac      : tactic
  val fold_goals_tac    : thm list -> tactic
  val fold_rule         : thm list -> thm -> thm
  val fold_tac          : thm list -> tactic
  val forward_tac       : thm list -> int -> tactic
  val forw_inst_tac     : (string*string)list -> thm -> int -> tactic
  val ftac              : thm -> int ->tactic
  val insert_tagged_brl : ('a * (bool * thm)) *
    (('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net) ->
      ('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net
  val delete_tagged_brl : (bool * thm) *
    (('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net) ->
      ('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net
  val is_fact           : thm -> bool
  val lessb             : (bool * thm) * (bool * thm) -> bool
  val lift_inst_rule    : thm * int * (string*string)list * thm -> thm
  val make_elim         : thm -> thm
  val match_from_net_tac        : (int*thm) Net.net -> int -> tactic
  val match_tac : thm list -> int -> tactic
  val metacut_tac       : thm -> int -> tactic
  val net_bimatch_tac   : (bool*thm) list -> int -> tactic
  val net_biresolve_tac : (bool*thm) list -> int -> tactic
  val net_match_tac     : thm list -> int -> tactic
  val net_resolve_tac   : thm list -> int -> tactic
  val norm_hhf_tac      : int -> tactic
  val prune_params_tac  : tactic
  val rename_params_tac : string list -> int -> tactic
  val rename_tac        : string -> int -> tactic
  val rename_last_tac   : string -> string list -> int -> tactic
  val resolve_from_net_tac      : (int*thm) Net.net -> int -> tactic
  val resolve_tac       : thm list -> int -> tactic
  val res_inst_tac      : (string*string)list -> thm -> int -> tactic
  val rewrite_goal_tac  : thm list -> int -> tactic
  val rewrite_goals_rule: thm list -> thm -> thm
  val rewrite_rule      : thm list -> thm -> thm
  val rewrite_goals_tac : thm list -> tactic
  val rewrite_tac       : thm list -> tactic
  val asm_rewrite_goal_tac: bool * bool * bool -> (simpset -> tactic) -> simpset -> int -> tactic
  val rewtac            : thm -> tactic
  val rotate_tac        : int -> int -> tactic
  val rtac              : thm -> int -> tactic
  val rule_by_tactic    : tactic -> thm -> thm
  val solve_tac         : thm list -> int -> tactic
  val subgoal_tac       : string -> int -> tactic
  val subgoals_tac      : string list -> int -> tactic
  val subgoals_of_brl   : bool * thm -> int
  val term_lift_inst_rule       :
      thm * int * ((indexname * sort) * typ) list * ((indexname * typ) * term) list * thm
      -> thm
  val instantiate_tac   : (string * string) list -> tactic
  val thin_tac          : string -> int -> tactic
  val trace_goalno_tac  : (int -> tactic) -> int -> tactic
  val CONJUNCTS: tactic -> int -> tactic
  val PRECISE_CONJUNCTS: int -> tactic -> int -> tactic
end;

signature TACTIC =
sig
  include BASIC_TACTIC
  val innermost_params: int -> thm -> (string * typ) list
  val untaglist: (int * 'a) list -> 'a list
  val eq_kbrl: ('a * (bool * thm)) * ('a * (bool * thm)) -> bool
  val orderlist: (int * 'a) list -> 'a list
  val rewrite: bool -> thm list -> cterm -> thm
  val simplify: bool -> thm list -> thm -> thm
  val conjunction_tac: int -> tactic
  val precise_conjunction_tac: int -> int -> tactic
  val compose_inst_tac' : (indexname * string) list -> (bool * thm * int) ->
                          int -> tactic
  val lift_inst_rule'   : thm * int * (indexname * string) list * thm -> thm
  val eres_inst_tac'    : (indexname * string) list -> thm -> int -> tactic
  val res_inst_tac'     : (indexname * string) list -> thm -> int -> tactic
  val instantiate_tac'  : (indexname * string) list -> tactic
end;

structure Tactic: TACTIC =
struct

(*Discover which goal is chosen:  SOMEGOAL(trace_goalno_tac tac) *)
fun trace_goalno_tac tac i st =
    case Seq.pull(tac i st) of
        NONE    => Seq.empty
      | seqcell => (tracing ("Subgoal " ^ string_of_int i ^ " selected");
                         Seq.make(fn()=> seqcell));

(*Makes a rule by applying a tactic to an existing rule*)
fun rule_by_tactic tac rl =
  let val (st, thaw) = freeze_thaw (zero_var_indexes rl)
  in case Seq.pull (tac st)  of
        NONE        => raise THM("rule_by_tactic", 0, [rl])
      | SOME(st',_) => Thm.varifyT (thaw st')
  end;

(*** Basic tactics ***)

(*** The following fail if the goal number is out of range:
     thus (REPEAT (resolve_tac rules i)) stops once subgoal i disappears. *)

(*Solve subgoal i by assumption*)
fun assume_tac i = PRIMSEQ (assumption i);

(*Solve subgoal i by assumption, using no unification*)
fun eq_assume_tac i = PRIMITIVE (eq_assumption i);

(** Resolution/matching tactics **)

(*The composition rule/state: no lifting or var renaming.
  The arg = (bires_flg, orule, m) ;  see bicompose for explanation.*)
fun compose_tac arg i = PRIMSEQ (bicompose false arg i);

(*Converts a "destruct" rule like P&Q==>P to an "elimination" rule
  like [| P&Q; P==>R |] ==> R *)
fun make_elim rl = zero_var_indexes (rl RS revcut_rl);

(*Attack subgoal i by resolution, using flags to indicate elimination rules*)
fun biresolve_tac brules i = PRIMSEQ (biresolution false brules i);

(*Resolution: the simple case, works for introduction rules*)
fun resolve_tac rules = biresolve_tac (map (pair false) rules);

(*Resolution with elimination rules only*)
fun eresolve_tac rules = biresolve_tac (map (pair true) rules);

(*Forward reasoning using destruction rules.*)
fun forward_tac rls = resolve_tac (map make_elim rls) THEN' assume_tac;

(*Like forward_tac, but deletes the assumption after use.*)
fun dresolve_tac rls = eresolve_tac (map make_elim rls);

(*Shorthand versions: for resolution with a single theorem*)
val atac    =   assume_tac;
fun rtac rl =  resolve_tac [rl];
fun dtac rl = dresolve_tac [rl];
fun etac rl = eresolve_tac [rl];
fun ftac rl =  forward_tac [rl];
fun datac thm j = EVERY' (dtac thm::replicate j atac);
fun eatac thm j = EVERY' (etac thm::replicate j atac);
fun fatac thm j = EVERY' (ftac thm::replicate j atac);

(*Use an assumption or some rules ... A popular combination!*)
fun ares_tac rules = assume_tac  ORELSE'  resolve_tac rules;

fun solve_tac rules = resolve_tac rules THEN_ALL_NEW assume_tac;

(*Matching tactics -- as above, but forbid updating of state*)
fun bimatch_tac brules i = PRIMSEQ (biresolution true brules i);
fun match_tac rules  = bimatch_tac (map (pair false) rules);
fun ematch_tac rules = bimatch_tac (map (pair true) rules);
fun dmatch_tac rls   = ematch_tac (map make_elim rls);

(*Smash all flex-flex disagreement pairs in the proof state.*)
val flexflex_tac = PRIMSEQ flexflex_rule;

(*Remove duplicate subgoals.*)
fun distinct_subgoals_tac state =
  let
    val perm_tac = PRIMITIVE oo Thm.permute_prems;

    fun distinct_tac (i, k) =
      perm_tac 0 (i - 1) THEN
      perm_tac 1 (k - 1) THEN
      DETERM (PRIMSEQ (fn st =>
        Thm.compose_no_flatten false (st, 0) 1
          (Drule.incr_indexes st Drule.distinct_prems_rl))) THEN
      perm_tac 1 (1 - k) THEN
      perm_tac 0 (1 - i);

    fun distinct_subgoal_tac i st =
      (case Library.drop (i - 1, Thm.prems_of st) of
        [] => no_tac st
      | A :: Bs =>
          st |> EVERY (fold (fn (B, k) =>
            if A aconv B then cons (distinct_tac (i, k)) else I) (Bs ~~ (1 upto length Bs)) []));

    val goals = Thm.prems_of state;
    val dups = distinct (eq_fst (op aconv)) (goals ~~ (1 upto length goals));
  in EVERY (rev (map (distinct_subgoal_tac o snd) dups)) state end;

(*Determine print names of goal parameters (reversed)*)
fun innermost_params i st =
  let val (_, _, Bi, _) = dest_state (st, i)
  in rename_wrt_term Bi (Logic.strip_params Bi) end;

(*params of subgoal i as they are printed*)
fun params_of_state st i =
  let val (_, _, Bi, _) = dest_state(st,i)
      val params = Logic.strip_params Bi
  in rev(rename_wrt_term Bi params) end;

(*read instantiations with respect to subgoal i of proof state st*)
fun read_insts_in_state (st, i, sinsts, rule) =
  let val thy = Thm.theory_of_thm st
      and params = params_of_state st i
      and rts = types_sorts rule and (types,sorts) = types_sorts st
      fun types'(a, ~1) = (case AList.lookup (op =) params a of NONE => types (a, ~1) | sm => sm)
        | types' ixn = types ixn;
      val used = Drule.add_used rule (Drule.add_used st []);
  in read_insts thy rts (types',sorts) used sinsts end;

(*Lift and instantiate a rule wrt the given state and subgoal number *)
fun lift_inst_rule' (st, i, sinsts, rule) =
let val (Tinsts,insts) = read_insts_in_state (st, i, sinsts, rule)
    and {maxidx,...} = rep_thm st
    and params = params_of_state st i
    val paramTs = map #2 params
    and inc = maxidx+1
    fun liftvar (Var ((a,j), T)) = Var((a, j+inc), paramTs---> Logic.incr_tvar inc T)
      | liftvar t = raise TERM("Variable expected", [t]);
    fun liftterm t = list_abs_free (params,
                                    Logic.incr_indexes(paramTs,inc) t)
    (*Lifts instantiation pair over params*)
    fun liftpair (cv,ct) = (cterm_fun liftvar cv, cterm_fun liftterm ct)
    val lifttvar = pairself (ctyp_fun (Logic.incr_tvar inc))
in Drule.instantiate (map lifttvar Tinsts, map liftpair insts)
                     (Thm.lift_rule (Thm.cprem_of st i) rule)
end;

fun lift_inst_rule (st, i, sinsts, rule) = lift_inst_rule'
  (st, i, map (apfst Syntax.indexname) sinsts, rule);

(*
Like lift_inst_rule but takes terms, not strings, where the terms may contain
Bounds referring to parameters of the subgoal.

insts: [...,(vj,tj),...]

The tj may contain references to parameters of subgoal i of the state st
in the form of Bound k, i.e. the tj may be subterms of the subgoal.
To saturate the lose bound vars, the tj are enclosed in abstractions
corresponding to the parameters of subgoal i, thus turning them into
functions. At the same time, the types of the vj are lifted.

NB: the types in insts must be correctly instantiated already,
    i.e. Tinsts is not applied to insts.
*)
fun term_lift_inst_rule (st, i, Tinsts, insts, rule) =
let val {maxidx,thy,...} = rep_thm st
    val paramTs = map #2 (params_of_state st i)
    and inc = maxidx+1
    fun liftvar ((a,j), T) = Var((a, j+inc), paramTs---> Logic.incr_tvar inc T)
    (*lift only Var, not term, which must be lifted already*)
    fun liftpair (v,t) = (cterm_of thy (liftvar v), cterm_of thy t)
    fun liftTpair (((a, i), S), T) =
      (ctyp_of thy (TVar ((a, i + inc), S)),
       ctyp_of thy (Logic.incr_tvar inc T))
in Drule.instantiate (map liftTpair Tinsts, map liftpair insts)
                     (Thm.lift_rule (Thm.cprem_of st i) rule)
end;

(*** Resolve after lifting and instantation; may refer to parameters of the
     subgoal.  Fails if "i" is out of range.  ***)

(*compose version: arguments are as for bicompose.*)
fun gen_compose_inst_tac instf sinsts (bires_flg, rule, nsubgoal) i st =
  if i > nprems_of st then no_tac st
  else st |>
    (compose_tac (bires_flg, instf (st, i, sinsts, rule), nsubgoal) i
     handle TERM (msg,_)   => (warning msg;  no_tac)
          | THM  (msg,_,_) => (warning msg;  no_tac));

val compose_inst_tac = gen_compose_inst_tac lift_inst_rule;
val compose_inst_tac' = gen_compose_inst_tac lift_inst_rule';

(*"Resolve" version.  Note: res_inst_tac cannot behave sensibly if the
  terms that are substituted contain (term or type) unknowns from the
  goal, because it is unable to instantiate goal unknowns at the same time.

  The type checker is instructed not to freeze flexible type vars that
  were introduced during type inference and still remain in the term at the
  end.  This increases flexibility but can introduce schematic type vars in
  goals.
*)
fun res_inst_tac sinsts rule i =
    compose_inst_tac sinsts (false, rule, nprems_of rule) i;

fun res_inst_tac' sinsts rule i =
    compose_inst_tac' sinsts (false, rule, nprems_of rule) i;

(*eresolve elimination version*)
fun eres_inst_tac sinsts rule i =
    compose_inst_tac sinsts (true, rule, nprems_of rule) i;

fun eres_inst_tac' sinsts rule i =
    compose_inst_tac' sinsts (true, rule, nprems_of rule) i;

(*For forw_inst_tac and dres_inst_tac.  Preserve Var indexes of rl;
  increment revcut_rl instead.*)
fun make_elim_preserve rl =
  let val {maxidx,...} = rep_thm rl
      fun cvar ixn = cterm_of ProtoPure.thy (Var(ixn,propT));
      val revcut_rl' =
          instantiate ([],  [(cvar("V",0), cvar("V",maxidx+1)),
                             (cvar("W",0), cvar("W",maxidx+1))]) revcut_rl
      val arg = (false, rl, nprems_of rl)
      val [th] = Seq.list_of (bicompose false arg 1 revcut_rl')
  in  th  end
  handle Bind => raise THM("make_elim_preserve", 1, [rl]);

(*instantiate and cut -- for a FACT, anyway...*)
fun cut_inst_tac sinsts rule = res_inst_tac sinsts (make_elim_preserve rule);

(*forward tactic applies a RULE to an assumption without deleting it*)
fun forw_inst_tac sinsts rule = cut_inst_tac sinsts rule THEN' assume_tac;

(*dresolve tactic applies a RULE to replace an assumption*)
fun dres_inst_tac sinsts rule = eres_inst_tac sinsts (make_elim_preserve rule);

(*instantiate variables in the whole state*)
val instantiate_tac = PRIMITIVE o read_instantiate;

val instantiate_tac' = PRIMITIVE o Drule.read_instantiate';

(*Deletion of an assumption*)
fun thin_tac s = eres_inst_tac [("V",s)] thin_rl;

(*** Applications of cut_rl ***)

(*Used by metacut_tac*)
fun bires_cut_tac arg i =
    resolve_tac [cut_rl] i  THEN  biresolve_tac arg (i+1) ;

(*The conclusion of the rule gets assumed in subgoal i,
  while subgoal i+1,... are the premises of the rule.*)
fun metacut_tac rule = bires_cut_tac [(false,rule)];

(*Recognizes theorems that are not rules, but simple propositions*)
fun is_fact rl =
    case prems_of rl of
        [] => true  |  _::_ => false;

(*"Cut" a list of rules into the goal.  Their premises will become new
  subgoals.*)
fun cut_rules_tac ths i = EVERY (map (fn th => metacut_tac th i) ths);

(*As above, but inserts only facts (unconditional theorems);
  generates no additional subgoals. *)
fun cut_facts_tac ths = cut_rules_tac  (List.filter is_fact ths);

(*Introduce the given proposition as a lemma and subgoal*)
fun subgoal_tac sprop =
  DETERM o res_inst_tac [("psi", sprop)] cut_rl THEN' SUBGOAL (fn (prop, _) =>
    let val concl' = Logic.strip_assums_concl prop in
      if null (term_tvars concl') then ()
      else warning"Type variables in new subgoal: add a type constraint?";
      all_tac
  end);

(*Introduce a list of lemmas and subgoals*)
fun subgoals_tac sprops = EVERY' (map subgoal_tac sprops);


(**** Indexing and filtering of theorems ****)

(*Returns the list of potentially resolvable theorems for the goal "prem",
        using the predicate  could(subgoal,concl).
  Resulting list is no longer than "limit"*)
fun filter_thms could (limit, prem, ths) =
  let val pb = Logic.strip_assums_concl prem;   (*delete assumptions*)
      fun filtr (limit, []) = []
        | filtr (limit, th::ths) =
            if limit=0 then  []
            else if could(pb, concl_of th)  then th :: filtr(limit-1, ths)
            else filtr(limit,ths)
  in  filtr(limit,ths)  end;


(*** biresolution and resolution using nets ***)

(** To preserve the order of the rules, tag them with increasing integers **)

(*insert tags*)
fun taglist k [] = []
  | taglist k (x::xs) = (k,x) :: taglist (k+1) xs;

(*remove tags and suppress duplicates -- list is assumed sorted!*)
fun untaglist [] = []
  | untaglist [(k:int,x)] = [x]
  | untaglist ((k,x) :: (rest as (k',x')::_)) =
      if k=k' then untaglist rest
      else    x :: untaglist rest;

(*return list elements in original order*)
fun orderlist kbrls = untaglist (sort (int_ord o pairself fst) kbrls);

(*insert one tagged brl into the pair of nets*)
fun insert_tagged_brl (kbrl as (k, (eres, th)), (inet, enet)) =
  if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.insert_term (K false) (prem, kbrl) enet)
    | NONE => error "insert_tagged_brl: elimination rule with no premises")
  else (Net.insert_term (K false) (concl_of th, kbrl) inet, enet);

(*build a pair of nets for biresolution*)
fun build_netpair netpair brls =
    foldr insert_tagged_brl netpair (taglist 1 brls);

(*delete one kbrl from the pair of nets*)
fun eq_kbrl ((_, (_, th)), (_, (_, th'))) = Drule.eq_thm_prop (th, th')

fun delete_tagged_brl (brl as (eres, th), (inet, enet)) =
  (if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.delete_term eq_kbrl (prem, ((), brl)) enet)
    | NONE => (inet, enet))  (*no major premise: ignore*)
  else (Net.delete_term eq_kbrl (Thm.concl_of th, ((), brl)) inet, enet))
  handle Net.DELETE => (inet,enet);


(*biresolution using a pair of nets rather than rules.
    function "order" must sort and possibly filter the list of brls.
    boolean "match" indicates matching or unification.*)
fun biresolution_from_nets_tac order match (inet,enet) =
  SUBGOAL
    (fn (prem,i) =>
      let val hyps = Logic.strip_assums_hyp prem
          and concl = Logic.strip_assums_concl prem
          val kbrls = Net.unify_term inet concl @
                      List.concat (map (Net.unify_term enet) hyps)
      in PRIMSEQ (biresolution match (order kbrls) i) end);

(*versions taking pre-built nets.  No filtering of brls*)
val biresolve_from_nets_tac = biresolution_from_nets_tac orderlist false;
val bimatch_from_nets_tac   = biresolution_from_nets_tac orderlist true;

(*fast versions using nets internally*)
val net_biresolve_tac =
    biresolve_from_nets_tac o build_netpair(Net.empty,Net.empty);

val net_bimatch_tac =
    bimatch_from_nets_tac o build_netpair(Net.empty,Net.empty);

(*** Simpler version for resolve_tac -- only one net, and no hyps ***)

(*insert one tagged rl into the net*)
fun insert_krl (krl as (k,th), net) =
    Net.insert_term (K false) (concl_of th, krl) net;

(*build a net of rules for resolution*)
fun build_net rls =
    foldr insert_krl Net.empty (taglist 1 rls);

(*resolution using a net rather than rules; pred supports filt_resolve_tac*)
fun filt_resolution_from_net_tac match pred net =
  SUBGOAL
    (fn (prem,i) =>
      let val krls = Net.unify_term net (Logic.strip_assums_concl prem)
      in
         if pred krls
         then PRIMSEQ
                (biresolution match (map (pair false) (orderlist krls)) i)
         else no_tac
      end);

(*Resolve the subgoal using the rules (making a net) unless too flexible,
   which means more than maxr rules are unifiable.      *)
fun filt_resolve_tac rules maxr =
    let fun pred krls = length krls <= maxr
    in  filt_resolution_from_net_tac false pred (build_net rules)  end;

(*versions taking pre-built nets*)
val resolve_from_net_tac = filt_resolution_from_net_tac false (K true);
val match_from_net_tac = filt_resolution_from_net_tac true (K true);

(*fast versions using nets internally*)
val net_resolve_tac = resolve_from_net_tac o build_net;
val net_match_tac = match_from_net_tac o build_net;


(*** For Natural Deduction using (bires_flg, rule) pairs ***)

(*The number of new subgoals produced by the brule*)
fun subgoals_of_brl (true,rule)  = nprems_of rule - 1
  | subgoals_of_brl (false,rule) = nprems_of rule;

(*Less-than test: for sorting to minimize number of new subgoals*)
fun lessb (brl1,brl2) = subgoals_of_brl brl1 < subgoals_of_brl brl2;


(*** Meta-Rewriting Tactics ***)

val simple_prover =
  SINGLE o (fn ss => ALLGOALS (resolve_tac (MetaSimplifier.prems_of_ss ss)));

val rewrite = MetaSimplifier.rewrite_aux simple_prover;
val simplify = MetaSimplifier.simplify_aux simple_prover;
val rewrite_rule = simplify true;
val rewrite_goals_rule = MetaSimplifier.rewrite_goals_rule_aux simple_prover;

(*Rewrite subgoal i only.  SELECT_GOAL avoids inefficiencies in goals_conv.*)
fun asm_rewrite_goal_tac mode prover_tac ss =
  SELECT_GOAL
    (PRIMITIVE (MetaSimplifier.rewrite_goal_rule mode (SINGLE o prover_tac) ss 1));

fun rewrite_goal_tac rews =
  let val ss = MetaSimplifier.empty_ss addsimps rews in
    fn i => fn st => asm_rewrite_goal_tac (true, false, false) (K no_tac)
      (MetaSimplifier.theory_context (Thm.theory_of_thm st) ss) i st
  end;

(*Rewrite throughout proof state. *)
fun rewrite_tac defs = PRIMITIVE(rewrite_rule defs);

(*Rewrite subgoals only, not main goal. *)
fun rewrite_goals_tac defs = PRIMITIVE (rewrite_goals_rule defs);
fun rewtac def = rewrite_goals_tac [def];

val norm_hhf_tac =
  rtac Drule.asm_rl  (*cheap approximation -- thanks to builtin Logic.flatten_params*)
  THEN' SUBGOAL (fn (t, i) =>
    if Drule.is_norm_hhf t then all_tac
    else rewrite_goal_tac [Drule.norm_hhf_eq] i);


(*** for folding definitions, handling critical pairs ***)

(*The depth of nesting in a term*)
fun term_depth (Abs(a,T,t)) = 1 + term_depth t
  | term_depth (f$t) = 1 + Int.max(term_depth f, term_depth t)
  | term_depth _ = 0;

val lhs_of_thm = #1 o Logic.dest_equals o prop_of;

(*folding should handle critical pairs!  E.g. K == Inl(0),  S == Inr(Inl(0))
  Returns longest lhs first to avoid folding its subexpressions.*)
fun sort_lhs_depths defs =
  let val keylist = AList.make (term_depth o lhs_of_thm) defs
      val keys = sort_distinct (rev_order o int_ord) (map #2 keylist)
  in map (AList.find (op =) keylist) keys end;

val rev_defs = sort_lhs_depths o map symmetric;

fun fold_rule defs thm = Library.foldl (fn (th, ds) => rewrite_rule ds th) (thm, rev_defs defs);
fun fold_tac defs = EVERY (map rewrite_tac (rev_defs defs));
fun fold_goals_tac defs = EVERY (map rewrite_goals_tac (rev_defs defs));


(*** Renaming of parameters in a subgoal
     Names may contain letters, digits or primes and must be
     separated by blanks ***)

fun rename_params_tac xs i =
  case Library.find_first (not o Syntax.is_identifier) xs of
      SOME x => error ("Not an identifier: " ^ x)
    | NONE =>
       (if !Logic.auto_rename
         then (warning "Resetting Logic.auto_rename";
             Logic.auto_rename := false)
        else (); PRIMITIVE (rename_params_rule (xs, i)));

fun rename_tac str i =
  let val cs = Symbol.explode str in
  case #2 (take_prefix (Symbol.is_letdig orf Symbol.is_blank) cs) of
      [] => rename_params_tac (scanwords Symbol.is_letdig cs) i
    | c::_ => error ("Illegal character: " ^ c)
  end;

(*Rename recent parameters using names generated from a and the suffixes,
  provided the string a, which represents a term, is an identifier. *)
fun rename_last_tac a sufs i =
  let val names = map (curry op^ a) sufs
  in  if Syntax.is_identifier a
      then PRIMITIVE (rename_params_rule (names,i))
      else all_tac
  end;

(*Prunes all redundant parameters from the proof state by rewriting.
  DOES NOT rewrite main goal, where quantification over an unused bound
    variable is sometimes done to avoid the need for cut_facts_tac.*)
val prune_params_tac = rewrite_goals_tac [triv_forall_equality];

(*rotate_tac n i: rotate the assumptions of subgoal i by n positions, from
  right to left if n is positive, and from left to right if n is negative.*)
fun rotate_tac 0 i = all_tac
  | rotate_tac k i = PRIMITIVE (rotate_rule k i);

(*Rotates the given subgoal to be the last.*)
fun defer_tac i = PRIMITIVE (permute_prems (i-1) 1);

(* remove premises that do not satisfy p; fails if all prems satisfy p *)
fun filter_prems_tac p =
  let fun Then NONE tac = SOME tac
        | Then (SOME tac) tac' = SOME(tac THEN' tac');
      fun thins ((tac,n),H) =
        if p H then (tac,n+1)
        else (Then tac (rotate_tac n THEN' etac thin_rl),0);
  in SUBGOAL(fn (subg,n) =>
       let val Hs = Logic.strip_assums_hyp subg
       in case fst(Library.foldl thins ((NONE,0),Hs)) of
            NONE => no_tac | SOME tac => tac n
       end)
  end;


(* meta-level conjunction *)

val conj_tac = SUBGOAL (fn (goal, i) =>
  if can Logic.dest_conjunction goal then rtac Conjunction.conjunctionI i
  else no_tac);

val conjunction_tac = TRY o REPEAT_ALL_NEW conj_tac;

val precise_conjunction_tac =
  let
    fun tac 0 i = eq_assume_tac i
      | tac 1 i = SUBGOAL (K all_tac) i
      | tac n i = conj_tac i THEN TRY (fn st => tac (n - 1) (i + 1) st);
  in TRY oo tac end;

fun CONJUNCTS tac =
  SELECT_GOAL (conjunction_tac 1
    THEN tac
    THEN PRIMITIVE (Conjunction.uncurry ~1));

fun PRECISE_CONJUNCTS n tac =
  SELECT_GOAL (precise_conjunction_tac n 1
    THEN tac
    THEN PRIMITIVE (Conjunction.uncurry ~1));

end;

structure BasicTactic: BASIC_TACTIC = Tactic;
open BasicTactic;
