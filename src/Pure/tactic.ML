(*  Title: 	tactic
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics 
*)

signature TACTIC =
  sig
  val ares_tac: thm list -> int -> tactic
  val asm_rewrite_goal_tac:
        bool*bool -> (meta_simpset -> tactic) -> meta_simpset -> int -> tactic
  val assume_tac: int -> tactic
  val atac: int ->tactic
  val bimatch_from_nets_tac: 
      (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net -> int -> tactic
  val bimatch_tac: (bool*thm)list -> int -> tactic
  val biresolve_from_nets_tac: 
      (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net -> int -> tactic
  val biresolve_tac: (bool*thm)list -> int -> tactic
  val build_net: thm list -> (int*thm) Net.net
  val build_netpair:    (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net ->
      (bool*thm)list -> (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net
  val compose_inst_tac: (string*string)list -> (bool*thm*int) -> int -> tactic
  val compose_tac: (bool * thm * int) -> int -> tactic 
  val cterm_lift_inst_rule:
      thm * int * (indexname*ctyp)list * (term*cterm)list  * thm -> thm
  val cut_facts_tac: thm list -> int -> tactic
  val cut_inst_tac: (string*string)list -> thm -> int -> tactic   
  val dmatch_tac: thm list -> int -> tactic
  val dresolve_tac: thm list -> int -> tactic
  val dres_inst_tac: (string*string)list -> thm -> int -> tactic   
  val dtac: thm -> int ->tactic
  val etac: thm -> int ->tactic
  val eq_assume_tac: int -> tactic   
  val ematch_tac: thm list -> int -> tactic
  val eresolve_tac: thm list -> int -> tactic
  val eres_inst_tac: (string*string)list -> thm -> int -> tactic   
  val filter_thms: (term*term->bool) -> int*term*thm list -> thm list
  val filt_resolve_tac: thm list -> int -> int -> tactic
  val flexflex_tac: tactic
  val fold_goals_tac: thm list -> tactic
  val fold_tac: thm list -> tactic
  val forward_tac: thm list -> int -> tactic   
  val forw_inst_tac: (string*string)list -> thm -> int -> tactic
  val freeze: thm -> thm   
  val insert_tagged_brl:  ('a*(bool*thm)) * 
                    (('a*(bool*thm))Net.net * ('a*(bool*thm))Net.net) ->
                    ('a*(bool*thm))Net.net * ('a*(bool*thm))Net.net
  val delete_tagged_brl:  (bool*thm) * 
                    ((int*(bool*thm))Net.net * (int*(bool*thm))Net.net) ->
                    (int*(bool*thm))Net.net * (int*(bool*thm))Net.net
  val is_fact: thm -> bool
  val lessb: (bool * thm) * (bool * thm) -> bool
  val lift_inst_rule: thm * int * (string*string)list * thm -> thm
  val make_elim: thm -> thm
  val match_from_net_tac: (int*thm) Net.net -> int -> tactic
  val match_tac: thm list -> int -> tactic
  val metacut_tac: thm -> int -> tactic   
  val net_bimatch_tac: (bool*thm) list -> int -> tactic
  val net_biresolve_tac: (bool*thm) list -> int -> tactic
  val net_match_tac: thm list -> int -> tactic
  val net_resolve_tac: thm list -> int -> tactic
  val PRIMITIVE: (thm -> thm) -> tactic  
  val PRIMSEQ: (thm -> thm Sequence.seq) -> tactic  
  val prune_params_tac: tactic
  val rename_tac: string -> int -> tactic
  val rename_last_tac: string -> string list -> int -> tactic
  val resolve_from_net_tac: (int*thm) Net.net -> int -> tactic
  val resolve_tac: thm list -> int -> tactic
  val res_inst_tac: (string*string)list -> thm -> int -> tactic   
  val rewrite_goals_tac: thm list -> tactic
  val rewrite_tac: thm list -> tactic
  val rewtac: thm -> tactic
  val rotate_tac: int -> int -> tactic
  val rtac: thm -> int -> tactic
  val rule_by_tactic: tactic -> thm -> thm
  val subgoal_tac: string -> int -> tactic
  val subgoals_tac: string list -> int -> tactic
  val subgoals_of_brl: bool * thm -> int
  val thin_tac: string -> int -> tactic
  val trace_goalno_tac: (int -> tactic) -> int -> tactic
  end;


structure Tactic : TACTIC = 
struct

(*Discover which goal is chosen:  SOMEGOAL(trace_goalno_tac tac) *)
fun trace_goalno_tac tac i st =  
    case Sequence.pull(tac i st) of
	None    => Sequence.null
      | seqcell => (prs("Subgoal " ^ string_of_int i ^ " selected\n"); 
    			 Sequence.seqof(fn()=> seqcell));

fun string_of (a,0) = a
  | string_of (a,i) = a ^ "_" ^ string_of_int i;

(*convert all Vars in a theorem to Frees*)
fun freeze th =
  let val fth = freezeT th
      val {prop,sign,...} = rep_thm fth
      fun mk_inst (Var(v,T)) = 
	  (cterm_of sign (Var(v,T)),
	   cterm_of sign (Free(string_of v, T)))
      val insts = map mk_inst (term_vars prop)
  in  instantiate ([],insts) fth  end;

(*Makes a rule by applying a tactic to an existing rule*)
fun rule_by_tactic tac rl =
    case Sequence.pull(tac (freeze (standard rl))) of
	None        => raise THM("rule_by_tactic", 0, [rl])
      | Some(rl',_) => standard rl';
 
(*** Basic tactics ***)

(*Makes a tactic whose effect on a state is given by thmfun: thm->thm seq.*)
fun PRIMSEQ thmfun st =  thmfun st handle THM _ => Sequence.null;

(*Makes a tactic whose effect on a state is given by thmfun: thm->thm.*)
fun PRIMITIVE thmfun = PRIMSEQ (Sequence.single o thmfun);

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
fun rtac rl = resolve_tac [rl];
fun etac rl = eresolve_tac [rl];
fun dtac rl = dresolve_tac [rl];
val atac = assume_tac;

(*Use an assumption or some rules ... A popular combination!*)
fun ares_tac rules = assume_tac  ORELSE'  resolve_tac rules;

(*Matching tactics -- as above, but forbid updating of state*)
fun bimatch_tac brules i = PRIMSEQ (biresolution true brules i);
fun match_tac rules  = bimatch_tac (map (pair false) rules);
fun ematch_tac rules = bimatch_tac (map (pair true) rules);
fun dmatch_tac rls   = ematch_tac (map make_elim rls);

(*Smash all flex-flex disagreement pairs in the proof state.*)
val flexflex_tac = PRIMSEQ flexflex_rule;

(*Lift and instantiate a rule wrt the given state and subgoal number *)
fun lift_inst_rule (st, i, sinsts, rule) =
let val {maxidx,sign,...} = rep_thm st
    val (_, _, Bi, _) = dest_state(st,i)
    val params = Logic.strip_params Bi	        (*params of subgoal i*)
    val params = rev(rename_wrt_term Bi params) (*as they are printed*)
    val paramTs = map #2 params
    and inc = maxidx+1
    fun liftvar (Var ((a,j), T)) = Var((a, j+inc), paramTs---> incr_tvar inc T)
      | liftvar t = raise TERM("Variable expected", [t]);
    fun liftterm t = list_abs_free (params, 
				    Logic.incr_indexes(paramTs,inc) t)
    (*Lifts instantiation pair over params*)
    fun liftpair (cv,ct) = (cterm_fun liftvar cv, cterm_fun liftterm ct)
    fun lifttvar((a,i),ctyp) =
	let val {T,sign} = rep_ctyp ctyp
	in  ((a,i+inc), ctyp_of sign (incr_tvar inc T)) end
    val rts = types_sorts rule and (types,sorts) = types_sorts st
    fun types'(a,~1) = (case assoc(params,a) of None => types(a,~1) | sm => sm)
      | types'(ixn) = types ixn;
    val used = add_term_tvarnames
                  (#prop(rep_thm st) $ #prop(rep_thm rule),[])
    val (Tinsts,insts) = read_insts sign rts (types',sorts) used sinsts
in instantiate (map lifttvar Tinsts, map liftpair insts)
               (lift_rule (st,i) rule)
end;

(*Like lift_inst_rule but takes cterms, not strings.
  The cterms must be functions of the parameters of the subgoal,
  i.e. they are assumed to be lifted already!
  Also: types of Vars must be fully instantiated already *)
fun cterm_lift_inst_rule (st, i, Tinsts, insts, rule) =
let val {maxidx,sign,...} = rep_thm st
    val (_, _, Bi, _) = dest_state(st,i)
    val params = Logic.strip_params Bi          (*params of subgoal i*)
    val paramTs = map #2 params
    and inc = maxidx+1
    fun liftvar (Var ((a,j), T)) =
          cterm_of sign (Var((a, j+inc), paramTs---> incr_tvar inc T))
      | liftvar t = raise TERM("Variable expected", [t]);
    (*lift only Var, not cterm! Must to be lifted already*)
    fun liftpair (v,ct) = (liftvar v, ct)
    fun lifttvar((a,i),ctyp) =
        let val {T,sign} = rep_ctyp ctyp
        in  ((a,i+inc), ctyp_of sign (incr_tvar inc T)) end
in instantiate (map lifttvar Tinsts, map liftpair insts)
               (lift_rule (st,i) rule)
end;

(*** Resolve after lifting and instantation; may refer to parameters of the
     subgoal.  Fails if "i" is out of range.  ***)

(*compose version: arguments are as for bicompose.*)
fun compose_inst_tac sinsts (bires_flg, rule, nsubgoal) i =
  STATE ( fn st => 
	   compose_tac (bires_flg, lift_inst_rule (st, i, sinsts, rule),
			nsubgoal) i
	   handle TERM (msg,_) => (writeln msg;  no_tac)
		| THM  (msg,_,_) => (writeln msg;  no_tac) );

(*"Resolve" version.  Note: res_inst_tac cannot behave sensibly if the
  terms that are substituted contain (term or type) unknowns from the
  goal, because it is unable to instantiate goal unknowns at the same time.

  The type checker is instructed not to freezes flexible type vars that
  were introduced during type inference and still remain in the term at the
  end.  This increases flexibility but can introduce schematic type vars in
  goals.
*)
fun res_inst_tac sinsts rule i =
    compose_inst_tac sinsts (false, rule, nprems_of rule) i;

(*eresolve elimination version*)
fun eres_inst_tac sinsts rule i =
    compose_inst_tac sinsts (true, rule, nprems_of rule) i;

(*For forw_inst_tac and dres_inst_tac.  Preserve Var indexes of rl;
  increment revcut_rl instead.*)
fun make_elim_preserve rl = 
  let val {maxidx,...} = rep_thm rl
      fun cvar ixn = cterm_of Sign.proto_pure (Var(ixn,propT));
      val revcut_rl' = 
	  instantiate ([],  [(cvar("V",0), cvar("V",maxidx+1)),
			     (cvar("W",0), cvar("W",maxidx+1))]) revcut_rl
      val arg = (false, rl, nprems_of rl)
      val [th] = Sequence.list_of_s (bicompose false arg 1 revcut_rl')
  in  th  end
  handle Bind => raise THM("make_elim_preserve", 1, [rl]);

(*instantiate and cut -- for a FACT, anyway...*)
fun cut_inst_tac sinsts rule = res_inst_tac sinsts (make_elim_preserve rule);

(*forward tactic applies a RULE to an assumption without deleting it*)
fun forw_inst_tac sinsts rule = cut_inst_tac sinsts rule THEN' assume_tac;

(*dresolve tactic applies a RULE to replace an assumption*)
fun dres_inst_tac sinsts rule = eres_inst_tac sinsts (make_elim_preserve rule);

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

(*"Cut" all facts from theorem list into the goal as assumptions. *)
fun cut_facts_tac ths i =
    EVERY (map (fn th => metacut_tac th i) (filter is_fact ths));

(*Introduce the given proposition as a lemma and subgoal*)
fun subgoal_tac sprop = res_inst_tac [("psi", sprop)] cut_rl;

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
val orderlist = untaglist o sort (fn(x,y)=> #1 x < #1 y); 

(*insert one tagged brl into the pair of nets*)
fun insert_tagged_brl (kbrl as (k,(eres,th)), (inet,enet)) =
    if eres then 
	case prems_of th of
	    prem::_ => (inet, Net.insert_term ((prem,kbrl), enet, K false))
	  | [] => error"insert_tagged_brl: elimination rule with no premises"
    else (Net.insert_term ((concl_of th, kbrl), inet, K false), enet);

(*build a pair of nets for biresolution*)
fun build_netpair netpair brls = 
    foldr insert_tagged_brl (taglist 1 brls, netpair);

(*delete one kbrl from the pair of nets;
  we don't know the value of k, so we use 0 and ignore it in the comparison*)
local
  fun eq_kbrl ((k,(eres,th)), (k',(eres',th'))) = eq_thm (th,th')
in
fun delete_tagged_brl (brl as (eres,th), (inet,enet)) =
    if eres then 
	case prems_of th of
	    prem::_ => (inet, Net.delete_term ((prem, (0,brl)), enet, eq_kbrl))
	  | [] => error"delete_brl: elimination rule with no premises"
    else (Net.delete_term ((concl_of th, (0,brl)), inet, eq_kbrl), enet);
end;


(*biresolution using a pair of nets rather than rules*)
fun biresolution_from_nets_tac match (inet,enet) =
  SUBGOAL
    (fn (prem,i) =>
      let val hyps = Logic.strip_assums_hyp prem
          and concl = Logic.strip_assums_concl prem 
          val kbrls = Net.unify_term inet concl @
                      flat (map (Net.unify_term enet) hyps)
      in PRIMSEQ (biresolution match (orderlist kbrls) i) end);

(*versions taking pre-built nets*)
val biresolve_from_nets_tac = biresolution_from_nets_tac false;
val bimatch_from_nets_tac = biresolution_from_nets_tac true;

(*fast versions using nets internally*)
val net_biresolve_tac =
    biresolve_from_nets_tac o build_netpair(Net.empty,Net.empty);

val net_bimatch_tac =
    bimatch_from_nets_tac o build_netpair(Net.empty,Net.empty);

(*** Simpler version for resolve_tac -- only one net, and no hyps ***)

(*insert one tagged rl into the net*)
fun insert_krl (krl as (k,th), net) =
    Net.insert_term ((concl_of th, krl), net, K false);

(*build a net of rules for resolution*)
fun build_net rls = 
    foldr insert_krl (taglist 1 rls, Net.empty);

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

fun result1 tacf mss thm =
  case Sequence.pull(tacf mss thm) of
    None => None
  | Some(thm,_) => Some(thm);

(*Rewrite subgoal i only *)
fun asm_rewrite_goal_tac mode prover_tac mss i =
      PRIMITIVE(rewrite_goal_rule mode (result1 prover_tac) mss i);

(*Rewrite throughout proof state. *)
fun rewrite_tac defs = PRIMITIVE(rewrite_rule defs);

(*Rewrite subgoals only, not main goal. *)
fun rewrite_goals_tac defs = PRIMITIVE (rewrite_goals_rule defs);

fun rewtac def = rewrite_goals_tac [def];


(*** for folding definitions, handling critical pairs ***)

(*The depth of nesting in a term*)
fun term_depth (Abs(a,T,t)) = 1 + term_depth t
  | term_depth (f$t) = 1 + max [term_depth f, term_depth t]
  | term_depth _ = 0;

val lhs_of_thm = #1 o Logic.dest_equals o #prop o rep_thm;

(*folding should handle critical pairs!  E.g. K == Inl(0),  S == Inr(Inl(0))
  Returns longest lhs first to avoid folding its subexpressions.*)
fun sort_lhs_depths defs =
  let val keylist = make_keylist (term_depth o lhs_of_thm) defs
      val keys = distinct (sort op> (map #2 keylist))
  in  map (keyfilter keylist) keys  end;

fun fold_tac defs = EVERY 
    (map rewrite_tac (sort_lhs_depths (map symmetric defs)));

fun fold_goals_tac defs = EVERY 
    (map rewrite_goals_tac (sort_lhs_depths (map symmetric defs)));


(*** Renaming of parameters in a subgoal
     Names may contain letters, digits or primes and must be
     separated by blanks ***)

(*Calling this will generate the warning "Same as previous level" since
  it affects nothing but the names of bound variables!*)
fun rename_tac str i = 
  let val cs = explode str 
  in  
  if !Logic.auto_rename 
  then (writeln"Note: setting Logic.auto_rename := false"; 
	Logic.auto_rename := false)
  else ();
  case #2 (take_prefix (is_letdig orf is_blank) cs) of
      [] => PRIMITIVE (rename_params_rule (scanwords is_letdig cs, i))
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

(*Prunes all redundant parameters from the proof state by rewriting*)
val prune_params_tac = rewrite_tac [triv_forall_equality];

(*rotate_tac n i: rotate the assumptions of subgoal i by n positions, from
  right to left if n is positive, and from left to right if n is negative.*)
fun rotate_tac n =
  let fun rot(n) = EVERY'(replicate n (dtac asm_rl));
  in if n >= 0 then rot n
     else SUBGOAL (fn (t,i) => rot(length(Logic.strip_assums_hyp t)+n) i)
  end;

end;

open Tactic;
