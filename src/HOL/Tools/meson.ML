(*  Title:      HOL/Tools/meson.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The MESON resolution proof procedure for HOL.

When making clauses, avoids using the rewriter -- instead uses RS recursively

NEED TO SORT LITERALS BY # OF VARS, USING ==>I/E.  ELIMINATES NEED FOR
FUNCTION nodups -- if done to goal clauses too!
*)

signature BASIC_MESON =
sig
  val size_of_subgoals	: thm -> int
  val make_cnf		: thm list -> thm -> thm list
  val make_nnf		: thm -> thm
  val make_nnf1		: thm -> thm
  val skolemize		: thm -> thm
  val make_clauses	: thm list -> thm list
  val make_horns	: thm list -> thm list
  val best_prolog_tac	: (thm -> int) -> thm list -> tactic
  val depth_prolog_tac	: thm list -> tactic
  val gocls		: thm list -> thm list
  val skolemize_prems_tac	: thm list -> int -> tactic
  val MESON		: (thm list -> tactic) -> int -> tactic
  val best_meson_tac	: (thm -> int) -> int -> tactic
  val safe_best_meson_tac	: int -> tactic
  val depth_meson_tac	: int -> tactic
  val prolog_step_tac'	: thm list -> int -> tactic
  val iter_deepen_prolog_tac	: thm list -> tactic
  val iter_deepen_meson_tac	: thm list -> int -> tactic
  val meson_tac		: int -> tactic
  val negate_head	: thm -> thm
  val select_literal	: int -> thm -> thm
  val skolemize_tac	: int -> tactic
  val make_clauses_tac	: int -> tactic
  val check_is_fol_term : term -> term
end


structure Meson =
struct

val not_conjD = thm "meson_not_conjD";
val not_disjD = thm "meson_not_disjD";
val not_notD = thm "meson_not_notD";
val not_allD = thm "meson_not_allD";
val not_exD = thm "meson_not_exD";
val imp_to_disjD = thm "meson_imp_to_disjD";
val not_impD = thm "meson_not_impD";
val iff_to_disjD = thm "meson_iff_to_disjD";
val not_iffD = thm "meson_not_iffD";
val conj_exD1 = thm "meson_conj_exD1";
val conj_exD2 = thm "meson_conj_exD2";
val disj_exD = thm "meson_disj_exD";
val disj_exD1 = thm "meson_disj_exD1";
val disj_exD2 = thm "meson_disj_exD2";
val disj_assoc = thm "meson_disj_assoc";
val disj_comm = thm "meson_disj_comm";
val disj_FalseD1 = thm "meson_disj_FalseD1";
val disj_FalseD2 = thm "meson_disj_FalseD2";

val depth_limit = ref 2000;

(**** Operators for forward proof ****)

(*Like RS, but raises Option if there are no unifiers and allows multiple unifiers.*)
fun resolve1 (tha,thb) = Seq.hd (biresolution false [(false,tha)] 1 thb);

(*raises exception if no rules apply -- unlike RL*)
fun tryres (th, rls) = 
  let fun tryall [] = raise THM("tryres", 0, th::rls)
        | tryall (rl::rls) = (resolve1(th,rl) handle Option.Option => tryall rls)
  in  tryall rls  end;
  
(*Permits forward proof from rules that discharge assumptions*)
fun forward_res nf st =
  case Seq.pull (ALLGOALS (METAHYPS (fn [prem] => rtac (nf prem) 1)) st)
  of SOME(th,_) => th
   | NONE => raise THM("forward_res", 0, [st]);


(*Are any of the constants in "bs" present in the term?*)
fun has_consts bs =
  let fun has (Const(a,_)) = member (op =) bs a
	| has (Const ("Hilbert_Choice.Eps",_) $ _) = false
		     (*ignore constants within @-terms*)
	| has (f$u) = has f orelse has u
	| has (Abs(_,_,t)) = has t
	| has _ = false
  in  has  end;
  

(**** Clause handling ****)

fun literals (Const("Trueprop",_) $ P) = literals P
  | literals (Const("op |",_) $ P $ Q) = literals P @ literals Q
  | literals (Const("Not",_) $ P) = [(false,P)]
  | literals P = [(true,P)];

(*number of literals in a term*)
val nliterals = length o literals;


(*** Tautology Checking ***)

fun signed_lits_aux (Const ("op |", _) $ P $ Q) (poslits, neglits) = 
      signed_lits_aux Q (signed_lits_aux P (poslits, neglits))
  | signed_lits_aux (Const("Not",_) $ P) (poslits, neglits) = (poslits, P::neglits)
  | signed_lits_aux P (poslits, neglits) = (P::poslits, neglits);
  
fun signed_lits th = signed_lits_aux (HOLogic.dest_Trueprop (concl_of th)) ([],[]);

(*Literals like X=X are tautologous*)
fun taut_poslit (Const("op =",_) $ t $ u) = t aconv u
  | taut_poslit (Const("True",_)) = true
  | taut_poslit _ = false;

fun is_taut th =
  let val (poslits,neglits) = signed_lits th
  in  exists taut_poslit poslits
      orelse
      exists (fn t => mem_term (t, neglits)) (HOLogic.false_const :: poslits)
  end
  handle TERM _ => false;	(*probably dest_Trueprop on a weird theorem*)		      


(*** To remove trivial negated equality literals from clauses ***)

(*They are typically functional reflexivity axioms and are the converses of
  injectivity equivalences*)
  
val not_refl_disj_D = thm"meson_not_refl_disj_D";

fun refl_clause_aux 0 th = th
  | refl_clause_aux n th =
       case HOLogic.dest_Trueprop (concl_of th) of
	  (Const ("op |", _) $ (Const ("op |", _) $ _ $ _) $ _) => 
            refl_clause_aux n (th RS disj_assoc)    (*isolate an atom as first disjunct*)
	| (Const ("op |", _) $ (Const("Not",_) $ (Const("op =",_) $ t $ u)) $ _) => 
	    if is_Var t orelse is_Var u then (*Var inequation: delete or ignore*)
		(refl_clause_aux (n-1) (th RS not_refl_disj_D)    (*delete*)
		 handle THM _ => refl_clause_aux (n-1) (th RS disj_comm))  (*ignore*)
	    else refl_clause_aux (n-1) (th RS disj_comm)  (*not between Vars: ignore*)
	| (Const ("op |", _) $ _ $ _) => refl_clause_aux n (th RS disj_comm)
	| _ => (*not a disjunction*) th;

fun notequal_lits_count (Const ("op |", _) $ P $ Q) = 
      notequal_lits_count P + notequal_lits_count Q
  | notequal_lits_count (Const("Not",_) $ (Const("op =",_) $ _ $ _)) = 1
  | notequal_lits_count _ = 0;

(*Simplify a clause by applying reflexivity to its negated equality literals*)
fun refl_clause th = 
  let val neqs = notequal_lits_count (HOLogic.dest_Trueprop (concl_of th))
  in  zero_var_indexes (refl_clause_aux neqs th)  end
  handle TERM _ => th;	(*probably dest_Trueprop on a weird theorem*)		      


(*** The basic CNF transformation ***)

(*Estimate the number of clauses in order to detect infeasible theorems*)
fun nclauses (Const("Trueprop",_) $ t) = nclauses t
  | nclauses (Const("op &",_) $ t $ u) = nclauses t + nclauses u
  | nclauses (Const("Ex", _) $ Abs (_,_,t)) = nclauses t
  | nclauses (Const("All",_) $ Abs (_,_,t)) = nclauses t
  | nclauses (Const("op |",_) $ t $ u) = nclauses t * nclauses u
  | nclauses _ = 1; (* literal *)

(*Replaces universally quantified variables by FREE variables -- because
  assumptions may not contain scheme variables.  Later, call "generalize". *)
fun freeze_spec th =
  let val newname = gensym "A_"
      val spec' = read_instantiate [("x", newname)] spec
  in  th RS spec'  end;

(*Used with METAHYPS below. There is one assumption, which gets bound to prem
  and then normalized via function nf. The normal form is given to resolve_tac,
  presumably to instantiate a Boolean variable.*)
fun resop nf [prem] = resolve_tac (nf prem) 1;

val has_meta_conn = 
    exists_Const (fn (c,_) => c mem_string ["==", "==>", "all", "prop"]);
  
(*Conjunctive normal form, adding clauses from th in front of ths (for foldr).
  Strips universal quantifiers and breaks up conjunctions.
  Eliminates existential quantifiers using skoths: Skolemization theorems.*)
fun cnf skoths (th,ths) =
  let fun cnf_aux (th,ths) =
  	if has_meta_conn (prop_of th) then ths (*meta-level: ignore*)
        else if not (has_consts ["All","Ex","op &"] (prop_of th))  
	then th::ths (*no work to do, terminate*)
	else case head_of (HOLogic.dest_Trueprop (concl_of th)) of
	    Const ("op &", _) => (*conjunction*)
		cnf_aux (th RS conjunct1,
			      cnf_aux (th RS conjunct2, ths))
	  | Const ("All", _) => (*universal quantifier*)
	        cnf_aux (freeze_spec th,  ths)
	  | Const ("Ex", _) => 
	      (*existential quantifier: Insert Skolem functions*)
	      cnf_aux (tryres (th,skoths), ths)
	  | Const ("op |", _) => (*disjunction*)
	      let val tac =
		  (METAHYPS (resop cnf_nil) 1) THEN
		   (fn st' => st' |> METAHYPS (resop cnf_nil) 1)
	      in  Seq.list_of (tac (th RS disj_forward)) @ ths  end 
	  | _ => (*no work to do*) th::ths 
      and cnf_nil th = cnf_aux (th,[])
  in 
    if nclauses (concl_of th) > 20 
    then (Output.debug ("cnf is ignoring: " ^ string_of_thm th); ths)
    else cnf_aux (th,ths)
  end;

(*Convert all suitable free variables to schematic variables, 
  but don't discharge assumptions.*)
fun generalize th = Thm.varifyT (forall_elim_vars 0 (forall_intr_frees th));

fun make_cnf skoths th = 
  filter (not o is_taut) 
    (map (refl_clause o generalize) (cnf skoths (th, [])));


(**** Removal of duplicate literals ****)

(*Forward proof, passing extra assumptions as theorems to the tactic*)
fun forward_res2 nf hyps st =
  case Seq.pull
	(REPEAT
	 (METAHYPS (fn major::minors => rtac (nf (minors@hyps) major) 1) 1)
	 st)
  of SOME(th,_) => th
   | NONE => raise THM("forward_res2", 0, [st]);

(*Remove duplicates in P|Q by assuming ~P in Q
  rls (initially []) accumulates assumptions of the form P==>False*)
fun nodups_aux rls th = nodups_aux rls (th RS disj_assoc)
    handle THM _ => tryres(th,rls)
    handle THM _ => tryres(forward_res2 nodups_aux rls (th RS disj_forward2),
			   [disj_FalseD1, disj_FalseD2, asm_rl])
    handle THM _ => th;

(*Remove duplicate literals, if there are any*)
fun nodups th =
    if null(findrep(literals(prop_of th))) then th
    else nodups_aux [] th;


(**** Generation of contrapositives ****)

(*Associate disjuctions to right -- make leftmost disjunct a LITERAL*)
fun assoc_right th = assoc_right (th RS disj_assoc)
	handle THM _ => th;

(*Must check for negative literal first!*)
val clause_rules = [disj_assoc, make_neg_rule, make_pos_rule];

(*For ordinary resolution. *)
val resolution_clause_rules = [disj_assoc, make_neg_rule', make_pos_rule'];

(*Create a goal or support clause, conclusing False*)
fun make_goal th =   (*Must check for negative literal first!*)
    make_goal (tryres(th, clause_rules))
  handle THM _ => tryres(th, [make_neg_goal, make_pos_goal]);

(*Sort clauses by number of literals*)
fun fewerlits(th1,th2) = nliterals(prop_of th1) < nliterals(prop_of th2);

fun sort_clauses ths = sort (make_ord fewerlits) ths;

(*True if the given type contains bool anywhere*)
fun has_bool (Type("bool",_)) = true
  | has_bool (Type(_, Ts)) = exists has_bool Ts
  | has_bool _ = false;
  
(*Is the string the name of a connective? It doesn't matter if this list is
  incomplete, since when actually called, the only connectives likely to
  remain are & | Not.*)  
val is_conn = member (op =)
    ["Trueprop", "HOL.tag", "op &", "op |", "op -->", "op =", "Not", 
     "All", "Ex", "Ball", "Bex"];

(*True if the term contains a function where the type of any argument contains
  bool.*)
val has_bool_arg_const = 
    exists_Const
      (fn (c,T) => not(is_conn c) andalso exists (has_bool) (binder_types T));
      
(*Raises an exception if any Vars in the theorem mention type bool; they
  could cause make_horn to loop! Also rejects functions whose arguments are 
  Booleans or other functions.*)
fun is_fol_term t =
    not (exists (has_bool o fastype_of) (term_vars t)  orelse
	 not (Term.is_first_order ["all","All","Ex"] t) orelse
	 has_bool_arg_const t  orelse  
	 has_meta_conn t);

(*FIXME: replace this by the boolean-valued version above!*)
fun check_is_fol_term t =
    if is_fol_term t then t else raise TERM("check_is_fol_term",[t]);

fun check_is_fol th = (check_is_fol_term (prop_of th); th);


(*Create a meta-level Horn clause*)
fun make_horn crules th = make_horn crules (tryres(th,crules))
			  handle THM _ => th;

(*Generate Horn clauses for all contrapositives of a clause. The input, th,
  is a HOL disjunction.*)
fun add_contras crules (th,hcs) =
  let fun rots (0,th) = hcs
	| rots (k,th) = zero_var_indexes (make_horn crules th) ::
			rots(k-1, assoc_right (th RS disj_comm))
  in case nliterals(prop_of th) of
	1 => th::hcs
      | n => rots(n, assoc_right th)
  end;

(*Use "theorem naming" to label the clauses*)
fun name_thms label =
    let fun name1 (th, (k,ths)) =
	  (k-1, Thm.name_thm (label ^ string_of_int k, th) :: ths)

    in  fn ths => #2 (foldr name1 (length ths, []) ths)  end;

(*Is the given disjunction an all-negative support clause?*)
fun is_negative th = forall (not o #1) (literals (prop_of th));

val neg_clauses = List.filter is_negative;


(***** MESON PROOF PROCEDURE *****)

fun rhyps (Const("==>",_) $ (Const("Trueprop",_) $ A) $ phi,
	   As) = rhyps(phi, A::As)
  | rhyps (_, As) = As;

(** Detecting repeated assumptions in a subgoal **)

(*The stringtree detects repeated assumptions.*)
fun ins_term (net,t) = Net.insert_term (op aconv) (t,t) net;

(*detects repetitions in a list of terms*)
fun has_reps [] = false
  | has_reps [_] = false
  | has_reps [t,u] = (t aconv u)
  | has_reps ts = (Library.foldl ins_term (Net.empty, ts);  false)
		  handle Net.INSERT => true;

(*Like TRYALL eq_assume_tac, but avoids expensive THEN calls*)
fun TRYING_eq_assume_tac 0 st = Seq.single st
  | TRYING_eq_assume_tac i st =
       TRYING_eq_assume_tac (i-1) (eq_assumption i st)
       handle THM _ => TRYING_eq_assume_tac (i-1) st;

fun TRYALL_eq_assume_tac st = TRYING_eq_assume_tac (nprems_of st) st;

(*Loop checking: FAIL if trying to prove the same thing twice
  -- if *ANY* subgoal has repeated literals*)
fun check_tac st =
  if exists (fn prem => has_reps (rhyps(prem,[]))) (prems_of st)
  then  Seq.empty  else  Seq.single st;


(* net_resolve_tac actually made it slower... *)
fun prolog_step_tac horns i =
    (assume_tac i APPEND resolve_tac horns i) THEN check_tac THEN
    TRYALL_eq_assume_tac;

(*Sums the sizes of the subgoals, ignoring hypotheses (ancestors)*)
fun addconcl(prem,sz) = size_of_term(Logic.strip_assums_concl prem) + sz

fun size_of_subgoals st = foldr addconcl 0 (prems_of st);


(*Negation Normal Form*)
val nnf_rls = [imp_to_disjD, iff_to_disjD, not_conjD, not_disjD,
               not_impD, not_iffD, not_allD, not_exD, not_notD];

fun make_nnf1 th = make_nnf1 (tryres(th, nnf_rls))
    handle THM _ =>
        forward_res make_nnf1
           (tryres(th, [conj_forward,disj_forward,all_forward,ex_forward]))
    handle THM _ => th;

(*The simplification removes defined quantifiers and occurrences of True and False, 
  as well as tags applied to True and False. nnf_ss also includes the one-point simprocs,
  which are needed to avoid the various one-point theorems from generating junk clauses.*)
val tag_True = thm "tag_True";
val tag_False = thm "tag_False";
val nnf_simps =
     [simp_implies_def, Ex1_def, Ball_def, Bex_def, tag_True, tag_False, if_True, 
      if_False, if_cancel, if_eq_cancel, cases_simp];
val nnf_extra_simps =
      thms"split_ifs" @ ex_simps @ all_simps @ simp_thms;

val nnf_ss =
    HOL_basic_ss addsimps nnf_extra_simps 
                 addsimprocs [defALL_regroup,defEX_regroup,neq_simproc,let_simproc];

fun make_nnf th = th |> rewrite_rule (map safe_mk_meta_eq nnf_simps)
                     |> simplify nnf_ss  (*But this doesn't simplify premises...*)
                     |> make_nnf1

(*Pull existential quantifiers to front. This accomplishes Skolemization for
  clauses that arise from a subgoal.*)
fun skolemize th =
  if not (has_consts ["Ex"] (prop_of th)) then th
  else (skolemize (tryres(th, [choice, conj_exD1, conj_exD2,
                              disj_exD, disj_exD1, disj_exD2])))
    handle THM _ =>
        skolemize (forward_res skolemize
                   (tryres (th, [conj_forward, disj_forward, all_forward])))
    handle THM _ => forward_res skolemize (th RS ex_forward);


(*Make clauses from a list of theorems, previously Skolemized and put into nnf.
  The resulting clauses are HOL disjunctions.*)
fun make_clauses ths =
    (sort_clauses (map (generalize o nodups) (foldr (cnf[]) [] ths)));


(*Convert a list of clauses (disjunctions) to Horn clauses (contrapositives)*)
fun make_horns ths =
    name_thms "Horn#"
      (distinct Drule.eq_thm_prop (foldr (add_contras clause_rules) [] ths));

(*Could simply use nprems_of, which would count remaining subgoals -- no
  discrimination as to their size!  With BEST_FIRST, fails for problem 41.*)

fun best_prolog_tac sizef horns =
    BEST_FIRST (has_fewer_prems 1, sizef) (prolog_step_tac horns 1);

fun depth_prolog_tac horns =
    DEPTH_FIRST (has_fewer_prems 1) (prolog_step_tac horns 1);

(*Return all negative clauses, as possible goal clauses*)
fun gocls cls = name_thms "Goal#" (map make_goal (neg_clauses cls));

fun skolemize_prems_tac prems =
    cut_facts_tac (map (skolemize o make_nnf) prems)  THEN'
    REPEAT o (etac exE);

(*Expand all definitions (presumably of Skolem functions) in a proof state.*)
fun expand_defs_tac st =
  let val defs = filter (can dest_equals) (#hyps (crep_thm st))
  in  LocalDefs.def_export false defs st  end;

(*Basis of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions*)
fun MESON cltac i st = 
  SELECT_GOAL
    (EVERY [rtac ccontr 1,
	    METAHYPS (fn negs =>
		      EVERY1 [skolemize_prems_tac negs,
			      METAHYPS (cltac o make_clauses)]) 1,
            expand_defs_tac]) i st
  handle TERM _ => no_tac st;	(*probably from check_is_fol*)		      

(** Best-first search versions **)

(*ths is a list of additional clauses (HOL disjunctions) to use.*)
fun best_meson_tac sizef =
  MESON (fn cls =>
         THEN_BEST_FIRST (resolve_tac (gocls cls) 1)
                         (has_fewer_prems 1, sizef)
                         (prolog_step_tac (make_horns cls) 1));

(*First, breaks the goal into independent units*)
val safe_best_meson_tac =
     SELECT_GOAL (TRY Safe_tac THEN
                  TRYALL (best_meson_tac size_of_subgoals));

(** Depth-first search version **)

val depth_meson_tac =
     MESON (fn cls => EVERY [resolve_tac (gocls cls) 1,
                             depth_prolog_tac (make_horns cls)]);


(** Iterative deepening version **)

(*This version does only one inference per call;
  having only one eq_assume_tac speeds it up!*)
fun prolog_step_tac' horns =
    let val (horn0s, hornps) = (*0 subgoals vs 1 or more*)
            take_prefix Thm.no_prems horns
        val nrtac = net_resolve_tac horns
    in  fn i => eq_assume_tac i ORELSE
                match_tac horn0s i ORELSE  (*no backtracking if unit MATCHES*)
                ((assume_tac i APPEND nrtac i) THEN check_tac)
    end;

fun iter_deepen_prolog_tac horns =
    ITER_DEEPEN (has_fewer_prems 1) (prolog_step_tac' horns);

fun iter_deepen_meson_tac ths =
  MESON (fn cls =>
           case (gocls (cls@ths)) of
           	[] => no_tac  (*no goal clauses*)
              | goes => 
		 (THEN_ITER_DEEPEN (resolve_tac goes 1)
				   (has_fewer_prems 1)
				   (prolog_step_tac' (make_horns (cls@ths)))));

fun meson_claset_tac ths cs =
  SELECT_GOAL (TRY (safe_tac cs) THEN TRYALL (iter_deepen_meson_tac ths));

val meson_tac = CLASET' (meson_claset_tac []);


(**** Code to support ordinary resolution, rather than Model Elimination ****)

(*Convert a list of clauses (disjunctions) to meta-level clauses (==>), 
  with no contrapositives, for ordinary resolution.*)

(*Rules to convert the head literal into a negated assumption. If the head
  literal is already negated, then using notEfalse instead of notEfalse'
  prevents a double negation.*)
val notEfalse = read_instantiate [("R","False")] notE;
val notEfalse' = rotate_prems 1 notEfalse;

fun negated_asm_of_head th = 
    th RS notEfalse handle THM _ => th RS notEfalse';

(*Converting one clause*)
fun make_meta_clause th = 
    negated_asm_of_head (make_horn resolution_clause_rules (check_is_fol th));

fun make_meta_clauses ths =
    name_thms "MClause#"
      (distinct Drule.eq_thm_prop (map make_meta_clause ths));

(*Permute a rule's premises to move the i-th premise to the last position.*)
fun make_last i th =
  let val n = nprems_of th 
  in  if 1 <= i andalso i <= n 
      then Thm.permute_prems (i-1) 1 th
      else raise THM("select_literal", i, [th])
  end;

(*Maps a rule that ends "... ==> P ==> False" to "... ==> ~P" while suppressing
  double-negations.*)
val negate_head = rewrite_rule [atomize_not, not_not RS eq_reflection];

(*Maps the clause  [P1,...Pn]==>False to [P1,...,P(i-1),P(i+1),...Pn] ==> ~P*)
fun select_literal i cl = negate_head (make_last i cl);


(*Top-level Skolemization. Allows part of the conversion to clauses to be
  expressed as a tactic (or Isar method).  Each assumption of the selected 
  goal is converted to NNF and then its existential quantifiers are pulled
  to the front. Finally, all existential quantifiers are eliminated, 
  leaving !!-quantified variables. Perhaps Safe_tac should follow, but it
  might generate many subgoals.*)

fun skolemize_tac i st = 
  let val ts = Logic.strip_assums_hyp (List.nth (prems_of st, i-1))
  in 
     EVERY' [METAHYPS
	    (fn hyps => (cut_facts_tac (map (skolemize o make_nnf) hyps) 1
                         THEN REPEAT (etac exE 1))),
            REPEAT_DETERM_N (length ts) o (etac thin_rl)] i st
  end
  handle Subscript => Seq.empty;

(*Top-level conversion to meta-level clauses. Each clause has  
  leading !!-bound universal variables, to express generality. To get 
  disjunctions instead of meta-clauses, remove "make_meta_clauses" below.*)
val make_clauses_tac = 
  SUBGOAL
    (fn (prop,_) =>
     let val ts = Logic.strip_assums_hyp prop
     in EVERY1 
	 [METAHYPS
	    (fn hyps => 
              (Method.insert_tac
                (map forall_intr_vars 
                  (make_meta_clauses (make_clauses hyps))) 1)),
	  REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);
     
     
(*** setup the special skoklemization methods ***)

(*No CHANGED_PROP here, since these always appear in the preamble*)

val skolemize_meth = Method.SIMPLE_METHOD' HEADGOAL skolemize_tac;

val make_clauses_meth = Method.SIMPLE_METHOD' HEADGOAL make_clauses_tac;

val skolemize_setup =
  Method.add_methods
    [("skolemize", Method.no_args skolemize_meth, 
      "Skolemization into existential quantifiers"),
     ("make_clauses", Method.no_args make_clauses_meth, 
      "Conversion to !!-quantified meta-level clauses")];

end;

structure BasicMeson: BASIC_MESON = Meson;
open BasicMeson;
