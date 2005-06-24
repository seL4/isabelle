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

(*raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

(*Permits forward proof from rules that discharge assumptions*)
fun forward_res nf st =
  case Seq.pull (ALLGOALS (METAHYPS (fn [prem] => rtac (nf prem) 1)) st)
  of SOME(th,_) => th
   | NONE => raise THM("forward_res", 0, [st]);


(*Are any of the constants in "bs" present in the term?*)
fun has_consts bs =
  let fun has (Const(a,_)) = a mem bs
	| has (Const ("Hilbert_Choice.Eps",_) $ _) = false
		     (*ignore constants within @-terms*)
	| has (f$u) = has f orelse has u
	| has (Abs(_,_,t)) = has t
	| has _ = false
  in  has  end;

(* for tracing: encloses each string element in brackets. *)
fun concat_with_and [] = ""
  | concat_with_and [x] = "(" ^ x ^ ")"
  | concat_with_and (x::xs) = "(" ^ x ^ ")" ^ " & " ^ concat_with_and xs;


(**** Clause handling ****)

fun literals (Const("Trueprop",_) $ P) = literals P
  | literals (Const("op |",_) $ P $ Q) = literals P @ literals Q
  | literals (Const("Not",_) $ P) = [(false,P)]
  | literals P = [(true,P)];

(*number of literals in a term*)
val nliterals = length o literals;

(*to detect, and remove, tautologous clauses*)
fun taut_lits [] = false
  | taut_lits ((flg,t)::ts) = (not flg,t) mem ts orelse taut_lits ts;

(*Include False as a literal: an occurrence of ~False is a tautology*)
fun is_taut th = taut_lits ((true, HOLogic.false_const) ::
			    literals (prop_of th));

(*Generation of unique names -- maxidx cannot be relied upon to increase!
  Cannot rely on "variant", since variables might coincide when literals
  are joined to make a clause...
  19 chooses "U" as the first variable name*)
val name_ref = ref 19;

(*Replaces universally quantified variables by FREE variables -- because
  assumptions may not contain scheme variables.  Later, call "generalize". *)
fun freeze_spec th =
  let val sth = th RS spec
      val newname = (name_ref := !name_ref + 1;
		     radixstring(26, "A", !name_ref))
  in  read_instantiate [("x", newname)] sth  end;

(*Used with METAHYPS below. There is one assumption, which gets bound to prem
  and then normalized via function nf. The normal form is given to resolve_tac,
  presumably to instantiate a Boolean variable.*)
fun resop nf [prem] = resolve_tac (nf prem) 1;

(*Conjunctive normal form, adding clauses from th in front of ths (for foldr).
  Detects tautologies early, with "seen" holding the other literals of a clause.
  Strips universal quantifiers and breaks up conjunctions.
  Eliminates existential quantifiers using skoths: Skolemization theorems.*)
fun cnf skoths (th,ths) =
  let fun cnf_aux seen (th,ths) =
        if taut_lits (literals(prop_of th) @ seen)  
	then ths     (*tautology ignored*)
	else if not (has_consts ["All","Ex","op &"] (prop_of th))  
	then th::ths (*no work to do, terminate*)
	else (*conjunction?*)
	      cnf_aux seen (th RS conjunct1,
			    cnf_aux seen (th RS conjunct2, ths))
	handle THM _ => (*universal quantifier?*)
	      cnf_aux seen (freeze_spec th,  ths)
	handle THM _ => (*existential quantifier? Insert Skolem functions.*)
	      cnf_aux seen (tryres (th,skoths), ths)
	handle THM _ => (*disjunction?*)
	  let val tac =
	      (METAHYPS (resop (cnf_nil seen)) 1) THEN
	     (fn st' => st' |>  
		METAHYPS (resop (cnf_nil (literals (concl_of st') @ seen))) 1)
	  in  Seq.list_of (tac (th RS disj_forward)) @ ths  end 
      and cnf_nil seen th = (cnf_aux seen (th,[]))
  in 
    name_ref := 19;  (*It's safe to reset this in a top-level call to cnf*)
    (cnf skoths (th RS conjunct1, cnf skoths (th RS conjunct2, ths))
     handle THM _ => (*not a conjunction*) cnf_aux [] (th, ths))
  end;

(*Convert all suitable free variables to schematic variables, 
  but don't discharge assumptions.*)
fun generalize th = Thm.varifyT (forall_elim_vars 0 (forall_intr_frees th));

fun make_cnf skoths th = map generalize (cnf skoths (th, []));


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

(*TAUTOLOGY CHECK SHOULD NOT BE NECESSARY!*)
fun sort_clauses ths =
    sort (make_ord fewerlits) (List.filter (not o is_taut) ths);

(*True if the given type contains bool anywhere*)
fun has_bool (Type("bool",_)) = true
  | has_bool (Type(_, Ts)) = exists has_bool Ts
  | has_bool _ = false;
  
(*Is the string the name of a connective? It doesn't matter if this list is
  incomplete, since when actually called, the only connectives likely to
  remain are & | Not.*)  
fun is_conn c = c mem_string
    ["Trueprop", "op &", "op |", "op -->", "op =", "Not", 
     "All", "Ex", "Ball", "Bex"];

(*True if the term contains a function where the type of any argument contains
  bool.*)
val has_bool_arg_const = 
    exists_Const
      (fn (c,T) => not(is_conn c) andalso exists (has_bool) (binder_types T));
      
val has_meta_conn = 
    exists_Const (fn (c,_) => c mem_string ["==", "==>", "all", "Goal"]);
  
(*Raises an exception if any Vars in the theorem mention type bool. That would mean
  they are higher-order, and in addition, they could cause make_horn to loop!
  Functions taking Boolean arguments are also rejected.*)
fun check_no_bool th =
  let val {prop,...} = rep_thm th
  in if exists (has_bool o fastype_of) (term_vars prop)  orelse
        has_bool_arg_const prop  orelse  
        has_meta_conn prop
  then raise THM ("check_no_bool", 0, [th]) else th
  end;

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
fun ins_term (net,t) = Net.insert_term((t,t), net, op aconv);

(*detects repetitions in a list of terms*)
fun has_reps [] = false
  | has_reps [_] = false
  | has_reps [t,u] = (t aconv u)
  | has_reps ts = (Library.foldl ins_term (Net.empty, ts);  false)
		  handle INSERT => true;

(*Like TRYALL eq_assume_tac, but avoids expensive THEN calls*)
fun TRYALL_eq_assume_tac 0 st = Seq.single st
  | TRYALL_eq_assume_tac i st =
       TRYALL_eq_assume_tac (i-1) (eq_assumption i st)
       handle THM _ => TRYALL_eq_assume_tac (i-1) st;

(*Loop checking: FAIL if trying to prove the same thing twice
  -- if *ANY* subgoal has repeated literals*)
fun check_tac st =
  if exists (fn prem => has_reps (rhyps(prem,[]))) (prems_of st)
  then  Seq.empty  else  Seq.single st;


(* net_resolve_tac actually made it slower... *)
fun prolog_step_tac horns i =
    (assume_tac i APPEND resolve_tac horns i) THEN check_tac THEN
    TRYALL eq_assume_tac;

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

(*The simplification removes defined quantifiers and occurrences of True and False.*)
val nnf_ss = HOL_basic_ss addsimps Ex1_def::Ball_def::Bex_def::simp_thms;

fun make_nnf th = th |> simplify nnf_ss
                     |> check_no_bool |> make_nnf1

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
      (gen_distinct Drule.eq_thm_prop (foldr (add_contras clause_rules) [] ths));

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

(*Shell of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions*)
fun MESON cltac = SELECT_GOAL
 (EVERY1 [rtac ccontr,
          METAHYPS (fn negs =>
                    EVERY1 [skolemize_prems_tac negs,
                            METAHYPS (cltac o make_clauses)])]);

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
	negated_asm_of_head (make_horn resolution_clause_rules (check_no_bool th));

fun make_meta_clauses ths =
    name_thms "MClause#"
      (gen_distinct Drule.eq_thm_prop (map make_meta_clause ths));

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
val skolemize_tac = 
  SUBGOAL
    (fn (prop,_) =>
     let val ts = Logic.strip_assums_hyp prop
     in EVERY1 
	 [METAHYPS
	    (fn hyps => (cut_facts_tac (map (skolemize o make_nnf) hyps) 1
                         THEN REPEAT (etac exE 1))),
	  REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);

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
 [Method.add_methods
  [("skolemize", Method.no_args skolemize_meth, 
    "Skolemization into existential quantifiers"),
   ("make_clauses", Method.no_args make_clauses_meth, 
    "Conversion to !!-quantified meta-level clauses")]];

end;

structure BasicMeson: BASIC_MESON = Meson;
open BasicMeson;
