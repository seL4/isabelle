(*  Title:      HOL/ex/meson
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The MESON resolution proof procedure for HOL

When making clauses, avoids using the rewriter -- instead uses RS recursively
*)

writeln"File HOL/ex/meson.";

(*Prove theorems using fast_tac*)
fun prove_fun s = 
    prove_goal HOL.thy s
         (fn prems => [ cut_facts_tac prems 1, fast_tac HOL_cs 1 ]);

(**** Negation Normal Form ****)

(*** de Morgan laws ***)

val not_conjD = prove_fun "~(P&Q) ==> ~P | ~Q";
val not_disjD = prove_fun "~(P|Q) ==> ~P & ~Q";
val not_notD = prove_fun "~~P ==> P";
val not_allD = prove_fun  "~(! x.P(x)) ==> ? x. ~P(x)";
val not_exD = prove_fun   "~(? x.P(x)) ==> ! x. ~P(x)";


(*** Removal of --> and <-> (positive and negative occurrences) ***)

val imp_to_disjD = prove_fun "P-->Q ==> ~P | Q";
val not_impD = prove_fun   "~(P-->Q) ==> P & ~Q";

val iff_to_disjD = prove_fun "P=Q ==> (~P | Q) & (~Q | P)";

(*Much more efficient than (P & ~Q) | (Q & ~P) for computing CNF*)
val not_iffD = prove_fun "~(P=Q) ==> (P | Q) & (~P | ~Q)";


(**** Pulling out the existential quantifiers ****)

(*** Conjunction ***)

val conj_exD1 = prove_fun "(? x.P(x)) & Q ==> ? x. P(x) & Q";
val conj_exD2 = prove_fun "P & (? x.Q(x)) ==> ? x. P & Q(x)";

(*** Disjunction ***)

(*DO NOT USE with forall-Skolemization: makes fewer schematic variables!!
  With ex-Skolemization, makes fewer Skolem constants*)
val disj_exD = prove_fun "(? x.P(x)) | (? x.Q(x)) ==> ? x. P(x) | Q(x)";

val disj_exD1 = prove_fun "(? x.P(x)) | Q ==> ? x. P(x) | Q";
val disj_exD2 = prove_fun "P | (? x.Q(x)) ==> ? x. P | Q(x)";


(**** Skolemization -- pulling "?" over "!" ****)

(*"Axiom" of Choice, proved using the description operator*)
val [major] = goal HOL.thy
    "! x. ? y. Q x y ==> ? f. ! x. Q x (f x)";
by (cut_facts_tac [major] 1);
by (fast_tac (HOL_cs addEs [selectI]) 1);
qed "choice";


(***** Generating clauses for the Meson Proof Procedure *****)

(*** Disjunctions ***)

val disj_assoc = prove_fun "(P|Q)|R ==> P|(Q|R)";

val disj_comm = prove_fun "P|Q ==> Q|P";

val disj_FalseD1 = prove_fun "False|P ==> P";
val disj_FalseD2 = prove_fun "P|False ==> P";

(*** Generation of contrapositives ***)

(*Inserts negated disjunct after removing the negation; P is a literal*)
val [major,minor] = goal HOL.thy "~P|Q ==> ((~P==>P) ==> Q)";
by (rtac (major RS disjE) 1);
by (rtac notE 1);
by (etac minor 2);
by (ALLGOALS assume_tac);
qed "make_neg_rule";

(*For Plaisted's "Postive refinement" of the MESON procedure*)
val [major,minor] = goal HOL.thy "~P|Q ==> (P ==> Q)";
by (rtac (major RS disjE) 1);
by (rtac notE 1);
by (rtac minor 2);
by (ALLGOALS assume_tac);
qed "make_refined_neg_rule";

(*P should be a literal*)
val [major,minor] = goal HOL.thy "P|Q ==> ((P==>~P) ==> Q)";
by (rtac (major RS disjE) 1);
by (rtac notE 1);
by (etac minor 1);
by (ALLGOALS assume_tac);
qed "make_pos_rule";

(*** Generation of a goal clause -- put away the final literal ***)

val [major,minor] = goal HOL.thy "~P ==> ((~P==>P) ==> False)";
by (rtac notE 1);
by (rtac minor 2);
by (ALLGOALS (rtac major));
qed "make_neg_goal";

val [major,minor] = goal HOL.thy "P ==> ((P==>~P) ==> False)";
by (rtac notE 1);
by (rtac minor 1);
by (ALLGOALS (rtac major));
qed "make_pos_goal";


(**** Lemmas for forward proof (like congruence rules) ****)

(*NOTE: could handle conjunctions (faster?) by
    nf(th RS conjunct2) RS (nf(th RS conjunct1) RS conjI) *)
val major::prems = goal HOL.thy
    "[| P'&Q';  P' ==> P;  Q' ==> Q |] ==> P&Q";
by (rtac (major RS conjE) 1);
by (rtac conjI 1);
by (ALLGOALS (eresolve_tac prems));
qed "conj_forward";

val major::prems = goal HOL.thy
    "[| P'|Q';  P' ==> P;  Q' ==> Q |] ==> P|Q";
by (rtac (major RS disjE) 1);
by (ALLGOALS (dresolve_tac prems));
by (ALLGOALS (eresolve_tac [disjI1,disjI2]));
qed "disj_forward";

val major::prems = goal HOL.thy
    "[| ! x. P'(x);  !!x. P'(x) ==> P(x) |] ==> ! x. P(x)";
by (rtac allI 1);
by (resolve_tac prems 1);
by (rtac (major RS spec) 1);
qed "all_forward";

val major::prems = goal HOL.thy
    "[| ? x. P'(x);  !!x. P'(x) ==> P(x) |] ==> ? x. P(x)";
by (rtac (major RS exE) 1);
by (rtac exI 1);
by (eresolve_tac prems 1);
qed "ex_forward";


(**** Operators for forward proof ****)

(*raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

val prop_of = #prop o rep_thm;

(*Permits forward proof from rules that discharge assumptions*)
fun forward_res nf st =
  case Sequence.pull (ALLGOALS (METAHYPS (fn [prem] => rtac (nf prem) 1)) st)
  of Some(th,_) => th
   | None => raise THM("forward_res", 0, [st]);


(*Negation Normal Form*)
val nnf_rls = [imp_to_disjD, iff_to_disjD, not_conjD, not_disjD,
               not_impD, not_iffD, not_allD, not_exD, not_notD];
fun make_nnf th = make_nnf (tryres(th, nnf_rls))
    handle THM _ => 
        forward_res make_nnf
           (tryres(th, [conj_forward,disj_forward,all_forward,ex_forward]))
    handle THM _ => th;


(*Are any of the constants in "bs" present in the term?*)
fun has_consts bs = 
  let fun has (Const(a,_)) = a mem bs
        | has (f$u) = has f orelse has u
        | has (Abs(_,_,t)) = has t
        | has _ = false
  in  has  end;

(*Pull existential quantifiers (Skolemization)*)
fun skolemize th = 
  if not (has_consts ["Ex"] (prop_of th)) then th
  else skolemize (tryres(th, [choice, conj_exD1, conj_exD2,
			      disj_exD, disj_exD1, disj_exD2]))
    handle THM _ => 
        skolemize (forward_res skolemize
		   (tryres (th, [conj_forward, disj_forward, all_forward])))
    handle THM _ => forward_res skolemize (th RS ex_forward);


(**** Clause handling ****)

fun literals (Const("Trueprop",_) $ P) = literals P
  | literals (Const("op |",_) $ P $ Q) = literals P @ literals Q
  | literals (Const("not",_) $ P) = [(false,P)]
  | literals P = [(true,P)];

(*number of literals in a term*)
val nliterals = length o literals;

(*to delete tautologous clauses*)
fun taut_lits [] = false
  | taut_lits ((flg,t)::ts) = (not flg,t) mem ts orelse taut_lits ts;

val is_taut = taut_lits o literals o prop_of;


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

fun resop nf [prem] = resolve_tac (nf prem) 1;

(*Conjunctive normal form, detecting tautologies early.
  Strips universal quantifiers and breaks up conjunctions. *)
fun cnf_aux seen (th,ths) = 
  if taut_lits (literals(prop_of th) @ seen)  then ths
  else if not (has_consts ["All","op &"] (prop_of th))  then th::ths
  else (*conjunction?*)
        cnf_aux seen (th RS conjunct1, 
                      cnf_aux seen (th RS conjunct2, ths))
  handle THM _ => (*universal quant?*)
        cnf_aux  seen (freeze_spec th,  ths)
  handle THM _ => (*disjunction?*)
    let val tac = 
        (METAHYPS (resop (cnf_nil seen)) 1) THEN
        (STATE (fn st' => 
                METAHYPS (resop (cnf_nil (literals (concl_of st') @ seen))) 1))
    in  Sequence.list_of_s (tac (th RS disj_forward)) @ ths  end
and cnf_nil seen th = cnf_aux seen (th,[]);

(*Top-level call to cnf -- it's safe to reset name_ref*)
fun cnf (th,ths) = 
   (name_ref := 19;  cnf (th RS conjunct1, cnf (th RS conjunct2, ths))
    handle THM _ => (*not a conjunction*) cnf_aux [] (th, ths));

(**** Removal of duplicate literals ****)

(*Version for removal of duplicate literals*)
val major::prems = goal HOL.thy
    "[| P'|Q';  P' ==> P;  [| Q'; P==>False |] ==> Q |] ==> P|Q";
by (rtac (major RS disjE) 1);
by (rtac disjI1 1);
by (rtac (disjCI RS disj_comm) 2);
by (ALLGOALS (eresolve_tac prems));
by (etac notE 1);
by (assume_tac 1);
qed "disj_forward2";

(*Forward proof, passing extra assumptions as theorems to the tactic*)
fun forward_res2 nf hyps st =
  case Sequence.pull
        (REPEAT 
	 (METAHYPS (fn major::minors => rtac (nf (minors@hyps) major) 1) 1) 
	 st)
  of Some(th,_) => th
   | None => raise THM("forward_res2", 0, [st]);

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
val refined_clause_rules = [disj_assoc, make_refined_neg_rule, make_pos_rule];

(*Create a goal or support clause, conclusing False*)
fun make_goal th =   (*Must check for negative literal first!*)
    make_goal (tryres(th, clause_rules)) 
  handle THM _ => tryres(th, [make_neg_goal, make_pos_goal]);

(*Sort clauses by number of literals*)
fun fewerlits(th1,th2) = nliterals(prop_of th1) < nliterals(prop_of th2);

(*TAUTOLOGY CHECK SHOULD NOT BE NECESSARY!*)
fun sort_clauses ths = sort fewerlits (filter (not o is_taut) ths);

(*Convert all suitable free variables to schematic variables*)
fun generalize th = forall_elim_vars 0 (forall_intr_frees th);

(*make clauses from a list of theorems*)
fun make_clauses ths = 
    sort_clauses (map (generalize o nodups) (foldr cnf (ths,[])));

(*Create a Horn clause*)
fun make_horn crules th = make_horn crules (tryres(th,crules)) 
                          handle THM _ => th;

(*Generate Horn clauses for all contrapositives of a clause*)
fun add_contras crules (th,hcs) = 
  let fun rots (0,th) = hcs
        | rots (k,th) = zero_var_indexes (make_horn crules th) ::
                        rots(k-1, assoc_right (th RS disj_comm))
  in case nliterals(prop_of th) of
        1 => th::hcs
      | n => rots(n, assoc_right th)
  end;

(*Convert a list of clauses to (contrapositive) Horn clauses*)
fun make_horns ths = foldr (add_contras clause_rules) (ths,[]);

(*Find an all-negative support clause*)
fun is_negative th = forall (not o #1) (literals (prop_of th));

val neg_clauses = filter is_negative;


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
  | has_reps ts = (foldl ins_term (Net.empty, ts);  false)
                  handle INSERT => true; 

(*Loop checking: FAIL if trying to prove the same thing twice
  -- repeated literals*)
val check_tac = SUBGOAL (fn (prem,_) =>
  if has_reps (rhyps(prem,[]))  then  no_tac  else  all_tac); 

(* net_resolve_tac actually made it slower... *)
fun prolog_step_tac horns i = 
    (assume_tac i APPEND resolve_tac horns i) THEN
    (ALLGOALS check_tac) THEN
    (TRYALL eq_assume_tac);


(*Sums the sizes of the subgoals, ignoring hypotheses (ancestors)*)
local fun addconcl(prem,sz) = size_of_term (Logic.strip_assums_concl prem) + sz
in
fun size_of_subgoals st = foldr addconcl (prems_of st, 0)
end;

(*Could simply use nprems_of, which would count remaining subgoals -- no
  discrimination as to their size!  With BEST_FIRST, fails for problem 41.*)

fun best_prolog_tac sizef horns = 
    BEST_FIRST (has_fewer_prems 1, sizef) (prolog_step_tac horns 1);

fun depth_prolog_tac horns = 
    DEPTH_FIRST (has_fewer_prems 1) (prolog_step_tac horns 1);

(*Return all negative clauses, as possible goal clauses*)
fun gocls cls = map make_goal (neg_clauses cls);


fun skolemize_tac prems = 
    cut_facts_tac (map (skolemize o make_nnf) prems)  THEN'
    REPEAT o (etac exE);

fun MESON sko_tac = SELECT_GOAL
 (EVERY1 [rtac ccontr,
          METAHYPS (fn negs =>
                    EVERY1 [skolemize_tac negs,
                            METAHYPS (sko_tac o make_clauses)])]);

fun best_meson_tac sizef = 
  MESON (fn cls => 
         resolve_tac (gocls cls) 1
         THEN_BEST_FIRST 
         (has_fewer_prems 1, sizef,
          prolog_step_tac (make_horns cls) 1));

(*First, breaks the goal into independent units*)
val safe_meson_tac =
     SELECT_GOAL (TRY (safe_tac HOL_cs) THEN 
                  TRYALL (best_meson_tac size_of_subgoals));

val depth_meson_tac =
     MESON (fn cls => EVERY [resolve_tac (gocls cls) 1, 
                             depth_prolog_tac (make_horns cls)]);

writeln"Reached end of file.";
