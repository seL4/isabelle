(*  Title:      HOL/Tools/meson.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The MESON resolution proof procedure for HOL.

When making clauses, avoids using the rewriter -- instead uses RS recursively

NEED TO SORT LITERALS BY # OF VARS, USING ==>I/E.  ELIMINATES NEED FOR
FUNCTION nodups -- if done to goal clauses too!
*)

local

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


 (**** Operators for forward proof ****)

 (*raises exception if no rules apply -- unlike RL*)
 fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
   | tryres (th, []) = raise THM("tryres", 0, [th]);

 val prop_of = #prop o rep_thm;

 (*Permits forward proof from rules that discharge assumptions*)
 fun forward_res nf st =
   case Seq.pull (ALLGOALS (METAHYPS (fn [prem] => rtac (nf prem) 1)) st)
   of Some(th,_) => th
    | None => raise THM("forward_res", 0, [st]);


 (*Are any of the constants in "bs" present in the term?*)
 fun has_consts bs =
   let fun has (Const(a,_)) = a mem bs
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
         (fn st' => st' |>
                 METAHYPS (resop (cnf_nil (literals (concl_of st') @ seen))) 1)
     in  Seq.list_of (tac (th RS disj_forward)) @ ths  end
 and cnf_nil seen th = cnf_aux seen (th,[]);

 (*Top-level call to cnf -- it's safe to reset name_ref*)
 fun cnf (th,ths) =
    (name_ref := 19;  cnf (th RS conjunct1, cnf (th RS conjunct2, ths))
     handle THM _ => (*not a conjunction*) cnf_aux [] (th, ths));

 (**** Removal of duplicate literals ****)

 (*Forward proof, passing extra assumptions as theorems to the tactic*)
 fun forward_res2 nf hyps st =
   case Seq.pull
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

 (*For Plaisted's postive refinement.  [currently unused] *)
 val refined_clause_rules = [disj_assoc, make_refined_neg_rule, make_pos_rule];

 (*Create a goal or support clause, conclusing False*)
 fun make_goal th =   (*Must check for negative literal first!*)
     make_goal (tryres(th, clause_rules))
   handle THM _ => tryres(th, [make_neg_goal, make_pos_goal]);

 (*Sort clauses by number of literals*)
 fun fewerlits(th1,th2) = nliterals(prop_of th1) < nliterals(prop_of th2);

 (*TAUTOLOGY CHECK SHOULD NOT BE NECESSARY!*)
 fun sort_clauses ths = sort (make_ord fewerlits) (filter (not o is_taut) ths);

 (*Convert all suitable free variables to schematic variables*)
 fun generalize th = forall_elim_vars 0 (forall_intr_frees th);

 (*Create a meta-level Horn clause*)
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

 (*Use "theorem naming" to label the clauses*)
 fun name_thms label =
     let fun name1 (th, (k,ths)) =
           (k-1, Thm.name_thm (label ^ string_of_int k, th) :: ths)

     in  fn ths => #2 (foldr name1 (ths, (length ths, [])))  end;

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


in


(*Sums the sizes of the subgoals, ignoring hypotheses (ancestors)*)
local fun addconcl(prem,sz) = size_of_term(Logic.strip_assums_concl prem) + sz
in
fun size_of_subgoals st = foldr addconcl (prems_of st, 0)
end;

(*Negation Normal Form*)
val nnf_rls = [imp_to_disjD, iff_to_disjD, not_conjD, not_disjD,
               not_impD, not_iffD, not_allD, not_exD, not_notD];
fun make_nnf th = make_nnf (tryres(th, nnf_rls))
    handle THM _ =>
        forward_res make_nnf
           (tryres(th, [conj_forward,disj_forward,all_forward,ex_forward]))
    handle THM _ => th;

(*Pull existential quantifiers (Skolemization)*)
fun skolemize th =
  if not (has_consts ["Ex"] (prop_of th)) then th
  else skolemize (tryres(th, [choice, conj_exD1, conj_exD2,
                              disj_exD, disj_exD1, disj_exD2]))
    handle THM _ =>
        skolemize (forward_res skolemize
                   (tryres (th, [conj_forward, disj_forward, all_forward])))
    handle THM _ => forward_res skolemize (th RS ex_forward);


(*Make clauses from a list of theorems, previously Skolemized and put into nnf.
  The resulting clauses are HOL disjunctions.*)
fun make_clauses ths =
    sort_clauses (map (generalize o nodups) (foldr cnf (ths,[])));

(*Convert a list of clauses to (contrapositive) Horn clauses*)
fun make_horns ths =
    name_thms "Horn#"
      (gen_distinct Drule.eq_thm_prop (foldr (add_contras clause_rules) (ths,[])));

(*Could simply use nprems_of, which would count remaining subgoals -- no
  discrimination as to their size!  With BEST_FIRST, fails for problem 41.*)

fun best_prolog_tac sizef horns =
    BEST_FIRST (has_fewer_prems 1, sizef) (prolog_step_tac horns 1);

fun depth_prolog_tac horns =
    DEPTH_FIRST (has_fewer_prems 1) (prolog_step_tac horns 1);

(*Return all negative clauses, as possible goal clauses*)
fun gocls cls = name_thms "Goal#" (map make_goal (neg_clauses cls));


fun skolemize_tac prems =
    cut_facts_tac (map (skolemize o make_nnf) prems)  THEN'
    REPEAT o (etac exE);

(*Shell of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions*)
fun MESON cltac = SELECT_GOAL
 (EVERY1 [rtac ccontr,
          METAHYPS (fn negs =>
                    EVERY1 [skolemize_tac negs,
                            METAHYPS (cltac o make_clauses)])]);

(** Best-first search versions **)

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

val iter_deepen_meson_tac =
  MESON (fn cls =>
         (THEN_ITER_DEEPEN (resolve_tac (gocls cls) 1)
                           (has_fewer_prems 1)
                           (prolog_step_tac' (make_horns cls))));

fun meson_claset_tac cs =
  SELECT_GOAL (TRY (safe_tac cs) THEN TRYALL iter_deepen_meson_tac);

val meson_tac = CLASET' meson_claset_tac;


(* proof method setup *)

local

fun meson_meth ctxt =
  Method.SIMPLE_METHOD' HEADGOAL
    (CHANGED_PROP o meson_claset_tac (Classical.get_local_claset ctxt));

in

val meson_setup =
 [Method.add_methods
  [("meson", Method.ctxt_args meson_meth, "The MESON resolution proof procedure")]];

end;

end;
