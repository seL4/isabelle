(*  Title:      HOL/Tools/meson.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

The MESON resolution proof procedure for HOL.
When making clauses, avoids using the rewriter -- instead uses RS recursively.
*)

signature MESON =
sig
  val term_pair_of: indexname * (typ * 'a) -> term * 'a
  val first_order_resolve: thm -> thm -> thm
  val flexflex_first_order: thm -> thm
  val size_of_subgoals: thm -> int
  val too_many_clauses: Proof.context option -> term -> bool
  val make_cnf: thm list -> thm -> Proof.context -> thm list * Proof.context
  val finish_cnf: thm list -> thm list
  val make_nnf: thm -> thm
  val skolemize: thm -> thm
  val is_fol_term: theory -> term -> bool
  val make_clauses: thm list -> thm list
  val make_horns: thm list -> thm list
  val best_prolog_tac: (thm -> int) -> thm list -> tactic
  val depth_prolog_tac: thm list -> tactic
  val gocls: thm list -> thm list
  val skolemize_prems_tac: thm list -> int -> tactic
  val MESON: (thm list -> thm list) -> (thm list -> tactic) -> int -> tactic
  val best_meson_tac: (thm -> int) -> int -> tactic
  val safe_best_meson_tac: claset -> int -> tactic
  val depth_meson_tac: int -> tactic
  val prolog_step_tac': thm list -> int -> tactic
  val iter_deepen_prolog_tac: thm list -> tactic
  val iter_deepen_meson_tac: thm list -> int -> tactic
  val make_meta_clause: thm -> thm
  val make_meta_clauses: thm list -> thm list
  val meson_claset_tac: thm list -> claset -> int -> tactic
  val meson_tac: claset -> int -> tactic
  val negate_head: thm -> thm
  val select_literal: int -> thm -> thm
  val skolemize_tac: int -> tactic
  val setup: Context.theory -> Context.theory
end

structure Meson: MESON =
struct

val max_clauses_default = 60;
val (max_clauses, setup) = Attrib.config_int "max_clauses" max_clauses_default;

val disj_forward = @{thm disj_forward};
val disj_forward2 = @{thm disj_forward2};
val make_pos_rule = @{thm make_pos_rule};
val make_pos_rule' = @{thm make_pos_rule'};
val make_pos_goal = @{thm make_pos_goal};
val make_neg_rule = @{thm make_neg_rule};
val make_neg_rule' = @{thm make_neg_rule'};
val make_neg_goal = @{thm make_neg_goal};
val conj_forward = @{thm conj_forward};
val all_forward = @{thm all_forward};
val ex_forward = @{thm ex_forward};
val choice = @{thm choice};

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


(** First-order Resolution **)

fun typ_pair_of (ix, (sort,ty)) = (TVar (ix,sort), ty);
fun term_pair_of (ix, (ty,t)) = (Var (ix,ty), t);

val Envir.Envir {asol = tenv0, iTs = tyenv0, ...} = Envir.empty 0

(*FIXME: currently does not "rename variables apart"*)
fun first_order_resolve thA thB =
  let val thy = theory_of_thm thA
      val tmA = concl_of thA
      val Const("==>",_) $ tmB $ _ = prop_of thB
      val (tyenv,tenv) = Pattern.first_order_match thy (tmB,tmA) (tyenv0,tenv0)
      val ct_pairs = map (pairself (cterm_of thy) o term_pair_of) (Vartab.dest tenv)
  in  thA RS (cterm_instantiate ct_pairs thB)  end
  handle _ => raise THM ("first_order_resolve", 0, [thA,thB]);  (* FIXME avoid handle _ *)

fun flexflex_first_order th =
  case (tpairs_of th) of
      [] => th
    | pairs =>
        let val thy = theory_of_thm th
            val (tyenv,tenv) =
                  List.foldl (uncurry (Pattern.first_order_match thy)) (tyenv0,tenv0) pairs
            val t_pairs = map term_pair_of (Vartab.dest tenv)
            val th' = Thm.instantiate ([], map (pairself (cterm_of thy)) t_pairs) th
        in  th'  end
        handle THM _ => th;

(*Forward proof while preserving bound variables names*)
fun rename_bvs_RS th rl =
  let val th' = th RS rl
  in  Thm.rename_boundvars (concl_of th') (concl_of th) th' end;

(*raises exception if no rules apply*)
fun tryres (th, rls) =
  let fun tryall [] = raise THM("tryres", 0, th::rls)
        | tryall (rl::rls) = (rename_bvs_RS th rl handle THM _ => tryall rls)
  in  tryall rls  end;

(*Permits forward proof from rules that discharge assumptions. The supplied proof state st,
  e.g. from conj_forward, should have the form
    "[| P' ==> ?P; Q' ==> ?Q |] ==> ?P & ?Q"
  and the effect should be to instantiate ?P and ?Q with normalized versions of P' and Q'.*)
fun forward_res nf st =
  let fun forward_tacf [prem] = rtac (nf prem) 1
        | forward_tacf prems =
            error ("Bad proof state in forward_res, please inform lcp@cl.cam.ac.uk:\n" ^
                   Display.string_of_thm st ^
                   "\nPremises:\n" ^
                   ML_Syntax.print_list Display.string_of_thm prems)
  in
    case Seq.pull (ALLGOALS (METAHYPS forward_tacf) st)
    of SOME(th,_) => th
     | NONE => raise THM("forward_res", 0, [st])
  end;

(*Are any of the logical connectives in "bs" present in the term?*)
fun has_conns bs =
  let fun has (Const(a,_)) = false
        | has (Const("Trueprop",_) $ p) = has p
        | has (Const("Not",_) $ p) = has p
        | has (Const("op |",_) $ p $ q) = member (op =) bs "op |" orelse has p orelse has q
        | has (Const("op &",_) $ p $ q) = member (op =) bs "op &" orelse has p orelse has q
        | has (Const("All",_) $ Abs(_,_,p)) = member (op =) bs "All" orelse has p
        | has (Const("Ex",_) $ Abs(_,_,p)) = member (op =) bs "Ex" orelse has p
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
      exists (member (op aconv) neglits) (HOLogic.false_const :: poslits)
  end
  handle TERM _ => false;       (*probably dest_Trueprop on a weird theorem*)


(*** To remove trivial negated equality literals from clauses ***)

(*They are typically functional reflexivity axioms and are the converses of
  injectivity equivalences*)

val not_refl_disj_D = thm"meson_not_refl_disj_D";

(*Is either term a Var that does not properly occur in the other term?*)
fun eliminable (t as Var _, u) = t aconv u orelse not (Logic.occs(t,u))
  | eliminable (u, t as Var _) = t aconv u orelse not (Logic.occs(t,u))
  | eliminable _ = false;

fun refl_clause_aux 0 th = th
  | refl_clause_aux n th =
       case HOLogic.dest_Trueprop (concl_of th) of
          (Const ("op |", _) $ (Const ("op |", _) $ _ $ _) $ _) =>
            refl_clause_aux n (th RS disj_assoc)    (*isolate an atom as first disjunct*)
        | (Const ("op |", _) $ (Const("Not",_) $ (Const("op =",_) $ t $ u)) $ _) =>
            if eliminable(t,u)
            then refl_clause_aux (n-1) (th RS not_refl_disj_D)  (*Var inequation: delete*)
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
  handle TERM _ => th;  (*probably dest_Trueprop on a weird theorem*)


(*** Removal of duplicate literals ***)

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
  if has_duplicates (op =) (literals (prop_of th))
    then nodups_aux [] th
    else th;


(*** The basic CNF transformation ***)

fun too_many_clauses ctxto t = 
 let
  val max_cl = case ctxto of SOME ctxt => Config.get ctxt max_clauses
                           | NONE => max_clauses_default
  
  fun sum x y = if x < max_cl andalso y < max_cl then x+y else max_cl;
  fun prod x y = if x < max_cl andalso y < max_cl then x*y else max_cl;
  
  (*Estimate the number of clauses in order to detect infeasible theorems*)
  fun signed_nclauses b (Const("Trueprop",_) $ t) = signed_nclauses b t
    | signed_nclauses b (Const("Not",_) $ t) = signed_nclauses (not b) t
    | signed_nclauses b (Const("op &",_) $ t $ u) =
	if b then sum (signed_nclauses b t) (signed_nclauses b u)
	     else prod (signed_nclauses b t) (signed_nclauses b u)
    | signed_nclauses b (Const("op |",_) $ t $ u) =
	if b then prod (signed_nclauses b t) (signed_nclauses b u)
	     else sum (signed_nclauses b t) (signed_nclauses b u)
    | signed_nclauses b (Const("op -->",_) $ t $ u) =
	if b then prod (signed_nclauses (not b) t) (signed_nclauses b u)
	     else sum (signed_nclauses (not b) t) (signed_nclauses b u)
    | signed_nclauses b (Const("op =", Type ("fun", [T, _])) $ t $ u) =
	if T = HOLogic.boolT then (*Boolean equality is if-and-only-if*)
	    if b then sum (prod (signed_nclauses (not b) t) (signed_nclauses b u))
			  (prod (signed_nclauses (not b) u) (signed_nclauses b t))
		 else sum (prod (signed_nclauses b t) (signed_nclauses b u))
			  (prod (signed_nclauses (not b) t) (signed_nclauses (not b) u))
	else 1
    | signed_nclauses b (Const("Ex", _) $ Abs (_,_,t)) = signed_nclauses b t
    | signed_nclauses b (Const("All",_) $ Abs (_,_,t)) = signed_nclauses b t
    | signed_nclauses _ _ = 1; (* literal *)
 in 
  signed_nclauses true t >= max_cl
 end;

(*Replaces universally quantified variables by FREE variables -- because
  assumptions may not contain scheme variables.  Later, generalize using Variable.export. *)
local  
  val spec_var = Thm.dest_arg (Thm.dest_arg (#2 (Thm.dest_implies (Thm.cprop_of spec))));
  val spec_varT = #T (Thm.rep_cterm spec_var);
  fun name_of (Const ("All", _) $ Abs(x,_,_)) = x | name_of _ = Name.uu;
in  
  fun freeze_spec th ctxt =
    let
      val cert = Thm.cterm_of (ProofContext.theory_of ctxt);
      val ([x], ctxt') = Variable.variant_fixes [name_of (HOLogic.dest_Trueprop (concl_of th))] ctxt;
      val spec' = Thm.instantiate ([], [(spec_var, cert (Free (x, spec_varT)))]) spec;
    in (th RS spec', ctxt') end
end;

(*Used with METAHYPS below. There is one assumption, which gets bound to prem
  and then normalized via function nf. The normal form is given to resolve_tac,
  instantiate a Boolean variable created by resolution with disj_forward. Since
  (nf prem) returns a LIST of theorems, we can backtrack to get all combinations.*)
fun resop nf [prem] = resolve_tac (nf prem) 1;

(*Any need to extend this list with
  "HOL.type_class","HOL.eq_class","Pure.term"?*)
val has_meta_conn =
    exists_Const (member (op =) ["==", "==>", "=simp=>", "all", "prop"] o #1);

fun apply_skolem_ths (th, rls) =
  let fun tryall [] = raise THM("apply_skolem_ths", 0, th::rls)
        | tryall (rl::rls) = (first_order_resolve th rl handle THM _ => tryall rls)
  in  tryall rls  end;

(*Conjunctive normal form, adding clauses from th in front of ths (for foldr).
  Strips universal quantifiers and breaks up conjunctions.
  Eliminates existential quantifiers using skoths: Skolemization theorems.*)
fun cnf skoths ctxt (th,ths) =
  let val ctxtr = ref ctxt
      fun cnf_aux (th,ths) =
        if not (can HOLogic.dest_Trueprop (prop_of th)) then ths (*meta-level: ignore*)
        else if not (has_conns ["All","Ex","op &"] (prop_of th))
        then nodups th :: ths (*no work to do, terminate*)
        else case head_of (HOLogic.dest_Trueprop (concl_of th)) of
            Const ("op &", _) => (*conjunction*)
                cnf_aux (th RS conjunct1, cnf_aux (th RS conjunct2, ths))
          | Const ("All", _) => (*universal quantifier*)
                let val (th',ctxt') = freeze_spec th (!ctxtr)
                in  ctxtr := ctxt'; cnf_aux (th', ths) end
          | Const ("Ex", _) =>
              (*existential quantifier: Insert Skolem functions*)
              cnf_aux (apply_skolem_ths (th,skoths), ths)
          | Const ("op |", _) =>
              (*Disjunction of P, Q: Create new goal of proving ?P | ?Q and solve it using
                all combinations of converting P, Q to CNF.*)
              let val tac =
                  (METAHYPS (resop cnf_nil) 1) THEN
                   (fn st' => st' |> METAHYPS (resop cnf_nil) 1)
              in  Seq.list_of (tac (th RS disj_forward)) @ ths  end
          | _ => nodups th :: ths  (*no work to do*)
      and cnf_nil th = cnf_aux (th,[])
      val cls = 
	    if too_many_clauses (SOME ctxt) (concl_of th)
	    then (warning ("cnf is ignoring: " ^ Display.string_of_thm th); ths)
	    else cnf_aux (th,ths)
  in  (cls, !ctxtr)  end;

fun make_cnf skoths th ctxt = cnf skoths ctxt (th, []);

(*Generalization, removal of redundant equalities, removal of tautologies.*)
fun finish_cnf ths = filter (not o is_taut) (map refl_clause ths);


(**** Generation of contrapositives ****)

fun is_left (Const ("Trueprop", _) $
               (Const ("op |", _) $ (Const ("op |", _) $ _ $ _) $ _)) = true
  | is_left _ = false;

(*Associate disjuctions to right -- make leftmost disjunct a LITERAL*)
fun assoc_right th =
  if is_left (prop_of th) then assoc_right (th RS disj_assoc)
  else th;

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

(*Is the string the name of a connective? Really only | and Not can remain,
  since this code expects to be called on a clause form.*)
val is_conn = member (op =)
    ["Trueprop", "op &", "op |", "op -->", "Not",
     "All", "Ex", "Ball", "Bex"];

(*True if the term contains a function--not a logical connective--where the type
  of any argument contains bool.*)
val has_bool_arg_const =
    exists_Const
      (fn (c,T) => not(is_conn c) andalso exists (has_bool) (binder_types T));

(*A higher-order instance of a first-order constant? Example is the definition of
  HOL.one, 1, at a function type in theory SetsAndFunctions.*)
fun higher_inst_const thy (c,T) =
  case binder_types T of
      [] => false (*not a function type, OK*)
    | Ts => length (binder_types (Sign.the_const_type thy c)) <> length Ts;

(*Returns false if any Vars in the theorem mention type bool.
  Also rejects functions whose arguments are Booleans or other functions.*)
fun is_fol_term thy t =
    Term.is_first_order ["all","All","Ex"] t andalso
    not (exists_subterm (fn Var (_, T) => has_bool T | _ => false) t  orelse
         has_bool_arg_const t  orelse
         exists_Const (higher_inst_const thy) t orelse
         has_meta_conn t);

fun rigid t = not (is_Var (head_of t));

fun ok4horn (Const ("Trueprop",_) $ (Const ("op |", _) $ t $ _)) = rigid t
  | ok4horn (Const ("Trueprop",_) $ t) = rigid t
  | ok4horn _ = false;

(*Create a meta-level Horn clause*)
fun make_horn crules th =
  if ok4horn (concl_of th)
  then make_horn crules (tryres(th,crules)) handle THM _ => th
  else th;

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
          (k-1, Thm.put_name_hint (label ^ string_of_int k) th :: ths)
    in  fn ths => #2 (List.foldr name1 (length ths, []) ths)  end;

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

fun size_of_subgoals st = List.foldr addconcl 0 (prems_of st);


(*Negation Normal Form*)
val nnf_rls = [imp_to_disjD, iff_to_disjD, not_conjD, not_disjD,
               not_impD, not_iffD, not_allD, not_exD, not_notD];

fun ok4nnf (Const ("Trueprop",_) $ (Const ("Not", _) $ t)) = rigid t
  | ok4nnf (Const ("Trueprop",_) $ t) = rigid t
  | ok4nnf _ = false;

fun make_nnf1 th =
  if ok4nnf (concl_of th)
  then make_nnf1 (tryres(th, nnf_rls))
    handle THM ("tryres", _, _) =>
        forward_res make_nnf1
           (tryres(th, [conj_forward,disj_forward,all_forward,ex_forward]))
    handle THM ("tryres", _, _) => th
  else th;

(*The simplification removes defined quantifiers and occurrences of True and False.
  nnf_ss also includes the one-point simprocs,
  which are needed to avoid the various one-point theorems from generating junk clauses.*)
val nnf_simps =
     [simp_implies_def, Ex1_def, Ball_def, Bex_def, if_True,
      if_False, if_cancel, if_eq_cancel, cases_simp];
val nnf_extra_simps =
      thms"split_ifs" @ ex_simps @ all_simps @ simp_thms;

val nnf_ss =
  HOL_basic_ss addsimps nnf_extra_simps
    addsimprocs [defALL_regroup,defEX_regroup, @{simproc neq}, @{simproc let_simp}];

fun make_nnf th = case prems_of th of
    [] => th |> rewrite_rule (map safe_mk_meta_eq nnf_simps)
             |> simplify nnf_ss
             |> make_nnf1
  | _ => raise THM ("make_nnf: premises in argument", 0, [th]);

(*Pull existential quantifiers to front. This accomplishes Skolemization for
  clauses that arise from a subgoal.*)
fun skolemize1 th =
  if not (has_conns ["Ex"] (prop_of th)) then th
  else (skolemize1 (tryres(th, [choice, conj_exD1, conj_exD2,
                              disj_exD, disj_exD1, disj_exD2])))
    handle THM ("tryres", _, _) =>
        skolemize1 (forward_res skolemize1
                   (tryres (th, [conj_forward, disj_forward, all_forward])))
    handle THM ("tryres", _, _) => 
        forward_res skolemize1 (rename_bvs_RS th ex_forward);

fun skolemize th = skolemize1 (make_nnf th);

fun skolemize_nnf_list [] = []
  | skolemize_nnf_list (th::ths) = 
      skolemize th :: skolemize_nnf_list ths
      handle THM _ => (*RS can fail if Unify.search_bound is too small*)
       (warning ("Failed to Skolemize " ^ Display.string_of_thm th);
        skolemize_nnf_list ths);

fun add_clauses (th,cls) =
  let val ctxt0 = Variable.thm_context th
      val (cnfs,ctxt) = make_cnf [] th ctxt0
  in Variable.export ctxt ctxt0 cnfs @ cls end;

(*Make clauses from a list of theorems, previously Skolemized and put into nnf.
  The resulting clauses are HOL disjunctions.*)
fun make_clauses ths = sort_clauses (List.foldr add_clauses [] ths);

(*Convert a list of clauses (disjunctions) to Horn clauses (contrapositives)*)
fun make_horns ths =
    name_thms "Horn#"
      (distinct Thm.eq_thm_prop (List.foldr (add_contras clause_rules) [] ths));

(*Could simply use nprems_of, which would count remaining subgoals -- no
  discrimination as to their size!  With BEST_FIRST, fails for problem 41.*)

fun best_prolog_tac sizef horns =
    BEST_FIRST (has_fewer_prems 1, sizef) (prolog_step_tac horns 1);

fun depth_prolog_tac horns =
    DEPTH_FIRST (has_fewer_prems 1) (prolog_step_tac horns 1);

(*Return all negative clauses, as possible goal clauses*)
fun gocls cls = name_thms "Goal#" (map make_goal (neg_clauses cls));

fun skolemize_prems_tac prems =
    cut_facts_tac (skolemize_nnf_list prems) THEN'
    REPEAT o (etac exE);

(*Basis of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions.
  Function mkcl converts theorems to clauses.*)
fun MESON mkcl cltac i st =
  SELECT_GOAL
    (EVERY [ObjectLogic.atomize_prems_tac 1,
            rtac ccontr 1,
            METAHYPS (fn negs =>
                      EVERY1 [skolemize_prems_tac negs,
                              METAHYPS (cltac o mkcl)]) 1]) i st
  handle THM _ => no_tac st;    (*probably from make_meta_clause, not first-order*)

(** Best-first search versions **)

(*ths is a list of additional clauses (HOL disjunctions) to use.*)
fun best_meson_tac sizef =
  MESON make_clauses
    (fn cls =>
         THEN_BEST_FIRST (resolve_tac (gocls cls) 1)
                         (has_fewer_prems 1, sizef)
                         (prolog_step_tac (make_horns cls) 1));

(*First, breaks the goal into independent units*)
fun safe_best_meson_tac cs =
     SELECT_GOAL (TRY (safe_tac cs) THEN
                  TRYALL (best_meson_tac size_of_subgoals));

(** Depth-first search version **)

val depth_meson_tac =
  MESON make_clauses
    (fn cls => EVERY [resolve_tac (gocls cls) 1, depth_prolog_tac (make_horns cls)]);


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

fun iter_deepen_meson_tac ths = MESON make_clauses
 (fn cls =>
      case (gocls (cls@ths)) of
           [] => no_tac  (*no goal clauses*)
         | goes =>
             let val horns = make_horns (cls@ths)
                 val _ =
                     Output.debug (fn () => ("meson method called:\n" ^
                                  ML_Syntax.print_list Display.string_of_thm (cls@ths) ^
                                  "\nclauses:\n" ^
                                  ML_Syntax.print_list Display.string_of_thm horns))
             in THEN_ITER_DEEPEN (resolve_tac goes 1) (has_fewer_prems 1) (prolog_step_tac' horns)
             end
 );

fun meson_claset_tac ths cs =
  SELECT_GOAL (TRY (safe_tac cs) THEN TRYALL (iter_deepen_meson_tac ths));

val meson_tac = meson_claset_tac [];


(**** Code to support ordinary resolution, rather than Model Elimination ****)

(*Convert a list of clauses (disjunctions) to meta-level clauses (==>),
  with no contrapositives, for ordinary resolution.*)

(*Rules to convert the head literal into a negated assumption. If the head
  literal is already negated, then using notEfalse instead of notEfalse'
  prevents a double negation.*)
val notEfalse = read_instantiate @{context} [(("R", 0), "False")] notE;
val notEfalse' = rotate_prems 1 notEfalse;

fun negated_asm_of_head th =
    th RS notEfalse handle THM _ => th RS notEfalse';

(*Converting one theorem from a disjunction to a meta-level clause*)
fun make_meta_clause th =
  let val (fth,thaw) = Drule.freeze_thaw_robust th
  in  
      (zero_var_indexes o Thm.varifyT o thaw 0 o 
       negated_asm_of_head o make_horn resolution_clause_rules) fth
  end;

fun make_meta_clauses ths =
    name_thms "MClause#"
      (distinct Thm.eq_thm_prop (map make_meta_clause ths));

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
            (fn hyps => (cut_facts_tac (skolemize_nnf_list hyps) 1
                         THEN REPEAT (etac exE 1))),
            REPEAT_DETERM_N (length ts) o (etac thin_rl)] i st
  end
  handle Subscript => Seq.empty;

end;
