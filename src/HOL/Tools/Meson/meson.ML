(*  Title:      HOL/Tools/Meson/meson.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

The MESON resolution proof procedure for HOL.
When making clauses, avoids using the rewriter -- instead uses RS recursively.
*)

signature MESON =
sig
  val trace : bool Config.T
  val unfold_set_consts : bool Config.T
  val max_clauses : int Config.T
  val term_pair_of: indexname * (typ * 'a) -> term * 'a
  val first_order_resolve : thm -> thm -> thm
  val size_of_subgoals: thm -> int
  val has_too_many_clauses: Proof.context -> term -> bool
  val make_cnf:
    thm list -> thm -> Proof.context
    -> Proof.context -> thm list * Proof.context
  val finish_cnf: thm list -> thm list
  val unfold_set_const_simps : Proof.context -> thm list
  val presimplified_consts : Proof.context -> string list
  val presimplify: Proof.context -> thm -> thm
  val make_nnf: Proof.context -> thm -> thm
  val choice_theorems : theory -> thm list
  val skolemize_with_choice_theorems : Proof.context -> thm list -> thm -> thm
  val skolemize : Proof.context -> thm -> thm
  val extensionalize_conv : Proof.context -> conv
  val extensionalize_theorem : Proof.context -> thm -> thm
  val is_fol_term: theory -> term -> bool
  val make_clauses_unsorted: Proof.context -> thm list -> thm list
  val make_clauses: Proof.context -> thm list -> thm list
  val make_horns: thm list -> thm list
  val best_prolog_tac: (thm -> int) -> thm list -> tactic
  val depth_prolog_tac: thm list -> tactic
  val gocls: thm list -> thm list
  val skolemize_prems_tac : Proof.context -> thm list -> int -> tactic
  val MESON:
    tactic -> (thm list -> thm list) -> (thm list -> tactic) -> Proof.context
    -> int -> tactic
  val best_meson_tac: (thm -> int) -> Proof.context -> int -> tactic
  val safe_best_meson_tac: Proof.context -> int -> tactic
  val depth_meson_tac: Proof.context -> int -> tactic
  val prolog_step_tac': thm list -> int -> tactic
  val iter_deepen_prolog_tac: thm list -> tactic
  val iter_deepen_meson_tac: Proof.context -> thm list -> int -> tactic
  val make_meta_clause: thm -> thm
  val make_meta_clauses: thm list -> thm list
  val meson_tac: Proof.context -> thm list -> int -> tactic
end

structure Meson : MESON =
struct

val trace = Attrib.setup_config_bool @{binding meson_trace} (K false)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

val unfold_set_consts =
  Attrib.setup_config_bool @{binding meson_unfold_set_consts} (K false)

val max_clauses = Attrib.setup_config_int @{binding meson_max_clauses} (K 60)

(*No known example (on 1-5-2007) needs even thirty*)
val iter_deepen_limit = 50;

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

val not_conjD = @{thm not_conjD};
val not_disjD = @{thm not_disjD};
val not_notD = @{thm not_notD};
val not_allD = @{thm not_allD};
val not_exD = @{thm not_exD};
val imp_to_disjD = @{thm imp_to_disjD};
val not_impD = @{thm not_impD};
val iff_to_disjD = @{thm iff_to_disjD};
val not_iffD = @{thm not_iffD};
val conj_exD1 = @{thm conj_exD1};
val conj_exD2 = @{thm conj_exD2};
val disj_exD = @{thm disj_exD};
val disj_exD1 = @{thm disj_exD1};
val disj_exD2 = @{thm disj_exD2};
val disj_assoc = @{thm disj_assoc};
val disj_comm = @{thm disj_comm};
val disj_FalseD1 = @{thm disj_FalseD1};
val disj_FalseD2 = @{thm disj_FalseD2};


(**** Operators for forward proof ****)


(** First-order Resolution **)

fun term_pair_of (ix, (ty,t)) = (Var (ix,ty), t);

(*FIXME: currently does not "rename variables apart"*)
fun first_order_resolve thA thB =
  (case
    try (fn () =>
      let val thy = theory_of_thm thA
          val tmA = concl_of thA
          val Const("==>",_) $ tmB $ _ = prop_of thB
          val tenv =
            Pattern.first_order_match thy (tmB, tmA)
                                          (Vartab.empty, Vartab.empty) |> snd
          val ct_pairs = map (pairself (cterm_of thy) o term_pair_of) (Vartab.dest tenv)
      in  thA RS (cterm_instantiate ct_pairs thB)  end) () of
    SOME th => th
  | NONE => raise THM ("first_order_resolve", 0, [thA, thB]))

(* Hack to make it less likely that we lose our precious bound variable names in
   "rename_bound_vars_RS" below, because of a clash. *)
val protect_prefix = "Meson_xyzzy"

fun protect_bound_var_names (t $ u) =
    protect_bound_var_names t $ protect_bound_var_names u
  | protect_bound_var_names (Abs (s, T, t')) =
    Abs (protect_prefix ^ s, T, protect_bound_var_names t')
  | protect_bound_var_names t = t

fun fix_bound_var_names old_t new_t =
  let
    fun quant_of @{const_name All} = SOME true
      | quant_of @{const_name Ball} = SOME true
      | quant_of @{const_name Ex} = SOME false
      | quant_of @{const_name Bex} = SOME false
      | quant_of _ = NONE
    val flip_quant = Option.map not
    fun some_eq (SOME x) (SOME y) = x = y
      | some_eq _ _ = false
    fun add_names quant (Const (quant_s, _) $ Abs (s, _, t')) =
        add_names quant t' #> some_eq quant (quant_of quant_s) ? cons s
      | add_names quant (@{const Not} $ t) = add_names (flip_quant quant) t
      | add_names quant (@{const implies} $ t1 $ t2) =
        add_names (flip_quant quant) t1 #> add_names quant t2
      | add_names quant (t1 $ t2) = fold (add_names quant) [t1, t2]
      | add_names _ _ = I
    fun lost_names quant =
      subtract (op =) (add_names quant new_t []) (add_names quant old_t [])
    fun aux ((t1 as Const (quant_s, _)) $ (Abs (s, T, t'))) =
      t1 $ Abs (s |> String.isPrefix protect_prefix s
                   ? perhaps (try (fn _ => hd (lost_names (quant_of quant_s)))),
                T, aux t')
      | aux (t1 $ t2) = aux t1 $ aux t2
      | aux t = t
  in aux new_t end

(* Forward proof while preserving bound variables names *)
fun rename_bound_vars_RS th rl =
  let
    val t = concl_of th
    val r = concl_of rl
    val th' = th RS Thm.rename_boundvars r (protect_bound_var_names r) rl
    val t' = concl_of th'
  in Thm.rename_boundvars t' (fix_bound_var_names t t') th' end

(*raises exception if no rules apply*)
fun tryres (th, rls) =
  let fun tryall [] = raise THM("tryres", 0, th::rls)
        | tryall (rl::rls) =
          (rename_bound_vars_RS th rl handle THM _ => tryall rls)
  in  tryall rls  end;

(*Permits forward proof from rules that discharge assumptions. The supplied proof state st,
  e.g. from conj_forward, should have the form
    "[| P' ==> ?P; Q' ==> ?Q |] ==> ?P & ?Q"
  and the effect should be to instantiate ?P and ?Q with normalized versions of P' and Q'.*)
fun forward_res ctxt nf st =
  let fun forward_tacf [prem] = rtac (nf prem) 1
        | forward_tacf prems =
            error (cat_lines
              ("Bad proof state in forward_res, please inform lcp@cl.cam.ac.uk:" ::
                Display.string_of_thm ctxt st ::
                "Premises:" :: map (Display.string_of_thm ctxt) prems))
  in
    case Seq.pull (ALLGOALS (Misc_Legacy.METAHYPS forward_tacf) st)
    of SOME(th,_) => th
     | NONE => raise THM("forward_res", 0, [st])
  end;

(*Are any of the logical connectives in "bs" present in the term?*)
fun has_conns bs =
  let fun has (Const _) = false
        | has (Const(@{const_name Trueprop},_) $ p) = has p
        | has (Const(@{const_name Not},_) $ p) = has p
        | has (Const(@{const_name HOL.disj},_) $ p $ q) = member (op =) bs @{const_name HOL.disj} orelse has p orelse has q
        | has (Const(@{const_name HOL.conj},_) $ p $ q) = member (op =) bs @{const_name HOL.conj} orelse has p orelse has q
        | has (Const(@{const_name All},_) $ Abs(_,_,p)) = member (op =) bs @{const_name All} orelse has p
        | has (Const(@{const_name Ex},_) $ Abs(_,_,p)) = member (op =) bs @{const_name Ex} orelse has p
        | has _ = false
  in  has  end;


(**** Clause handling ****)

fun literals (Const(@{const_name Trueprop},_) $ P) = literals P
  | literals (Const(@{const_name HOL.disj},_) $ P $ Q) = literals P @ literals Q
  | literals (Const(@{const_name Not},_) $ P) = [(false,P)]
  | literals P = [(true,P)];

(*number of literals in a term*)
val nliterals = length o literals;


(*** Tautology Checking ***)

fun signed_lits_aux (Const (@{const_name HOL.disj}, _) $ P $ Q) (poslits, neglits) =
      signed_lits_aux Q (signed_lits_aux P (poslits, neglits))
  | signed_lits_aux (Const(@{const_name Not},_) $ P) (poslits, neglits) = (poslits, P::neglits)
  | signed_lits_aux P (poslits, neglits) = (P::poslits, neglits);

fun signed_lits th = signed_lits_aux (HOLogic.dest_Trueprop (concl_of th)) ([],[]);

(*Literals like X=X are tautologous*)
fun taut_poslit (Const(@{const_name HOL.eq},_) $ t $ u) = t aconv u
  | taut_poslit (Const(@{const_name True},_)) = true
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

val not_refl_disj_D = @{thm not_refl_disj_D};

(*Is either term a Var that does not properly occur in the other term?*)
fun eliminable (t as Var _, u) = t aconv u orelse not (Logic.occs(t,u))
  | eliminable (u, t as Var _) = t aconv u orelse not (Logic.occs(t,u))
  | eliminable _ = false;

fun refl_clause_aux 0 th = th
  | refl_clause_aux n th =
       case HOLogic.dest_Trueprop (concl_of th) of
          (Const (@{const_name HOL.disj}, _) $ (Const (@{const_name HOL.disj}, _) $ _ $ _) $ _) =>
            refl_clause_aux n (th RS disj_assoc)    (*isolate an atom as first disjunct*)
        | (Const (@{const_name HOL.disj}, _) $ (Const(@{const_name Not},_) $ (Const(@{const_name HOL.eq},_) $ t $ u)) $ _) =>
            if eliminable(t,u)
            then refl_clause_aux (n-1) (th RS not_refl_disj_D)  (*Var inequation: delete*)
            else refl_clause_aux (n-1) (th RS disj_comm)  (*not between Vars: ignore*)
        | (Const (@{const_name HOL.disj}, _) $ _ $ _) => refl_clause_aux n (th RS disj_comm)
        | _ => (*not a disjunction*) th;

fun notequal_lits_count (Const (@{const_name HOL.disj}, _) $ P $ Q) =
      notequal_lits_count P + notequal_lits_count Q
  | notequal_lits_count (Const(@{const_name Not},_) $ (Const(@{const_name HOL.eq},_) $ _ $ _)) = 1
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
         (Misc_Legacy.METAHYPS (fn major::minors => rtac (nf (minors@hyps) major) 1) 1)
         st)
  of SOME(th,_) => th
   | NONE => raise THM("forward_res2", 0, [st]);

(*Remove duplicates in P|Q by assuming ~P in Q
  rls (initially []) accumulates assumptions of the form P==>False*)
fun nodups_aux ctxt rls th = nodups_aux ctxt rls (th RS disj_assoc)
    handle THM _ => tryres(th,rls)
    handle THM _ => tryres(forward_res2 (nodups_aux ctxt) rls (th RS disj_forward2),
                           [disj_FalseD1, disj_FalseD2, asm_rl])
    handle THM _ => th;

(*Remove duplicate literals, if there are any*)
fun nodups ctxt th =
  if has_duplicates (op =) (literals (prop_of th))
    then nodups_aux ctxt [] th
    else th;


(*** The basic CNF transformation ***)

fun estimated_num_clauses bound t =
 let
  fun sum x y = if x < bound andalso y < bound then x+y else bound
  fun prod x y = if x < bound andalso y < bound then x*y else bound
  
  (*Estimate the number of clauses in order to detect infeasible theorems*)
  fun signed_nclauses b (Const(@{const_name Trueprop},_) $ t) = signed_nclauses b t
    | signed_nclauses b (Const(@{const_name Not},_) $ t) = signed_nclauses (not b) t
    | signed_nclauses b (Const(@{const_name HOL.conj},_) $ t $ u) =
        if b then sum (signed_nclauses b t) (signed_nclauses b u)
             else prod (signed_nclauses b t) (signed_nclauses b u)
    | signed_nclauses b (Const(@{const_name HOL.disj},_) $ t $ u) =
        if b then prod (signed_nclauses b t) (signed_nclauses b u)
             else sum (signed_nclauses b t) (signed_nclauses b u)
    | signed_nclauses b (Const(@{const_name HOL.implies},_) $ t $ u) =
        if b then prod (signed_nclauses (not b) t) (signed_nclauses b u)
             else sum (signed_nclauses (not b) t) (signed_nclauses b u)
    | signed_nclauses b (Const(@{const_name HOL.eq}, Type ("fun", [T, _])) $ t $ u) =
        if T = HOLogic.boolT then (*Boolean equality is if-and-only-if*)
            if b then sum (prod (signed_nclauses (not b) t) (signed_nclauses b u))
                          (prod (signed_nclauses (not b) u) (signed_nclauses b t))
                 else sum (prod (signed_nclauses b t) (signed_nclauses b u))
                          (prod (signed_nclauses (not b) t) (signed_nclauses (not b) u))
        else 1
    | signed_nclauses b (Const(@{const_name Ex}, _) $ Abs (_,_,t)) = signed_nclauses b t
    | signed_nclauses b (Const(@{const_name All},_) $ Abs (_,_,t)) = signed_nclauses b t
    | signed_nclauses _ _ = 1; (* literal *)
 in signed_nclauses true t end

fun has_too_many_clauses ctxt t =
  let val max_cl = Config.get ctxt max_clauses in
    estimated_num_clauses (max_cl + 1) t > max_cl
  end

(*Replaces universally quantified variables by FREE variables -- because
  assumptions may not contain scheme variables.  Later, generalize using Variable.export. *)
local  
  val spec_var = Thm.dest_arg (Thm.dest_arg (#2 (Thm.dest_implies (Thm.cprop_of spec))));
  val spec_varT = #T (Thm.rep_cterm spec_var);
  fun name_of (Const (@{const_name All}, _) $ Abs(x,_,_)) = x | name_of _ = Name.uu;
in  
  fun freeze_spec th ctxt =
    let
      val cert = Thm.cterm_of (Proof_Context.theory_of ctxt);
      val ([x], ctxt') = Variable.variant_fixes [name_of (HOLogic.dest_Trueprop (concl_of th))] ctxt;
      val spec' = Thm.instantiate ([], [(spec_var, cert (Free (x, spec_varT)))]) spec;
    in (th RS spec', ctxt') end
end;

(*Used with METAHYPS below. There is one assumption, which gets bound to prem
  and then normalized via function nf. The normal form is given to resolve_tac,
  instantiate a Boolean variable created by resolution with disj_forward. Since
  (nf prem) returns a LIST of theorems, we can backtrack to get all combinations.*)
fun resop nf [prem] = resolve_tac (nf prem) 1;

(* Any need to extend this list with "HOL.type_class", "HOL.eq_class",
   and "Pure.term"? *)
val has_meta_conn = exists_Const (member (op =) ["==", "==>", "=simp=>", "all", "prop"] o #1);

fun apply_skolem_theorem (th, rls) =
  let
    fun tryall [] = raise THM ("apply_skolem_theorem", 0, th::rls)
      | tryall (rl :: rls) =
        first_order_resolve th rl handle THM _ => tryall rls
  in tryall rls end

(* Conjunctive normal form, adding clauses from th in front of ths (for foldr).
   Strips universal quantifiers and breaks up conjunctions.
   Eliminates existential quantifiers using Skolemization theorems. *)
fun cnf old_skolem_ths ctxt ctxt0 (th, ths) =
  let val ctxt0r = Unsynchronized.ref ctxt0   (* FIXME ??? *)
      fun cnf_aux (th,ths) =
        if not (can HOLogic.dest_Trueprop (prop_of th)) then ths (*meta-level: ignore*)
        else if not (has_conns [@{const_name All}, @{const_name Ex}, @{const_name HOL.conj}] (prop_of th))
        then nodups ctxt0 th :: ths (*no work to do, terminate*)
        else case head_of (HOLogic.dest_Trueprop (concl_of th)) of
            Const (@{const_name HOL.conj}, _) => (*conjunction*)
                cnf_aux (th RS conjunct1, cnf_aux (th RS conjunct2, ths))
          | Const (@{const_name All}, _) => (*universal quantifier*)
                let val (th',ctxt0') = freeze_spec th (!ctxt0r)
                in  ctxt0r := ctxt0'; cnf_aux (th', ths) end
          | Const (@{const_name Ex}, _) =>
              (*existential quantifier: Insert Skolem functions*)
              cnf_aux (apply_skolem_theorem (th, old_skolem_ths), ths)
          | Const (@{const_name HOL.disj}, _) =>
              (*Disjunction of P, Q: Create new goal of proving ?P | ?Q and solve it using
                all combinations of converting P, Q to CNF.*)
              let val tac =
                  Misc_Legacy.METAHYPS (resop cnf_nil) 1 THEN
                   (fn st' => st' |> Misc_Legacy.METAHYPS (resop cnf_nil) 1)
              in  Seq.list_of (tac (th RS disj_forward)) @ ths  end
          | _ => nodups ctxt0 th :: ths  (*no work to do*)
      and cnf_nil th = cnf_aux (th,[])
      val cls =
        if has_too_many_clauses ctxt (concl_of th) then
          (trace_msg ctxt (fn () =>
               "cnf is ignoring: " ^ Display.string_of_thm ctxt0 th); ths)
        else
          cnf_aux (th, ths)
  in (cls, !ctxt0r) end
fun make_cnf old_skolem_ths th ctxt ctxt0 =
  cnf old_skolem_ths ctxt ctxt0 (th, [])

(*Generalization, removal of redundant equalities, removal of tautologies.*)
fun finish_cnf ths = filter (not o is_taut) (map refl_clause ths);


(**** Generation of contrapositives ****)

fun is_left (Const (@{const_name Trueprop}, _) $
               (Const (@{const_name HOL.disj}, _) $ (Const (@{const_name HOL.disj}, _) $ _ $ _) $ _)) = true
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

fun has_bool @{typ bool} = true
  | has_bool (Type (_, Ts)) = exists has_bool Ts
  | has_bool _ = false

fun has_fun (Type (@{type_name fun}, _)) = true
  | has_fun (Type (_, Ts)) = exists has_fun Ts
  | has_fun _ = false

(*Is the string the name of a connective? Really only | and Not can remain,
  since this code expects to be called on a clause form.*)
val is_conn = member (op =)
    [@{const_name Trueprop}, @{const_name HOL.conj}, @{const_name HOL.disj},
     @{const_name HOL.implies}, @{const_name Not},
     @{const_name All}, @{const_name Ex}, @{const_name Ball}, @{const_name Bex}];

(*True if the term contains a function--not a logical connective--where the type
  of any argument contains bool.*)
val has_bool_arg_const =
    exists_Const
      (fn (c,T) => not(is_conn c) andalso exists has_bool (binder_types T));

(*A higher-order instance of a first-order constant? Example is the definition of
  one, 1, at a function type in theory Function_Algebras.*)
fun higher_inst_const thy (c,T) =
  case binder_types T of
      [] => false (*not a function type, OK*)
    | Ts => length (binder_types (Sign.the_const_type thy c)) <> length Ts;

(* Returns false if any Vars in the theorem mention type bool.
   Also rejects functions whose arguments are Booleans or other functions. *)
fun is_fol_term thy t =
    Term.is_first_order [@{const_name all}, @{const_name All},
                         @{const_name Ex}] t andalso
    not (exists_subterm (fn Var (_, T) => has_bool T orelse has_fun T
                          | _ => false) t orelse
         has_bool_arg_const t orelse
         exists_Const (higher_inst_const thy) t orelse
         has_meta_conn t);

fun rigid t = not (is_Var (head_of t));

fun ok4horn (Const (@{const_name Trueprop},_) $ (Const (@{const_name HOL.disj}, _) $ t $ _)) = rigid t
  | ok4horn (Const (@{const_name Trueprop},_) $ t) = rigid t
  | ok4horn _ = false;

(*Create a meta-level Horn clause*)
fun make_horn crules th =
  if ok4horn (concl_of th)
  then make_horn crules (tryres(th,crules)) handle THM _ => th
  else th;

(*Generate Horn clauses for all contrapositives of a clause. The input, th,
  is a HOL disjunction.*)
fun add_contras crules th hcs =
  let fun rots (0,_) = hcs
        | rots (k,th) = zero_var_indexes (make_horn crules th) ::
                        rots(k-1, assoc_right (th RS disj_comm))
  in case nliterals(prop_of th) of
        1 => th::hcs
      | n => rots(n, assoc_right th)
  end;

(*Use "theorem naming" to label the clauses*)
fun name_thms label =
    let fun name1 th (k, ths) =
          (k-1, Thm.put_name_hint (label ^ string_of_int k) th :: ths)
    in  fn ths => #2 (fold_rev name1 ths (length ths, []))  end;

(*Is the given disjunction an all-negative support clause?*)
fun is_negative th = forall (not o #1) (literals (prop_of th));

val neg_clauses = filter is_negative;


(***** MESON PROOF PROCEDURE *****)

fun rhyps (Const("==>",_) $ (Const(@{const_name Trueprop},_) $ A) $ phi,
           As) = rhyps(phi, A::As)
  | rhyps (_, As) = As;

(** Detecting repeated assumptions in a subgoal **)

(*The stringtree detects repeated assumptions.*)
fun ins_term t net = Net.insert_term (op aconv) (t, t) net;

(*detects repetitions in a list of terms*)
fun has_reps [] = false
  | has_reps [_] = false
  | has_reps [t,u] = (t aconv u)
  | has_reps ts = (fold ins_term ts Net.empty; false) handle Net.INSERT => true;

(*Like TRYALL eq_assume_tac, but avoids expensive THEN calls*)
fun TRYING_eq_assume_tac 0 st = Seq.single st
  | TRYING_eq_assume_tac i st =
       TRYING_eq_assume_tac (i-1) (Thm.eq_assumption i st)
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
fun addconcl prem sz = size_of_term (Logic.strip_assums_concl prem) + sz;

fun size_of_subgoals st = fold_rev addconcl (prems_of st) 0;


(*Negation Normal Form*)
val nnf_rls = [imp_to_disjD, iff_to_disjD, not_conjD, not_disjD,
               not_impD, not_iffD, not_allD, not_exD, not_notD];

fun ok4nnf (Const (@{const_name Trueprop},_) $ (Const (@{const_name Not}, _) $ t)) = rigid t
  | ok4nnf (Const (@{const_name Trueprop},_) $ t) = rigid t
  | ok4nnf _ = false;

fun make_nnf1 ctxt th =
  if ok4nnf (concl_of th)
  then make_nnf1 ctxt (tryres(th, nnf_rls))
    handle THM ("tryres", _, _) =>
        forward_res ctxt (make_nnf1 ctxt)
           (tryres(th, [conj_forward,disj_forward,all_forward,ex_forward]))
    handle THM ("tryres", _, _) => th
  else th

fun unfold_set_const_simps ctxt =
  if Config.get ctxt unfold_set_consts then @{thms Collect_def_raw mem_def_raw}
  else []

(*The simplification removes defined quantifiers and occurrences of True and False.
  nnf_ss also includes the one-point simprocs,
  which are needed to avoid the various one-point theorems from generating junk clauses.*)
val nnf_simps =
  @{thms simp_implies_def Ex1_def Ball_def Bex_def if_True if_False if_cancel
         if_eq_cancel cases_simp}
val nnf_extra_simps = @{thms split_ifs ex_simps all_simps simp_thms}

(* FIXME: "let_simp" is probably redundant now that we also rewrite with
  "Let_def_raw". *)
val nnf_ss =
  HOL_basic_ss addsimps nnf_extra_simps
    addsimprocs [@{simproc defined_All}, @{simproc defined_Ex}, @{simproc neq},
                 @{simproc let_simp}]

fun presimplified_consts ctxt =
  [@{const_name simp_implies}, @{const_name False}, @{const_name True},
   @{const_name Ex1}, @{const_name Ball}, @{const_name Bex}, @{const_name If},
   @{const_name Let}]
  |> Config.get ctxt unfold_set_consts
     ? append ([@{const_name Collect}, @{const_name Set.member}])

fun presimplify ctxt =
  rewrite_rule (map safe_mk_meta_eq nnf_simps)
  #> simplify nnf_ss
  (* TODO: avoid introducing "Set.member" in "Ball_def" "Bex_def" above if and
     when "metis_unfold_set_consts" becomes the only mode of operation. *)
  #> Raw_Simplifier.rewrite_rule
         (@{thm Let_def_raw} :: unfold_set_const_simps ctxt)

fun make_nnf ctxt th = case prems_of th of
    [] => th |> presimplify ctxt |> make_nnf1 ctxt
  | _ => raise THM ("make_nnf: premises in argument", 0, [th]);

fun choice_theorems thy =
  try (Global_Theory.get_thm thy) "Hilbert_Choice.choice" |> the_list

(* Pull existential quantifiers to front. This accomplishes Skolemization for
   clauses that arise from a subgoal. *)
fun skolemize_with_choice_theorems ctxt choice_ths =
  let
    fun aux th =
      if not (has_conns [@{const_name Ex}] (prop_of th)) then
        th
      else
        tryres (th, choice_ths @
                    [conj_exD1, conj_exD2, disj_exD, disj_exD1, disj_exD2])
        |> aux
        handle THM ("tryres", _, _) =>
               tryres (th, [conj_forward, disj_forward, all_forward])
               |> forward_res ctxt aux
               |> aux
               handle THM ("tryres", _, _) =>
                      rename_bound_vars_RS th ex_forward
                      |> forward_res ctxt aux
  in aux o make_nnf ctxt end

fun skolemize ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    skolemize_with_choice_theorems ctxt (choice_theorems thy)
  end

(* Removes the lambdas from an equation of the form "t = (%x1 ... xn. u)". It
   would be desirable to do this symmetrically but there's at least one existing
   proof in "Tarski" that relies on the current behavior. *)
fun extensionalize_conv ctxt ct =
  case term_of ct of
    Const (@{const_name HOL.eq}, _) $ _ $ Abs _ =>
    ct |> (Conv.rewr_conv @{thm fun_eq_iff [THEN eq_reflection]}
           then_conv extensionalize_conv ctxt)
  | _ $ _ => Conv.comb_conv (extensionalize_conv ctxt) ct
  | Abs _ => Conv.abs_conv (extensionalize_conv o snd) ctxt ct
  | _ => Conv.all_conv ct

val extensionalize_theorem = Conv.fconv_rule o extensionalize_conv

(* "RS" can fail if "unify_search_bound" is too small. *)
fun try_skolemize_etc ctxt =
  Raw_Simplifier.rewrite_rule (unfold_set_const_simps ctxt)
  (* Extensionalize "th", because that makes sense and that's what Sledgehammer
     does, but also keep an unextensionalized version of "th" for backward
     compatibility. *)
  #> (fn th => insert Thm.eq_thm_prop (extensionalize_theorem ctxt th) [th])
  #> map_filter (fn th => try (skolemize ctxt) th
                          |> tap (fn NONE =>
                                     trace_msg ctxt (fn () =>
                                         "Failed to skolemize " ^
                                          Display.string_of_thm ctxt th)
                                   | _ => ()))

fun add_clauses ctxt th cls =
  let val ctxt0 = Variable.global_thm_context th
      val (cnfs, ctxt) = make_cnf [] th ctxt ctxt0
  in Variable.export ctxt ctxt0 cnfs @ cls end;

(*Make clauses from a list of theorems, previously Skolemized and put into nnf.
  The resulting clauses are HOL disjunctions.*)
fun make_clauses_unsorted ctxt ths = fold_rev (add_clauses ctxt) ths [];
val make_clauses = sort_clauses oo make_clauses_unsorted;

(*Convert a list of clauses (disjunctions) to Horn clauses (contrapositives)*)
fun make_horns ths =
    name_thms "Horn#"
      (distinct Thm.eq_thm_prop (fold_rev (add_contras clause_rules) ths []));

(*Could simply use nprems_of, which would count remaining subgoals -- no
  discrimination as to their size!  With BEST_FIRST, fails for problem 41.*)

fun best_prolog_tac sizef horns =
    BEST_FIRST (has_fewer_prems 1, sizef) (prolog_step_tac horns 1);

fun depth_prolog_tac horns =
    DEPTH_FIRST (has_fewer_prems 1) (prolog_step_tac horns 1);

(*Return all negative clauses, as possible goal clauses*)
fun gocls cls = name_thms "Goal#" (map make_goal (neg_clauses cls));

fun skolemize_prems_tac ctxt prems =
  cut_facts_tac (maps (try_skolemize_etc ctxt) prems) THEN' REPEAT o etac exE

(*Basis of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions.
  Function mkcl converts theorems to clauses.*)
fun MESON preskolem_tac mkcl cltac ctxt i st =
  SELECT_GOAL
    (EVERY [Object_Logic.atomize_prems_tac 1,
            rtac ccontr 1,
            preskolem_tac,
            Subgoal.FOCUS (fn {context = ctxt', prems = negs, ...} =>
                      EVERY1 [skolemize_prems_tac ctxt negs,
                              Subgoal.FOCUS (cltac o mkcl o #prems) ctxt']) ctxt 1]) i st
  handle THM _ => no_tac st;    (*probably from make_meta_clause, not first-order*)


(** Best-first search versions **)

(*ths is a list of additional clauses (HOL disjunctions) to use.*)
fun best_meson_tac sizef ctxt =
  MESON all_tac (make_clauses ctxt)
    (fn cls =>
         THEN_BEST_FIRST (resolve_tac (gocls cls) 1)
                         (has_fewer_prems 1, sizef)
                         (prolog_step_tac (make_horns cls) 1))
    ctxt

(*First, breaks the goal into independent units*)
fun safe_best_meson_tac ctxt =
  SELECT_GOAL (TRY (safe_tac ctxt) THEN TRYALL (best_meson_tac size_of_subgoals ctxt));

(** Depth-first search version **)

fun depth_meson_tac ctxt =
  MESON all_tac (make_clauses ctxt)
    (fn cls => EVERY [resolve_tac (gocls cls) 1, depth_prolog_tac (make_horns cls)])
    ctxt

(** Iterative deepening version **)

(*This version does only one inference per call;
  having only one eq_assume_tac speeds it up!*)
fun prolog_step_tac' horns =
    let val (horn0s, _) = (*0 subgoals vs 1 or more*)
            take_prefix Thm.no_prems horns
        val nrtac = net_resolve_tac horns
    in  fn i => eq_assume_tac i ORELSE
                match_tac horn0s i ORELSE  (*no backtracking if unit MATCHES*)
                ((assume_tac i APPEND nrtac i) THEN check_tac)
    end;

fun iter_deepen_prolog_tac horns =
    ITER_DEEPEN iter_deepen_limit (has_fewer_prems 1) (prolog_step_tac' horns);

fun iter_deepen_meson_tac ctxt ths = ctxt |> MESON all_tac (make_clauses ctxt)
  (fn cls =>
    (case (gocls (cls @ ths)) of
      [] => no_tac  (*no goal clauses*)
    | goes =>
        let
          val horns = make_horns (cls @ ths)
          val _ = trace_msg ctxt (fn () =>
            cat_lines ("meson method called:" ::
              map (Display.string_of_thm ctxt) (cls @ ths) @
              ["clauses:"] @ map (Display.string_of_thm ctxt) horns))
        in
          THEN_ITER_DEEPEN iter_deepen_limit
            (resolve_tac goes 1) (has_fewer_prems 1) (prolog_step_tac' horns)
        end));

fun meson_tac ctxt ths =
  SELECT_GOAL (TRY (safe_tac ctxt) THEN TRYALL (iter_deepen_meson_tac ctxt ths));


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
  let val (fth,thaw) = Drule.legacy_freeze_thaw_robust th
  in  
      (zero_var_indexes o Thm.varifyT_global o thaw 0 o 
       negated_asm_of_head o make_horn resolution_clause_rules) fth
  end;

fun make_meta_clauses ths =
    name_thms "MClause#"
      (distinct Thm.eq_thm_prop (map make_meta_clause ths));

end;
