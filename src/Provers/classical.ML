(*  Title:      Provers/classical.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Theorem prover for classical reasoning, including predicate calculus, set
theory, etc.

Rules must be classified as intro, elim, safe, hazardous (unsafe).

A rule is unsafe unless it can be applied blindly without harmful results.
For a rule to be safe, its premises and conclusion should be logically
equivalent.  There should be no variables in the premises that are not in
the conclusion.
*)

(*higher precedence than := facilitates use of references*)
infix 4 addSIs addSEs addSDs addIs addEs addDs delrules
  addSWrapper delSWrapper addWrapper delWrapper
  addSbefore addSafter addbefore addafter
  addD2 addE2 addSD2 addSE2;

signature CLASSICAL_DATA =
sig
  val imp_elim: thm  (* P --> Q ==> (~ R ==> P) ==> (Q ==> R) ==> R *)
  val not_elim: thm  (* ~P ==> P ==> R *)
  val swap: thm  (* ~ P ==> (~ R ==> P) ==> R *)
  val classical: thm  (* (~ P ==> P) ==> P *)
  val sizef: thm -> int  (* size function for BEST_FIRST *)
  val hyp_subst_tacs: (int -> tactic) list
end;

signature BASIC_CLASSICAL =
sig
  type wrapper = (int -> tactic) -> int -> tactic
  type claset
  val print_claset: Proof.context -> unit
  val addDs: Proof.context * thm list -> Proof.context
  val addEs: Proof.context * thm list -> Proof.context
  val addIs: Proof.context * thm list -> Proof.context
  val addSDs: Proof.context * thm list -> Proof.context
  val addSEs: Proof.context * thm list -> Proof.context
  val addSIs: Proof.context * thm list -> Proof.context
  val delrules: Proof.context * thm list -> Proof.context
  val addSWrapper: claset * (string * (Proof.context -> wrapper)) -> claset
  val delSWrapper: claset *  string -> claset
  val addWrapper: claset * (string * (Proof.context -> wrapper)) -> claset
  val delWrapper: claset *  string -> claset
  val addSbefore: claset * (string * (int -> tactic)) -> claset
  val addSafter: claset * (string * (int -> tactic)) -> claset
  val addbefore: claset * (string * (int -> tactic)) -> claset
  val addafter: claset * (string * (int -> tactic)) -> claset
  val addD2: claset * (string * thm) -> claset
  val addE2: claset * (string * thm) -> claset
  val addSD2: claset * (string * thm) -> claset
  val addSE2: claset * (string * thm) -> claset
  val appSWrappers: Proof.context -> wrapper
  val appWrappers: Proof.context -> wrapper

  val global_claset_of: theory -> claset
  val claset_of: Proof.context -> claset
  val map_claset: (claset -> claset) -> Proof.context -> Proof.context
  val put_claset: claset -> Proof.context -> Proof.context

  val fast_tac: Proof.context -> int -> tactic
  val slow_tac: Proof.context -> int -> tactic
  val astar_tac: Proof.context -> int -> tactic
  val slow_astar_tac: Proof.context -> int -> tactic
  val best_tac: Proof.context -> int -> tactic
  val first_best_tac: Proof.context -> int -> tactic
  val slow_best_tac: Proof.context -> int -> tactic
  val depth_tac: Proof.context -> int -> int -> tactic
  val deepen_tac: Proof.context -> int -> int -> tactic

  val contr_tac: int -> tactic
  val dup_elim: thm -> thm
  val dup_intr: thm -> thm
  val dup_step_tac: Proof.context -> int -> tactic
  val eq_mp_tac: int -> tactic
  val haz_step_tac: Proof.context -> int -> tactic
  val joinrules: thm list * thm list -> (bool * thm) list
  val mp_tac: int -> tactic
  val safe_tac: Proof.context -> tactic
  val safe_steps_tac: Proof.context -> int -> tactic
  val safe_step_tac: Proof.context -> int -> tactic
  val clarify_tac: Proof.context -> int -> tactic
  val clarify_step_tac: Proof.context -> int -> tactic
  val step_tac: Proof.context -> int -> tactic
  val slow_step_tac: Proof.context -> int -> tactic
  val swapify: thm list -> thm list
  val swap_res_tac: thm list -> int -> tactic
  val inst_step_tac: Proof.context -> int -> tactic
  val inst0_step_tac: Proof.context -> int -> tactic
  val instp_step_tac: Proof.context -> int -> tactic
end;

signature CLASSICAL =
sig
  include BASIC_CLASSICAL
  val classical_rule: thm -> thm
  type netpair = (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net
  val rep_cs: claset ->
   {safeIs: thm Item_Net.T,
    safeEs: thm Item_Net.T,
    hazIs: thm Item_Net.T,
    hazEs: thm Item_Net.T,
    swrappers: (string * (Proof.context -> wrapper)) list,
    uwrappers: (string * (Proof.context -> wrapper)) list,
    safe0_netpair: netpair,
    safep_netpair: netpair,
    haz_netpair: netpair,
    dup_netpair: netpair,
    xtra_netpair: Context_Rules.netpair}
  val get_cs: Context.generic -> claset
  val map_cs: (claset -> claset) -> Context.generic -> Context.generic
  val safe_dest: int option -> attribute
  val safe_elim: int option -> attribute
  val safe_intro: int option -> attribute
  val haz_dest: int option -> attribute
  val haz_elim: int option -> attribute
  val haz_intro: int option -> attribute
  val rule_del: attribute
  val cla_modifiers: Method.modifier parser list
  val cla_method:
    (Proof.context -> tactic) -> (Proof.context -> Proof.method) context_parser
  val cla_method':
    (Proof.context -> int -> tactic) -> (Proof.context -> Proof.method) context_parser
  val setup: theory -> theory
end;


functor Classical(Data: CLASSICAL_DATA): CLASSICAL =
struct

(** classical elimination rules **)

(*
Classical reasoning requires stronger elimination rules.  For
instance, make_elim of Pure transforms the HOL rule injD into

    [| inj f; f x = f y; x = y ==> PROP W |] ==> PROP W

Such rules can cause fast_tac to fail and blast_tac to report "PROOF
FAILED"; classical_rule will strenthen this to

    [| inj f; ~ W ==> f x = f y; x = y ==> W |] ==> W
*)

fun classical_rule rule =
  if is_some (Object_Logic.elim_concl rule) then
    let
      val rule' = rule RS Data.classical;
      val concl' = Thm.concl_of rule';
      fun redundant_hyp goal =
        concl' aconv Logic.strip_assums_concl goal orelse
          (case Logic.strip_assums_hyp goal of
            hyp :: hyps => exists (fn t => t aconv hyp) hyps
          | _ => false);
      val rule'' =
        rule' |> ALLGOALS (SUBGOAL (fn (goal, i) =>
          if i = 1 orelse redundant_hyp goal
          then Tactic.etac thin_rl i
          else all_tac))
        |> Seq.hd
        |> Drule.zero_var_indexes;
    in if Thm.equiv_thm (rule, rule'') then rule else rule'' end
  else rule;

(*flatten nested meta connectives in prems*)
val flat_rule = Conv.fconv_rule (Conv.prems_conv ~1 Object_Logic.atomize_prems);


(*** Useful tactics for classical reasoning ***)

(*Prove goal that assumes both P and ~P.
  No backtracking if it finds an equal assumption.  Perhaps should call
  ematch_tac instead of eresolve_tac, but then cannot prove ZF/cantor.*)
val contr_tac =
  eresolve_tac [Data.not_elim] THEN' (eq_assume_tac ORELSE' assume_tac);

(*Finds P-->Q and P in the assumptions, replaces implication by Q.
  Could do the same thing for P<->Q and P... *)
fun mp_tac i = eresolve_tac [Data.not_elim, Data.imp_elim] i THEN assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = ematch_tac [Data.not_elim, Data.imp_elim] i THEN eq_assume_tac i;

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [Data.swap]);
val swapped = Thm.rule_attribute (fn _ => fn th => th RSN (2, Data.swap));

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac rls =
  let fun addrl rl brls = (false, rl) :: (true, rl RSN (2, Data.swap)) :: brls in
    assume_tac ORELSE'
    contr_tac ORELSE'
    biresolve_tac (fold_rev addrl rls [])
  end;

(*Duplication of hazardous rules, for complete provers*)
fun dup_intr th = zero_var_indexes (th RS Data.classical);

fun dup_elim th =  (* FIXME proper context!? *)
  let
    val rl = (th RSN (2, revcut_rl)) |> Thm.assumption 2 |> Seq.hd;
    val ctxt = Proof_Context.init_global (Thm.theory_of_thm rl);
  in rule_by_tactic ctxt (TRYALL (etac revcut_rl)) rl end;


(**** Classical rule sets ****)

type netpair = (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net;
type wrapper = (int -> tactic) -> int -> tactic;

datatype claset =
  CS of
   {safeIs         : thm Item_Net.T,          (*safe introduction rules*)
    safeEs         : thm Item_Net.T,          (*safe elimination rules*)
    hazIs          : thm Item_Net.T,          (*unsafe introduction rules*)
    hazEs          : thm Item_Net.T,          (*unsafe elimination rules*)
    swrappers      : (string * (Proof.context -> wrapper)) list, (*for transforming safe_step_tac*)
    uwrappers      : (string * (Proof.context -> wrapper)) list, (*for transforming step_tac*)
    safe0_netpair  : netpair,                 (*nets for trivial cases*)
    safep_netpair  : netpair,                 (*nets for >0 subgoals*)
    haz_netpair    : netpair,                 (*nets for unsafe rules*)
    dup_netpair    : netpair,                 (*nets for duplication*)
    xtra_netpair   : Context_Rules.netpair};  (*nets for extra rules*)

(*Desired invariants are
        safe0_netpair = build safe0_brls,
        safep_netpair = build safep_brls,
        haz_netpair = build (joinrules(hazIs, hazEs)),
        dup_netpair = build (joinrules(map dup_intr hazIs,
                                       map dup_elim hazEs))

where build = build_netpair(Net.empty,Net.empty),
      safe0_brls contains all brules that solve the subgoal, and
      safep_brls contains all brules that generate 1 or more new subgoals.
The theorem lists are largely comments, though they are used in merge_cs and print_cs.
Nets must be built incrementally, to save space and time.
*)

val empty_netpair = (Net.empty, Net.empty);

val empty_cs =
  CS
   {safeIs = Thm.full_rules,
    safeEs = Thm.full_rules,
    hazIs = Thm.full_rules,
    hazEs = Thm.full_rules,
    swrappers = [],
    uwrappers = [],
    safe0_netpair = empty_netpair,
    safep_netpair = empty_netpair,
    haz_netpair = empty_netpair,
    dup_netpair = empty_netpair,
    xtra_netpair = empty_netpair};

fun rep_cs (CS args) = args;


(*** Adding (un)safe introduction or elimination rules.

    In case of overlap, new rules are tried BEFORE old ones!!
***)

(*For use with biresolve_tac.  Combines intro rules with swap to handle negated
  assumptions.  Pairs elim rules with true. *)
fun joinrules (intrs, elims) =
  (map (pair true) (elims @ swapify intrs)) @ map (pair false) intrs;

fun joinrules' (intrs, elims) =
  map (pair true) elims @ map (pair false) intrs;

(*Priority: prefer rules with fewest subgoals,
  then rules added most recently (preferring the head of the list).*)
fun tag_brls k [] = []
  | tag_brls k (brl::brls) =
      (1000000*subgoals_of_brl brl + k, brl) ::
      tag_brls (k+1) brls;

fun tag_brls' _ _ [] = []
  | tag_brls' w k (brl::brls) = ((w, k), brl) :: tag_brls' w (k + 1) brls;

fun insert_tagged_list rls = fold_rev Tactic.insert_tagged_brl rls;

(*Insert into netpair that already has nI intr rules and nE elim rules.
  Count the intr rules double (to account for swapify).  Negate to give the
  new insertions the lowest priority.*)
fun insert (nI, nE) = insert_tagged_list o (tag_brls (~(2*nI+nE))) o joinrules;
fun insert' w (nI, nE) = insert_tagged_list o tag_brls' w (~(nI + nE)) o joinrules';

fun delete_tagged_list rls = fold_rev Tactic.delete_tagged_brl rls;
fun delete x = delete_tagged_list (joinrules x);
fun delete' x = delete_tagged_list (joinrules' x);

fun string_of_thm NONE = Display.string_of_thm_without_context
  | string_of_thm (SOME context) = Display.string_of_thm (Context.proof_of context);

fun make_elim context th =
  if has_fewer_prems 1 th then
    error ("Ill-formed destruction rule\n" ^ string_of_thm context th)
  else Tactic.make_elim th;

fun warn_thm opt_context msg th =
  if (case opt_context of SOME context => Context_Position.is_visible_proof context | NONE => false)
  then warning (msg ^ string_of_thm opt_context th)
  else ();

fun warn_rules context msg rules th =
  Item_Net.member rules th andalso (warn_thm context msg th; true);

fun warn_claset context th (CS {safeIs, safeEs, hazIs, hazEs, ...}) =
  warn_rules context "Rule already declared as safe introduction (intro!)\n" safeIs th orelse
  warn_rules context "Rule already declared as safe elimination (elim!)\n" safeEs th orelse
  warn_rules context "Rule already declared as introduction (intro)\n" hazIs th orelse
  warn_rules context "Rule already declared as elimination (elim)\n" hazEs th;


(*** Safe rules ***)

fun addSI w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate safe introduction (intro!)\n" safeIs th then cs
  else
    let
      val th' = flat_rule th;
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
        List.partition Thm.no_prems [th'];
      val nI = Item_Net.length safeIs + 1;
      val nE = Item_Net.length safeEs;
      val _ = warn_claset context th cs;
    in
      CS
       {safeIs = Item_Net.update th safeIs,
        safe0_netpair = insert (nI,nE) (safe0_rls, []) safe0_netpair,
        safep_netpair = insert (nI,nE) (safep_rls, []) safep_netpair,
        safeEs = safeEs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = insert' (the_default 0 w) (nI,nE) ([th], []) xtra_netpair}
    end;

fun addSE w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate safe elimination (elim!)\n" safeEs th then cs
  else if has_fewer_prems 1 th then
    error ("Ill-formed elimination rule\n" ^ string_of_thm context th)
  else
    let
      val th' = classical_rule (flat_rule th);
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
        List.partition (fn rl => nprems_of rl=1) [th'];
      val nI = Item_Net.length safeIs;
      val nE = Item_Net.length safeEs + 1;
      val _ = warn_claset context th cs;
    in
      CS
       {safeEs = Item_Net.update th safeEs,
        safe0_netpair = insert (nI,nE) ([], safe0_rls) safe0_netpair,
        safep_netpair = insert (nI,nE) ([], safep_rls) safep_netpair,
        safeIs = safeIs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = insert' (the_default 0 w) (nI,nE) ([], [th]) xtra_netpair}
    end;

fun addSD w context th = addSE w context (make_elim context th);


(*** Hazardous (unsafe) rules ***)

fun addI w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate introduction (intro)\n" hazIs th then cs
  else
    let
      val th' = flat_rule th;
      val nI = Item_Net.length hazIs + 1;
      val nE = Item_Net.length hazEs;
      val _ = warn_claset context th cs;
    in
      CS
       {hazIs = Item_Net.update th hazIs,
        haz_netpair = insert (nI, nE) ([th'], []) haz_netpair,
        dup_netpair = insert (nI, nE) ([dup_intr th'], []) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = insert' (the_default 1 w) (nI, nE) ([th], []) xtra_netpair}
    end
    handle THM ("RSN: no unifiers", _, _) => (*from dup_intr*)  (* FIXME !? *)
      error ("Ill-formed introduction rule\n" ^ string_of_thm context th);

fun addE w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate elimination (elim)\n" hazEs th then cs
  else if has_fewer_prems 1 th then
    error ("Ill-formed elimination rule\n" ^ string_of_thm context th)
  else
    let
      val th' = classical_rule (flat_rule th);
      val nI = Item_Net.length hazIs;
      val nE = Item_Net.length hazEs + 1;
      val _ = warn_claset context th cs;
    in
      CS
       {hazEs = Item_Net.update th hazEs,
        haz_netpair = insert (nI, nE) ([], [th']) haz_netpair,
        dup_netpair = insert (nI, nE) ([], [dup_elim th']) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazIs = hazIs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = insert' (the_default 1 w) (nI, nE) ([], [th]) xtra_netpair}
    end;

fun addD w context th = addE w context (make_elim context th);



(*** Deletion of rules
     Working out what to delete, requires repeating much of the code used
        to insert.
***)

fun delSI th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member safeIs th then
    let
      val th' = flat_rule th;
      val (safe0_rls, safep_rls) = List.partition Thm.no_prems [th'];
    in
      CS
       {safe0_netpair = delete (safe0_rls, []) safe0_netpair,
        safep_netpair = delete (safep_rls, []) safep_netpair,
        safeIs = Item_Net.remove th safeIs,
        safeEs = safeEs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = delete' ([th], []) xtra_netpair}
    end
  else cs;

fun delSE th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member safeEs th then
    let
      val th' = classical_rule (flat_rule th);
      val (safe0_rls, safep_rls) = List.partition (fn rl => nprems_of rl = 1) [th'];
    in
      CS
       {safe0_netpair = delete ([], safe0_rls) safe0_netpair,
        safep_netpair = delete ([], safep_rls) safep_netpair,
        safeIs = safeIs,
        safeEs = Item_Net.remove th safeEs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = delete' ([], [th]) xtra_netpair}
    end
  else cs;

fun delI context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member hazIs th then
    let val th' = flat_rule th in
      CS
       {haz_netpair = delete ([th'], []) haz_netpair,
        dup_netpair = delete ([dup_intr th'], []) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazIs = Item_Net.remove th hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([th], []) xtra_netpair}
    end
  else cs
  handle THM ("RSN: no unifiers", _, _) => (*from dup_intr*)  (* FIXME !? *)
    error ("Ill-formed introduction rule\n" ^ string_of_thm context th);

fun delE th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member hazEs th then
    let val th' = classical_rule (flat_rule th) in
      CS
       {haz_netpair = delete ([], [th']) haz_netpair,
        dup_netpair = delete ([], [dup_elim th']) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazIs = hazIs,
        hazEs = Item_Net.remove th hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([], [th]) xtra_netpair}
    end
  else cs;

(*Delete ALL occurrences of "th" in the claset (perhaps from several lists)*)
fun delrule context th (cs as CS {safeIs, safeEs, hazIs, hazEs, ...}) =
  let val th' = Tactic.make_elim th in
    if Item_Net.member safeIs th orelse Item_Net.member safeEs th orelse
      Item_Net.member hazIs th orelse Item_Net.member hazEs th orelse
      Item_Net.member safeEs th' orelse Item_Net.member hazEs th'
    then delSI th (delSE th (delI context th (delE th (delSE th' (delE th' cs)))))
    else (warn_thm context "Undeclared classical rule\n" th; cs)
  end;



(** claset data **)

(* wrappers *)

fun map_swrappers f
  (CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};

fun map_uwrappers f
  (CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = swrappers, uwrappers = f uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};


(* merge_cs *)

(*Merge works by adding all new rules of the 2nd claset into the 1st claset,
  in order to preserve priorities reliably.*)

fun merge_thms add thms1 thms2 =
  fold_rev (fn thm => if Item_Net.member thms1 thm then I else add thm) (Item_Net.content thms2);

fun merge_cs (cs as CS {safeIs, safeEs, hazIs, hazEs, ...},
    cs' as CS {safeIs = safeIs2, safeEs = safeEs2, hazIs = hazIs2, hazEs = hazEs2,
      swrappers, uwrappers, ...}) =
  if pointer_eq (cs, cs') then cs
  else
    cs
    |> merge_thms (addSI NONE NONE) safeIs safeIs2
    |> merge_thms (addSE NONE NONE) safeEs safeEs2
    |> merge_thms (addI NONE NONE) hazIs hazIs2
    |> merge_thms (addE NONE NONE) hazEs hazEs2
    |> map_swrappers (fn ws => AList.merge (op =) (K true) (ws, swrappers))
    |> map_uwrappers (fn ws => AList.merge (op =) (K true) (ws, uwrappers));


(* data *)

structure Claset = Generic_Data
(
  type T = claset;
  val empty = empty_cs;
  val extend = I;
  val merge = merge_cs;
);

val global_claset_of = Claset.get o Context.Theory;
val claset_of = Claset.get o Context.Proof;
val rep_claset_of = rep_cs o claset_of;

val get_cs = Claset.get;
val map_cs = Claset.map;

fun map_claset f = Context.proof_map (map_cs f);
fun put_claset cs = map_claset (K cs);

fun print_claset ctxt =
  let
    val {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers, ...} = rep_claset_of ctxt;
    val pretty_thms = map (Display.pretty_thm ctxt) o Item_Net.content;
  in
    [Pretty.big_list "safe introduction rules (intro!):" (pretty_thms safeIs),
      Pretty.big_list "introduction rules (intro):" (pretty_thms hazIs),
      Pretty.big_list "safe elimination rules (elim!):" (pretty_thms safeEs),
      Pretty.big_list "elimination rules (elim):" (pretty_thms hazEs),
      Pretty.strs ("safe wrappers:" :: map #1 swrappers),
      Pretty.strs ("unsafe wrappers:" :: map #1 uwrappers)]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* old-style declarations *)

fun decl f (ctxt, ths) = map_claset (fold_rev (f (SOME (Context.Proof ctxt))) ths) ctxt;

val op addSIs = decl (addSI NONE);
val op addSEs = decl (addSE NONE);
val op addSDs = decl (addSD NONE);
val op addIs = decl (addI NONE);
val op addEs = decl (addE NONE);
val op addDs = decl (addD NONE);
val op delrules = decl delrule;



(*** Modifying the wrapper tacticals ***)

fun appSWrappers ctxt = fold (fn (_, w) => w ctxt) (#swrappers (rep_claset_of ctxt));
fun appWrappers ctxt = fold (fn (_, w) => w ctxt) (#uwrappers (rep_claset_of ctxt));

fun update_warn msg (p as (key : string, _)) xs =
  (if AList.defined (op =) xs key then warning msg else (); AList.update (op =) p xs);

fun delete_warn msg (key : string) xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else (warning msg; xs);

(*Add/replace a safe wrapper*)
fun cs addSWrapper new_swrapper =
  map_swrappers (update_warn ("Overwriting safe wrapper " ^ fst new_swrapper) new_swrapper) cs;

(*Add/replace an unsafe wrapper*)
fun cs addWrapper new_uwrapper =
  map_uwrappers (update_warn ("Overwriting unsafe wrapper " ^ fst new_uwrapper) new_uwrapper) cs;

(*Remove a safe wrapper*)
fun cs delSWrapper name =
  map_swrappers (delete_warn ("No such safe wrapper in claset: " ^ name) name) cs;

(*Remove an unsafe wrapper*)
fun cs delWrapper name =
  map_uwrappers (delete_warn ("No such unsafe wrapper in claset: " ^ name) name) cs;

(* compose a safe tactic alternatively before/after safe_step_tac *)
fun cs addSbefore (name, tac1) = cs addSWrapper (name, fn _ => fn tac2 => tac1 ORELSE' tac2);
fun cs addSafter (name, tac2) = cs addSWrapper (name, fn _ => fn tac1 => tac1 ORELSE' tac2);

(*compose a tactic alternatively before/after the step tactic *)
fun cs addbefore (name, tac1) = cs addWrapper (name, fn _ => fn tac2 => tac1 APPEND' tac2);
fun cs addafter (name, tac2) = cs addWrapper (name, fn _ => fn tac1 => tac1 APPEND' tac2);

fun cs addD2 (name, thm) = cs addafter (name, dtac thm THEN' assume_tac);
fun cs addE2 (name, thm) = cs addafter (name, etac thm THEN' assume_tac);
fun cs addSD2 (name, thm) = cs addSafter (name, dmatch_tac [thm] THEN' eq_assume_tac);
fun cs addSE2 (name, thm) = cs addSafter (name, ematch_tac [thm] THEN' eq_assume_tac);



(**** Simple tactics for theorem proving ****)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun safe_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    appSWrappers ctxt
      (FIRST'
       [eq_assume_tac,
        eq_mp_tac,
        bimatch_from_nets_tac safe0_netpair,
        FIRST' Data.hyp_subst_tacs,
        bimatch_from_nets_tac safep_netpair])
  end;

(*Repeatedly attack a subgoal using safe inferences -- it's deterministic!*)
fun safe_steps_tac ctxt =
  REPEAT_DETERM1 o (fn i => COND (has_fewer_prems i) no_tac (safe_step_tac ctxt i));

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun safe_tac ctxt = REPEAT_DETERM1 (FIRSTGOAL (safe_steps_tac ctxt));


(*** Clarify_tac: do safe steps without causing branching ***)

fun nsubgoalsP n (k, brl) = (subgoals_of_brl brl = n);

(*version of bimatch_from_nets_tac that only applies rules that
  create precisely n subgoals.*)
fun n_bimatch_from_nets_tac n =
  biresolution_from_nets_tac (order_list o filter (nsubgoalsP n)) true;

fun eq_contr_tac i = ematch_tac [Data.not_elim] i THEN eq_assume_tac i;
val eq_assume_contr_tac = eq_assume_tac ORELSE' eq_contr_tac;

(*Two-way branching is allowed only if one of the branches immediately closes*)
fun bimatch2_tac netpair i =
  n_bimatch_from_nets_tac 2 netpair i THEN
  (eq_assume_contr_tac i ORELSE eq_assume_contr_tac (i + 1));

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun clarify_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    appSWrappers ctxt
     (FIRST'
       [eq_assume_contr_tac,
        bimatch_from_nets_tac safe0_netpair,
        FIRST' Data.hyp_subst_tacs,
        n_bimatch_from_nets_tac 1 safep_netpair,
        bimatch2_tac safep_netpair])
  end;

fun clarify_tac ctxt = SELECT_GOAL (REPEAT_DETERM (clarify_step_tac ctxt 1));


(*** Unsafe steps instantiate variables or lose information ***)

(*Backtracking is allowed among the various these unsafe ways of
  proving a subgoal.  *)
fun inst0_step_tac ctxt =
  assume_tac APPEND'
  contr_tac APPEND'
  biresolve_from_nets_tac (#safe0_netpair (rep_claset_of ctxt));

(*These unsafe steps could generate more subgoals.*)
fun instp_step_tac ctxt =
  biresolve_from_nets_tac (#safep_netpair (rep_claset_of ctxt));

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac ctxt = inst0_step_tac ctxt APPEND' instp_step_tac ctxt;

fun haz_step_tac ctxt =
  biresolve_from_nets_tac (#haz_netpair (rep_claset_of ctxt));

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac ctxt i =
  safe_tac ctxt ORELSE appWrappers ctxt (inst_step_tac ctxt ORELSE' haz_step_tac ctxt) i;

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac ctxt i =
  safe_tac ctxt ORELSE appWrappers ctxt (inst_step_tac ctxt APPEND' haz_step_tac ctxt) i;


(**** The following tactics all fail unless they solve one goal ****)

(*Dumb but fast*)
fun fast_tac ctxt =
  Object_Logic.atomize_prems_tac THEN' SELECT_GOAL (DEPTH_SOLVE (step_tac ctxt 1));

(*Slower but smarter than fast_tac*)
fun best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (step_tac ctxt 1));

(*even a bit smarter than best_tac*)
fun first_best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (FIRSTGOAL (step_tac ctxt)));

fun slow_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (DEPTH_SOLVE (slow_step_tac ctxt 1));

fun slow_best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (slow_step_tac ctxt 1));


(***ASTAR with weight weight_ASTAR, by Norbert Voelker*)

val weight_ASTAR = 5;

fun astar_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + weight_ASTAR * lev)
      (step_tac ctxt 1));

fun slow_astar_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + weight_ASTAR * lev)
      (slow_step_tac ctxt 1));


(**** Complete tactic, loosely based upon LeanTaP.  This tactic is the outcome
  of much experimentation!  Changing APPEND to ORELSE below would prove
  easy theorems faster, but loses completeness -- and many of the harder
  theorems such as 43. ****)

(*Non-deterministic!  Could always expand the first unsafe connective.
  That's hard to implement and did not perform better in experiments, due to
  greater search depth required.*)
fun dup_step_tac ctxt =
  biresolve_from_nets_tac (#dup_netpair (rep_claset_of ctxt));

(*Searching to depth m. A variant called nodup_depth_tac appears in clasimp.ML*)
local
  fun slow_step_tac' ctxt = appWrappers ctxt (instp_step_tac ctxt APPEND' dup_step_tac ctxt);
in
  fun depth_tac ctxt m i state = SELECT_GOAL
    (safe_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (depth_tac ctxt m 1),
        inst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (slow_step_tac' ctxt 1 THEN DEPTH_SOLVE (depth_tac ctxt (m - 1) 1)))) i state;
end;

(*Search, with depth bound m.
  This is the "entry point", which does safe inferences first.*)
fun safe_depth_tac ctxt m = SUBGOAL (fn (prem, i) =>
  let
    val deti = (*No Vars in the goal?  No need to backtrack between goals.*)
      if exists_subterm (fn Var _ => true | _ => false) prem then DETERM else I;
  in
    SELECT_GOAL (TRY (safe_tac ctxt) THEN DEPTH_SOLVE (deti (depth_tac ctxt m 1))) i
  end);

fun deepen_tac ctxt = DEEPEN (2, 10) (safe_depth_tac ctxt);


(* attributes *)

fun attrib f =
  Thm.declaration_attribute (fn th => fn context => map_cs (f (SOME context) th) context);

val safe_elim = attrib o addSE;
val safe_intro = attrib o addSI;
val safe_dest = attrib o addSD;
val haz_elim = attrib o addE;
val haz_intro = attrib o addI;
val haz_dest = attrib o addD;

val rule_del =
  Thm.declaration_attribute (fn th => fn context =>
    context |> map_cs (delrule (SOME context) th) |>
    Thm.attribute_declaration Context_Rules.rule_del th);



(** concrete syntax of attributes **)

val introN = "intro";
val elimN = "elim";
val destN = "dest";

val setup_attrs =
  Attrib.setup @{binding swapped} (Scan.succeed swapped)
    "classical swap of introduction rule" #>
  Attrib.setup @{binding dest} (Context_Rules.add safe_dest haz_dest Context_Rules.dest_query)
    "declaration of Classical destruction rule" #>
  Attrib.setup @{binding elim} (Context_Rules.add safe_elim haz_elim Context_Rules.elim_query)
    "declaration of Classical elimination rule" #>
  Attrib.setup @{binding intro} (Context_Rules.add safe_intro haz_intro Context_Rules.intro_query)
    "declaration of Classical introduction rule" #>
  Attrib.setup @{binding rule} (Scan.lift Args.del >> K rule_del)
    "remove declaration of intro/elim/dest rule";



(** proof methods **)

local

fun some_rule_tac ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = Context_Rules.find_rules false facts goal ctxt;
    val {xtra_netpair, ...} = rep_claset_of ctxt;
    val rules3 = Context_Rules.find_rules_netpair true facts goal xtra_netpair;
    val rules = rules1 @ rules2 @ rules3 @ rules4;
    val ruleq = Drule.multi_resolves facts rules;
  in
    Method.trace ctxt rules;
    fn st => Seq.maps (fn rule => Tactic.rtac rule i st) ruleq
  end)
  THEN_ALL_NEW Goal.norm_hhf_tac;

in

fun rule_tac ctxt [] facts = some_rule_tac ctxt facts
  | rule_tac _ rules facts = Method.rule_tac rules facts;

fun default_tac ctxt rules facts =
  HEADGOAL (rule_tac ctxt rules facts) ORELSE
  Class.default_intro_tac ctxt facts;

end;


(* contradiction method *)

val contradiction = Method.rule [Data.not_elim, Data.not_elim COMP Drule.swap_prems_rl];


(* automatic methods *)

val cla_modifiers =
 [Args.$$$ destN -- Args.bang_colon >> K ((I, safe_dest NONE): Method.modifier),
  Args.$$$ destN -- Args.colon >> K (I, haz_dest NONE),
  Args.$$$ elimN -- Args.bang_colon >> K (I, safe_elim NONE),
  Args.$$$ elimN -- Args.colon >> K (I, haz_elim NONE),
  Args.$$$ introN -- Args.bang_colon >> K (I, safe_intro NONE),
  Args.$$$ introN -- Args.colon >> K (I, haz_intro NONE),
  Args.del -- Args.colon >> K (I, rule_del)];

fun cla_method tac = Method.sections cla_modifiers >> K (SIMPLE_METHOD o tac);
fun cla_method' tac = Method.sections cla_modifiers >> K (SIMPLE_METHOD' o tac);



(** setup_methods **)

val setup_methods =
  Method.setup @{binding default}
   (Attrib.thms >> (fn rules => fn ctxt => METHOD (default_tac ctxt rules)))
    "apply some intro/elim rule (potentially classical)" #>
  Method.setup @{binding rule}
    (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o rule_tac ctxt rules)))
    "apply some intro/elim rule (potentially classical)" #>
  Method.setup @{binding contradiction} (Scan.succeed (K contradiction))
    "proof by contradiction" #>
  Method.setup @{binding clarify} (cla_method' (CHANGED_PROP oo clarify_tac))
    "repeatedly apply safe steps" #>
  Method.setup @{binding fast} (cla_method' fast_tac) "classical prover (depth-first)" #>
  Method.setup @{binding slow} (cla_method' slow_tac) "classical prover (slow depth-first)" #>
  Method.setup @{binding best} (cla_method' best_tac) "classical prover (best-first)" #>
  Method.setup @{binding deepen}
    (Scan.lift (Scan.optional Parse.nat 4) --| Method.sections cla_modifiers
      >> (fn n => fn ctxt => SIMPLE_METHOD' (deepen_tac ctxt n)))
    "classical prover (iterative deepening)" #>
  Method.setup @{binding safe} (cla_method (CHANGED_PROP o safe_tac))
    "classical prover (apply safe rules)";



(** theory setup **)

val setup = setup_attrs #> setup_methods;



(** outer syntax **)

val _ =
  Outer_Syntax.improper_command "print_claset" "print context of Classical Reasoner"
    Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (fn state =>
        let val ctxt = Toplevel.context_of state
        in print_claset ctxt end)));

end;
