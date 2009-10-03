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


(*should be a type abbreviation in signature CLASSICAL*)
type netpair = (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net;
type wrapper = (int -> tactic) -> (int -> tactic);

signature CLASSICAL_DATA =
sig
  val imp_elim  : thm           (* P --> Q ==> (~ R ==> P) ==> (Q ==> R) ==> R *)
  val not_elim  : thm           (* ~P ==> P ==> R *)
  val swap      : thm           (* ~ P ==> (~ R ==> P) ==> R *)
  val classical : thm           (* (~ P ==> P) ==> P *)
  val sizef     : thm -> int    (* size function for BEST_FIRST *)
  val hyp_subst_tacs: (int -> tactic) list
end;

signature BASIC_CLASSICAL =
sig
  type claset
  val empty_cs: claset
  val print_cs: claset -> unit
  val rep_cs:
    claset -> {safeIs: thm list, safeEs: thm list,
                 hazIs: thm list, hazEs: thm list,
                 swrappers: (string * wrapper) list,
                 uwrappers: (string * wrapper) list,
                 safe0_netpair: netpair, safep_netpair: netpair,
                 haz_netpair: netpair, dup_netpair: netpair,
                 xtra_netpair: ContextRules.netpair}
  val merge_cs          : claset * claset -> claset
  val addDs             : claset * thm list -> claset
  val addEs             : claset * thm list -> claset
  val addIs             : claset * thm list -> claset
  val addSDs            : claset * thm list -> claset
  val addSEs            : claset * thm list -> claset
  val addSIs            : claset * thm list -> claset
  val delrules          : claset * thm list -> claset
  val addSWrapper       : claset * (string * wrapper) -> claset
  val delSWrapper       : claset *  string            -> claset
  val addWrapper        : claset * (string * wrapper) -> claset
  val delWrapper        : claset *  string            -> claset
  val addSbefore        : claset * (string * (int -> tactic)) -> claset
  val addSafter         : claset * (string * (int -> tactic)) -> claset
  val addbefore         : claset * (string * (int -> tactic)) -> claset
  val addafter          : claset * (string * (int -> tactic)) -> claset
  val addD2             : claset * (string * thm) -> claset
  val addE2             : claset * (string * thm) -> claset
  val addSD2            : claset * (string * thm) -> claset
  val addSE2            : claset * (string * thm) -> claset
  val appSWrappers      : claset -> wrapper
  val appWrappers       : claset -> wrapper

  val global_claset_of  : theory -> claset
  val claset_of         : Proof.context -> claset

  val fast_tac          : claset -> int -> tactic
  val slow_tac          : claset -> int -> tactic
  val weight_ASTAR      : int Unsynchronized.ref
  val astar_tac         : claset -> int -> tactic
  val slow_astar_tac    : claset -> int -> tactic
  val best_tac          : claset -> int -> tactic
  val first_best_tac    : claset -> int -> tactic
  val slow_best_tac     : claset -> int -> tactic
  val depth_tac         : claset -> int -> int -> tactic
  val deepen_tac        : claset -> int -> int -> tactic

  val contr_tac         : int -> tactic
  val dup_elim          : thm -> thm
  val dup_intr          : thm -> thm
  val dup_step_tac      : claset -> int -> tactic
  val eq_mp_tac         : int -> tactic
  val haz_step_tac      : claset -> int -> tactic
  val joinrules         : thm list * thm list -> (bool * thm) list
  val mp_tac            : int -> tactic
  val safe_tac          : claset -> tactic
  val safe_steps_tac    : claset -> int -> tactic
  val safe_step_tac     : claset -> int -> tactic
  val clarify_tac       : claset -> int -> tactic
  val clarify_step_tac  : claset -> int -> tactic
  val step_tac          : claset -> int -> tactic
  val slow_step_tac     : claset -> int -> tactic
  val swapify           : thm list -> thm list
  val swap_res_tac      : thm list -> int -> tactic
  val inst_step_tac     : claset -> int -> tactic
  val inst0_step_tac    : claset -> int -> tactic
  val instp_step_tac    : claset -> int -> tactic
end;

signature CLASSICAL =
sig
  include BASIC_CLASSICAL
  val classical_rule: thm -> thm
  val add_context_safe_wrapper: string * (Proof.context -> wrapper) -> theory -> theory
  val del_context_safe_wrapper: string -> theory -> theory
  val add_context_unsafe_wrapper: string * (Proof.context -> wrapper) -> theory -> theory
  val del_context_unsafe_wrapper: string -> theory -> theory
  val get_claset: Proof.context -> claset
  val put_claset: claset -> Proof.context -> Proof.context
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
  val cla_meth: (claset -> tactic) -> thm list -> Proof.context -> Proof.method
  val cla_meth': (claset -> int -> tactic) -> thm list -> Proof.context -> Proof.method
  val cla_method: (claset -> tactic) -> (Proof.context -> Proof.method) context_parser
  val cla_method': (claset -> int -> tactic) -> (Proof.context -> Proof.method) context_parser
  val setup: theory -> theory
end;


functor ClassicalFun(Data: CLASSICAL_DATA): CLASSICAL =
struct

local open Data in

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
  if ObjectLogic.is_elim rule then
    let
      val rule' = rule RS classical;
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
val flat_rule = Conv.fconv_rule (Conv.prems_conv ~1 ObjectLogic.atomize_prems);


(*** Useful tactics for classical reasoning ***)

(*Prove goal that assumes both P and ~P.
  No backtracking if it finds an equal assumption.  Perhaps should call
  ematch_tac instead of eresolve_tac, but then cannot prove ZF/cantor.*)
val contr_tac = eresolve_tac [not_elim]  THEN'
                (eq_assume_tac ORELSE' assume_tac);

(*Finds P-->Q and P in the assumptions, replaces implication by Q.
  Could do the same thing for P<->Q and P... *)
fun mp_tac i = eresolve_tac [not_elim, Data.imp_elim] i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = ematch_tac [not_elim, Data.imp_elim] i  THEN  eq_assume_tac i;

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [Data.swap]);
val swapped = Thm.rule_attribute (fn _ => fn th => th RSN (2, Data.swap));

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac rls =
    let fun addrl (rl,brls) = (false, rl) :: (true, rl RSN (2, Data.swap)) :: brls
    in  assume_tac      ORELSE'
        contr_tac       ORELSE'
        biresolve_tac (List.foldr addrl [] rls)
    end;

(*Duplication of hazardous rules, for complete provers*)
fun dup_intr th = zero_var_indexes (th RS classical);

fun dup_elim th =
    rule_by_tactic (TRYALL (etac revcut_rl))
      ((th RSN (2, revcut_rl)) |> Thm.assumption 2 |> Seq.hd);

(**** Classical rule sets ****)

datatype claset =
  CS of {safeIs         : thm list,                (*safe introduction rules*)
         safeEs         : thm list,                (*safe elimination rules*)
         hazIs          : thm list,                (*unsafe introduction rules*)
         hazEs          : thm list,                (*unsafe elimination rules*)
         swrappers      : (string * wrapper) list, (*for transforming safe_step_tac*)
         uwrappers      : (string * wrapper) list, (*for transforming step_tac*)
         safe0_netpair  : netpair,                 (*nets for trivial cases*)
         safep_netpair  : netpair,                 (*nets for >0 subgoals*)
         haz_netpair    : netpair,                 (*nets for unsafe rules*)
         dup_netpair    : netpair,                 (*nets for duplication*)
         xtra_netpair   : ContextRules.netpair};   (*nets for extra rules*)

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
  CS{safeIs     = [],
     safeEs     = [],
     hazIs      = [],
     hazEs      = [],
     swrappers  = [],
     uwrappers  = [],
     safe0_netpair = empty_netpair,
     safep_netpair = empty_netpair,
     haz_netpair   = empty_netpair,
     dup_netpair   = empty_netpair,
     xtra_netpair  = empty_netpair};

fun print_cs (CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers, ...}) =
  let val pretty_thms = map Display.pretty_thm_without_context in
    [Pretty.big_list "safe introduction rules (intro!):" (pretty_thms safeIs),
      Pretty.big_list "introduction rules (intro):" (pretty_thms hazIs),
      Pretty.big_list "safe elimination rules (elim!):" (pretty_thms safeEs),
      Pretty.big_list "elimination rules (elim):" (pretty_thms hazEs),
      Pretty.strs ("safe wrappers:" :: map #1 swrappers),
      Pretty.strs ("unsafe wrappers:" :: map #1 uwrappers)]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun rep_cs (CS args) = args;

fun appSWrappers (CS {swrappers, ...}) = fold snd swrappers;
fun appWrappers  (CS {uwrappers, ...}) = fold snd uwrappers;


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

val mem_thm = member Thm.eq_thm_prop
and rem_thm = remove Thm.eq_thm_prop;

(*Warn if the rule is already present ELSEWHERE in the claset.  The addition
  is still allowed.*)
fun warn_dup th (CS{safeIs, safeEs, hazIs, hazEs, ...}) =
  if mem_thm safeIs th then
    warning ("Rule already declared as safe introduction (intro!)\n" ^
      Display.string_of_thm_without_context th)
  else if mem_thm safeEs th then
    warning ("Rule already declared as safe elimination (elim!)\n" ^
      Display.string_of_thm_without_context th)
  else if mem_thm hazIs th then
    warning ("Rule already declared as introduction (intro)\n" ^
      Display.string_of_thm_without_context th)
  else if mem_thm hazEs th then
    warning ("Rule already declared as elimination (elim)\n" ^
      Display.string_of_thm_without_context th)
  else ();


(*** Safe rules ***)

fun addSI w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
             safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm safeIs th then
    (warning ("Ignoring duplicate safe introduction (intro!)\n" ^
      Display.string_of_thm_without_context th); cs)
  else
  let val th' = flat_rule th
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
          List.partition Thm.no_prems [th']
      val nI = length safeIs + 1
      and nE = length safeEs
  in warn_dup th cs;
     CS{safeIs  = th::safeIs,
        safe0_netpair = insert (nI,nE) (safe0_rls, []) safe0_netpair,
        safep_netpair = insert (nI,nE) (safep_rls, []) safep_netpair,
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        swrappers    = swrappers,
        uwrappers    = uwrappers,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair,
        xtra_netpair = insert' (the_default 0 w) (nI,nE) ([th], []) xtra_netpair}
  end;

fun addSE w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
             safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm safeEs th then
    (warning ("Ignoring duplicate safe elimination (elim!)\n" ^
        Display.string_of_thm_without_context th); cs)
  else if has_fewer_prems 1 th then
    	error ("Ill-formed elimination rule\n" ^ Display.string_of_thm_without_context th)
  else
  let
      val th' = classical_rule (flat_rule th)
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
          List.partition (fn rl => nprems_of rl=1) [th']
      val nI = length safeIs
      and nE = length safeEs + 1
  in warn_dup th cs;
     CS{safeEs  = th::safeEs,
        safe0_netpair = insert (nI,nE) ([], safe0_rls) safe0_netpair,
        safep_netpair = insert (nI,nE) ([], safep_rls) safep_netpair,
        safeIs  = safeIs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        swrappers    = swrappers,
        uwrappers    = uwrappers,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair,
        xtra_netpair = insert' (the_default 0 w) (nI,nE) ([], [th]) xtra_netpair}
  end;

fun cs addSIs ths = fold_rev (addSI NONE) ths cs;
fun cs addSEs ths = fold_rev (addSE NONE) ths cs;

fun make_elim th =
    if has_fewer_prems 1 th then
    	  error ("Ill-formed destruction rule\n" ^ Display.string_of_thm_without_context th)
    else Tactic.make_elim th;

fun cs addSDs ths = cs addSEs (map make_elim ths);


(*** Hazardous (unsafe) rules ***)

fun addI w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
             safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm hazIs th then
    (warning ("Ignoring duplicate introduction (intro)\n" ^
        Display.string_of_thm_without_context th); cs)
  else
  let val th' = flat_rule th
      val nI = length hazIs + 1
      and nE = length hazEs
  in warn_dup th cs;
     CS{hazIs   = th::hazIs,
        haz_netpair = insert (nI,nE) ([th'], []) haz_netpair,
        dup_netpair = insert (nI,nE) (map dup_intr [th'], []) dup_netpair,
        safeIs  = safeIs,
        safeEs  = safeEs,
        hazEs   = hazEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = insert' (the_default 1 w) (nI,nE) ([th], []) xtra_netpair}
  end
  handle THM("RSN: no unifiers",_,_) => (*from dup_intr*)
    error ("Ill-formed introduction rule\n" ^ Display.string_of_thm_without_context th);

fun addE w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
            safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm hazEs th then
    (warning ("Ignoring duplicate elimination (elim)\n" ^
        Display.string_of_thm_without_context th); cs)
  else if has_fewer_prems 1 th then
    	error("Ill-formed elimination rule\n" ^ Display.string_of_thm_without_context th)
  else
  let
      val th' = classical_rule (flat_rule th)
      val nI = length hazIs
      and nE = length hazEs + 1
  in warn_dup th cs;
     CS{hazEs   = th::hazEs,
        haz_netpair = insert (nI,nE) ([], [th']) haz_netpair,
        dup_netpair = insert (nI,nE) ([], map dup_elim [th']) dup_netpair,
        safeIs  = safeIs,
        safeEs  = safeEs,
        hazIs   = hazIs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = insert' (the_default 1 w) (nI,nE) ([], [th]) xtra_netpair}
  end;

fun cs addIs ths = fold_rev (addI NONE) ths cs;
fun cs addEs ths = fold_rev (addE NONE) ths cs;

fun cs addDs ths = cs addEs (map make_elim ths);


(*** Deletion of rules
     Working out what to delete, requires repeating much of the code used
        to insert.
***)

fun delSI th
          (cs as CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
                    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm safeIs th then
   let val th' = flat_rule th
       val (safe0_rls, safep_rls) = List.partition Thm.no_prems [th']
   in CS{safe0_netpair = delete (safe0_rls, []) safe0_netpair,
         safep_netpair = delete (safep_rls, []) safep_netpair,
         safeIs = rem_thm th safeIs,
         safeEs = safeEs,
         hazIs  = hazIs,
         hazEs  = hazEs,
         swrappers    = swrappers,
         uwrappers    = uwrappers,
         haz_netpair  = haz_netpair,
         dup_netpair  = dup_netpair,
         xtra_netpair = delete' ([th], []) xtra_netpair}
   end
 else cs;

fun delSE th
          (cs as CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
                    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm safeEs th then
    let
      val th' = classical_rule (flat_rule th)
      val (safe0_rls, safep_rls) = List.partition (fn rl => nprems_of rl=1) [th']
    in CS{safe0_netpair = delete ([], safe0_rls) safe0_netpair,
         safep_netpair = delete ([], safep_rls) safep_netpair,
         safeIs = safeIs,
         safeEs = rem_thm th safeEs,
         hazIs  = hazIs,
         hazEs  = hazEs,
         swrappers    = swrappers,
         uwrappers    = uwrappers,
         haz_netpair  = haz_netpair,
         dup_netpair  = dup_netpair,
         xtra_netpair = delete' ([], [th]) xtra_netpair}
    end
  else cs;


fun delI th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm hazIs th then
    let val th' = flat_rule th
    in CS{haz_netpair = delete ([th'], []) haz_netpair,
        dup_netpair = delete ([dup_intr th'], []) dup_netpair,
        safeIs  = safeIs,
        safeEs  = safeEs,
        hazIs   = rem_thm th hazIs,
        hazEs   = hazEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([th], []) xtra_netpair}
    end
 else cs
 handle THM("RSN: no unifiers",_,_) => (*from dup_intr*)
   error ("Ill-formed introduction rule\n" ^ Display.string_of_thm_without_context th);


fun delE th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm hazEs th then
   let val th' = classical_rule (flat_rule th)
   in CS{haz_netpair = delete ([], [th']) haz_netpair,
        dup_netpair = delete ([], [dup_elim th']) dup_netpair,
        safeIs  = safeIs,
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = rem_thm th hazEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([], [th]) xtra_netpair}
   end
 else cs;

(*Delete ALL occurrences of "th" in the claset (perhaps from several lists)*)
fun delrule th (cs as CS {safeIs, safeEs, hazIs, hazEs, ...}) =
  let val th' = Tactic.make_elim th in
    if mem_thm safeIs th orelse mem_thm safeEs th orelse
      mem_thm hazIs th orelse mem_thm hazEs th orelse
      mem_thm safeEs th' orelse mem_thm hazEs th'
    then delSI th (delSE th (delI th (delE th (delSE th' (delE th' cs)))))
    else (warning ("Undeclared classical rule\n" ^ Display.string_of_thm_without_context th); cs)
  end;

fun cs delrules ths = fold delrule ths cs;


(*** Modifying the wrapper tacticals ***)
fun map_swrappers f
  (CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};

fun map_uwrappers f
  (CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = swrappers, uwrappers = f uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};

fun update_warn msg (p as (key : string, _)) xs =
  (if AList.defined (op =) xs key then warning msg else ();
    AList.update (op =) p xs);

fun delete_warn msg (key : string) xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
    else (warning msg; xs);

(*Add/replace a safe wrapper*)
fun cs addSWrapper new_swrapper = map_swrappers
  (update_warn ("Overwriting safe wrapper " ^ fst new_swrapper) new_swrapper) cs;

(*Add/replace an unsafe wrapper*)
fun cs addWrapper new_uwrapper = map_uwrappers
  (update_warn ("Overwriting unsafe wrapper " ^ fst new_uwrapper) new_uwrapper) cs;

(*Remove a safe wrapper*)
fun cs delSWrapper name = map_swrappers
  (delete_warn ("No such safe wrapper in claset: " ^ name) name) cs;

(*Remove an unsafe wrapper*)
fun cs delWrapper name = map_uwrappers
  (delete_warn ("No such unsafe wrapper in claset: " ^ name) name) cs;

(* compose a safe tactic alternatively before/after safe_step_tac *)
fun cs addSbefore  (name,    tac1) =
    cs addSWrapper (name, fn tac2 => tac1 ORELSE' tac2);
fun cs addSafter   (name,    tac2) =
    cs addSWrapper (name, fn tac1 => tac1 ORELSE' tac2);

(*compose a tactic alternatively before/after the step tactic *)
fun cs addbefore   (name,    tac1) =
    cs addWrapper  (name, fn tac2 => tac1 APPEND' tac2);
fun cs addafter    (name,    tac2) =
    cs addWrapper  (name, fn tac1 => tac1 APPEND' tac2);

fun cs addD2     (name, thm) =
    cs addafter  (name, datac thm 1);
fun cs addE2     (name, thm) =
    cs addafter  (name, eatac thm 1);
fun cs addSD2    (name, thm) =
    cs addSafter (name, dmatch_tac [thm] THEN' eq_assume_tac);
fun cs addSE2    (name, thm) =
    cs addSafter (name, ematch_tac [thm] THEN' eq_assume_tac);

(*Merge works by adding all new rules of the 2nd claset into the 1st claset.
  Merging the term nets may look more efficient, but the rather delicate
  treatment of priority might get muddled up.*)
fun merge_cs (cs as CS {safeIs, safeEs, hazIs, hazEs, ...},
    cs' as CS {safeIs = safeIs2, safeEs = safeEs2, hazIs = hazIs2, hazEs = hazEs2,
      swrappers, uwrappers, ...}) =
  if pointer_eq (cs, cs') then cs
  else
    let
      val safeIs' = fold rem_thm safeIs safeIs2;
      val safeEs' = fold rem_thm safeEs safeEs2;
      val hazIs' = fold rem_thm hazIs hazIs2;
      val hazEs' = fold rem_thm hazEs hazEs2;
      val cs1   = cs addSIs safeIs'
                     addSEs safeEs'
                     addIs  hazIs'
                     addEs  hazEs';
      val cs2 = map_swrappers
        (fn ws => AList.merge (op =) (K true) (ws, swrappers)) cs1;
      val cs3 = map_uwrappers
        (fn ws => AList.merge (op =) (K true) (ws, uwrappers)) cs2;
    in cs3 end;


(**** Simple tactics for theorem proving ****)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun safe_step_tac (cs as CS{safe0_netpair,safep_netpair,...}) =
  appSWrappers cs (FIRST' [
        eq_assume_tac,
        eq_mp_tac,
        bimatch_from_nets_tac safe0_netpair,
        FIRST' hyp_subst_tacs,
        bimatch_from_nets_tac safep_netpair]);

(*Repeatedly attack a subgoal using safe inferences -- it's deterministic!*)
fun safe_steps_tac cs = REPEAT_DETERM1 o
        (fn i => COND (has_fewer_prems i) no_tac (safe_step_tac cs i));

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun safe_tac cs = REPEAT_DETERM1 (FIRSTGOAL (safe_steps_tac cs));


(*** Clarify_tac: do safe steps without causing branching ***)

fun nsubgoalsP n (k,brl) = (subgoals_of_brl brl = n);

(*version of bimatch_from_nets_tac that only applies rules that
  create precisely n subgoals.*)
fun n_bimatch_from_nets_tac n =
    biresolution_from_nets_tac (order_list o List.filter (nsubgoalsP n)) true;

fun eq_contr_tac i = ematch_tac [not_elim] i  THEN  eq_assume_tac i;
val eq_assume_contr_tac = eq_assume_tac ORELSE' eq_contr_tac;

(*Two-way branching is allowed only if one of the branches immediately closes*)
fun bimatch2_tac netpair i =
    n_bimatch_from_nets_tac 2 netpair i THEN
    (eq_assume_contr_tac i ORELSE eq_assume_contr_tac (i+1));

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun clarify_step_tac (cs as CS{safe0_netpair,safep_netpair,...}) =
  appSWrappers cs (FIRST' [
        eq_assume_contr_tac,
        bimatch_from_nets_tac safe0_netpair,
        FIRST' hyp_subst_tacs,
        n_bimatch_from_nets_tac 1 safep_netpair,
        bimatch2_tac safep_netpair]);

fun clarify_tac cs = SELECT_GOAL (REPEAT_DETERM (clarify_step_tac cs 1));


(*** Unsafe steps instantiate variables or lose information ***)

(*Backtracking is allowed among the various these unsafe ways of
  proving a subgoal.  *)
fun inst0_step_tac (CS {safe0_netpair, ...}) =
  assume_tac APPEND'
  contr_tac APPEND'
  biresolve_from_nets_tac safe0_netpair;

(*These unsafe steps could generate more subgoals.*)
fun instp_step_tac (CS {safep_netpair, ...}) =
  biresolve_from_nets_tac safep_netpair;

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac cs = inst0_step_tac cs APPEND' instp_step_tac cs;

fun haz_step_tac (CS{haz_netpair,...}) =
  biresolve_from_nets_tac haz_netpair;

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac cs i = safe_tac cs ORELSE appWrappers cs
        (inst_step_tac cs ORELSE' haz_step_tac cs) i;

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac cs i = safe_tac cs ORELSE appWrappers cs
        (inst_step_tac cs APPEND' haz_step_tac cs) i;

(**** The following tactics all fail unless they solve one goal ****)

(*Dumb but fast*)
fun fast_tac cs =
  ObjectLogic.atomize_prems_tac THEN' SELECT_GOAL (DEPTH_SOLVE (step_tac cs 1));

(*Slower but smarter than fast_tac*)
fun best_tac cs =
  ObjectLogic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (step_tac cs 1));

(*even a bit smarter than best_tac*)
fun first_best_tac cs =
  ObjectLogic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (FIRSTGOAL (step_tac cs)));

fun slow_tac cs =
  ObjectLogic.atomize_prems_tac THEN'
  SELECT_GOAL (DEPTH_SOLVE (slow_step_tac cs 1));

fun slow_best_tac cs =
  ObjectLogic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (slow_step_tac cs 1));


(***ASTAR with weight weight_ASTAR, by Norbert Voelker*)
val weight_ASTAR = Unsynchronized.ref 5;

fun astar_tac cs =
  ObjectLogic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + !weight_ASTAR * lev)
      (step_tac cs 1));

fun slow_astar_tac cs =
  ObjectLogic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + !weight_ASTAR * lev)
      (slow_step_tac cs 1));

(**** Complete tactic, loosely based upon LeanTaP.  This tactic is the outcome
  of much experimentation!  Changing APPEND to ORELSE below would prove
  easy theorems faster, but loses completeness -- and many of the harder
  theorems such as 43. ****)

(*Non-deterministic!  Could always expand the first unsafe connective.
  That's hard to implement and did not perform better in experiments, due to
  greater search depth required.*)
fun dup_step_tac (CS {dup_netpair, ...}) =
  biresolve_from_nets_tac dup_netpair;

(*Searching to depth m. A variant called nodup_depth_tac appears in clasimp.ML*)
local
fun slow_step_tac' cs = appWrappers cs
        (instp_step_tac cs APPEND' dup_step_tac cs);
in fun depth_tac cs m i state = SELECT_GOAL
   (safe_steps_tac cs 1 THEN_ELSE
        (DEPTH_SOLVE (depth_tac cs m 1),
         inst0_step_tac cs 1 APPEND COND (K (m=0)) no_tac
                (slow_step_tac' cs 1 THEN DEPTH_SOLVE (depth_tac cs (m-1) 1))
        )) i state;
end;

(*Search, with depth bound m.
  This is the "entry point", which does safe inferences first.*)
fun safe_depth_tac cs m =
  SUBGOAL
    (fn (prem,i) =>
      let val deti =
          (*No Vars in the goal?  No need to backtrack between goals.*)
          if exists_subterm (fn Var _ => true | _ => false) prem then DETERM else I
      in  SELECT_GOAL (TRY (safe_tac cs) THEN
                       DEPTH_SOLVE (deti (depth_tac cs m 1))) i
      end);

fun deepen_tac cs = DEEPEN (2,10) (safe_depth_tac cs);



(** context dependent claset components **)

datatype context_cs = ContextCS of
 {swrappers: (string * (Proof.context -> wrapper)) list,
  uwrappers: (string * (Proof.context -> wrapper)) list};

fun context_cs ctxt cs (ContextCS {swrappers, uwrappers}) =
  let
    fun add_wrapper add (name, f) claset = add (claset, (name, f ctxt));
  in
    cs
    |> fold_rev (add_wrapper (op addSWrapper)) swrappers
    |> fold_rev (add_wrapper (op addWrapper)) uwrappers
  end;

fun make_context_cs (swrappers, uwrappers) =
  ContextCS {swrappers = swrappers, uwrappers = uwrappers};

val empty_context_cs = make_context_cs ([], []);

fun merge_context_cs (ctxt_cs1, ctxt_cs2) =
  if pointer_eq (ctxt_cs1, ctxt_cs2) then ctxt_cs1
  else
    let
      val ContextCS {swrappers = swrappers1, uwrappers = uwrappers1} = ctxt_cs1;
      val ContextCS {swrappers = swrappers2, uwrappers = uwrappers2} = ctxt_cs2;
      val swrappers' = AList.merge (op =) (K true) (swrappers1, swrappers2);
      val uwrappers' = AList.merge (op =) (K true) (uwrappers1, uwrappers2);
    in make_context_cs (swrappers', uwrappers') end;



(** claset data **)

(* global clasets *)

structure GlobalClaset = TheoryDataFun
(
  type T = claset * context_cs;
  val empty = (empty_cs, empty_context_cs);
  val copy = I;
  val extend = I;
  fun merge _ ((cs1, ctxt_cs1), (cs2, ctxt_cs2)) =
    (merge_cs (cs1, cs2), merge_context_cs (ctxt_cs1, ctxt_cs2));
);

val get_global_claset = #1 o GlobalClaset.get;
val map_global_claset = GlobalClaset.map o apfst;

val get_context_cs = #2 o GlobalClaset.get o ProofContext.theory_of;
fun map_context_cs f = GlobalClaset.map (apsnd
  (fn ContextCS {swrappers, uwrappers} => make_context_cs (f (swrappers, uwrappers))));

fun global_claset_of thy =
  let val (cs, ctxt_cs) = GlobalClaset.get thy
  in context_cs (ProofContext.init thy) cs (ctxt_cs) end;


(* context dependent components *)

fun add_context_safe_wrapper wrapper = map_context_cs (apfst ((AList.update (op =) wrapper)));
fun del_context_safe_wrapper name = map_context_cs (apfst ((AList.delete (op =) name)));

fun add_context_unsafe_wrapper wrapper = map_context_cs (apsnd ((AList.update (op =) wrapper)));
fun del_context_unsafe_wrapper name = map_context_cs (apsnd ((AList.delete (op =) name)));


(* local clasets *)

structure LocalClaset = ProofDataFun
(
  type T = claset;
  val init = get_global_claset;
);

val get_claset = LocalClaset.get;
val put_claset = LocalClaset.put;

fun claset_of ctxt =
  context_cs ctxt (LocalClaset.get ctxt) (get_context_cs ctxt);


(* generic clasets *)

val get_cs = Context.cases global_claset_of claset_of;
fun map_cs f = Context.mapping (map_global_claset f) (LocalClaset.map f);


(* attributes *)

fun attrib f = Thm.declaration_attribute (fn th =>
  Context.mapping (map_global_claset (f th)) (LocalClaset.map (f th)));

fun safe_dest w = attrib (addSE w o make_elim);
val safe_elim = attrib o addSE;
val safe_intro = attrib o addSI;
fun haz_dest w = attrib (addE w o make_elim);
val haz_elim = attrib o addE;
val haz_intro = attrib o addI;
val rule_del = attrib delrule o ContextRules.rule_del;


end;



(** concrete syntax of attributes **)

val introN = "intro";
val elimN = "elim";
val destN = "dest";

val setup_attrs =
  Attrib.setup @{binding swapped} (Scan.succeed swapped)
    "classical swap of introduction rule" #>
  Attrib.setup @{binding dest} (ContextRules.add safe_dest haz_dest ContextRules.dest_query)
    "declaration of Classical destruction rule" #>
  Attrib.setup @{binding elim} (ContextRules.add safe_elim haz_elim ContextRules.elim_query)
    "declaration of Classical elimination rule" #>
  Attrib.setup @{binding intro} (ContextRules.add safe_intro haz_intro ContextRules.intro_query)
    "declaration of Classical introduction rule" #>
  Attrib.setup @{binding rule} (Scan.lift Args.del >> K rule_del)
    "remove declaration of intro/elim/dest rule";



(** proof methods **)

local

fun some_rule_tac ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = ContextRules.find_rules false facts goal ctxt;
    val CS {xtra_netpair, ...} = claset_of ctxt;
    val rules3 = ContextRules.find_rules_netpair true facts goal xtra_netpair;
    val rules = rules1 @ rules2 @ rules3 @ rules4;
    val ruleq = Drule.multi_resolves facts rules;
  in
    Method.trace ctxt rules;
    fn st => Seq.flat (Seq.map (fn rule => Tactic.rtac rule i st) ruleq)
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

fun cla_meth tac prems ctxt = METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN tac (claset_of ctxt));

fun cla_meth' tac prems ctxt = METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN' tac (claset_of ctxt)));

fun cla_method tac = Args.bang_facts --| Method.sections cla_modifiers >> (cla_meth tac);
fun cla_method' tac = Args.bang_facts --| Method.sections cla_modifiers >> (cla_meth' tac);



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
  Method.setup @{binding deepen} (cla_method' (fn cs => deepen_tac cs 4))
    "classical prover (iterative deepening)" #>
  Method.setup @{binding safe} (cla_method (CHANGED_PROP o safe_tac))
    "classical prover (apply safe rules)";



(** theory setup **)

val setup = setup_attrs #> setup_methods;



(** outer syntax **)

val _ =
  OuterSyntax.improper_command "print_claset" "print context of Classical Reasoner"
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_cs o claset_of o Toplevel.context_of)));

end;
