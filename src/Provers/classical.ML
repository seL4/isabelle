(*  Title:      Provers/classical.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

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
  val mp        : thm           (* [| P-->Q;  P |] ==> Q *)
  val not_elim  : thm           (* [| ~P;  P |] ==> R *)
  val classical : thm           (* (~P ==> P) ==> P *)
  val sizef     : thm -> int    (* size function for BEST_FIRST *)
  val hyp_subst_tacs: (int -> tactic) list
end;

signature BASIC_CLASSICAL =
sig
  type claset
  val empty_cs: claset
  val print_cs: claset -> unit
  val print_claset: theory -> unit
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

  val change_claset_of: theory -> (claset -> claset) -> unit
  val change_claset: (claset -> claset) -> unit
  val claset_of: theory -> claset
  val claset: unit -> claset
  val CLASET: (claset -> tactic) -> tactic
  val CLASET': (claset -> 'a -> tactic) -> 'a -> tactic
  val local_claset_of   : Proof.context -> claset

  val fast_tac          : claset -> int -> tactic
  val slow_tac          : claset -> int -> tactic
  val weight_ASTAR      : int ref
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

  val AddDs             : thm list -> unit
  val AddEs             : thm list -> unit
  val AddIs             : thm list -> unit
  val AddSDs            : thm list -> unit
  val AddSEs            : thm list -> unit
  val AddSIs            : thm list -> unit
  val Delrules          : thm list -> unit
  val Safe_tac          : tactic
  val Safe_step_tac     : int -> tactic
  val Clarify_tac       : int -> tactic
  val Clarify_step_tac  : int -> tactic
  val Step_tac          : int -> tactic
  val Fast_tac          : int -> tactic
  val Best_tac          : int -> tactic
  val Slow_tac          : int -> tactic
  val Slow_best_tac     : int -> tactic
  val Deepen_tac        : int -> int -> tactic
end;

signature CLASSICAL =
sig
  include BASIC_CLASSICAL
  val swap: thm  (* ~P ==> (~Q ==> P) ==> Q *)
  val classical_rule: thm -> thm
  val add_context_safe_wrapper: string * (Proof.context -> wrapper) -> theory -> theory
  val del_context_safe_wrapper: string -> theory -> theory
  val add_context_unsafe_wrapper: string * (Proof.context -> wrapper) -> theory -> theory
  val del_context_unsafe_wrapper: string -> theory -> theory
  val get_claset: theory -> claset
  val print_local_claset: Proof.context -> unit
  val get_local_claset: Proof.context -> claset
  val put_local_claset: claset -> Proof.context -> Proof.context
  val safe_dest: int option -> Context.generic attribute
  val safe_elim: int option -> Context.generic attribute
  val safe_intro: int option -> Context.generic attribute
  val haz_dest: int option -> Context.generic attribute
  val haz_elim: int option -> Context.generic attribute
  val haz_intro: int option -> Context.generic attribute
  val rule_del: Context.generic attribute
  val cla_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val cla_meth: (claset -> tactic) -> thm list -> Proof.context -> Proof.method
  val cla_meth': (claset -> int -> tactic) -> thm list -> Proof.context -> Proof.method
  val cla_method: (claset -> tactic) -> Method.src -> Proof.context -> Proof.method
  val cla_method': (claset -> int -> tactic) -> Method.src -> Proof.context -> Proof.method
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

Such rules can cause Fast_tac to fail and Blast_tac to report "PROOF
FAILED"; classical_rule will strenthen this to

    [| inj f; ~ W ==> f x = f y; x = y ==> W |] ==> W
*)

local

fun equal_concl concl prop =
  concl aconv Logic.strip_assums_concl prop;

fun is_elim rule =
  let
    val thy = Thm.theory_of_thm rule;
    val concl = Thm.concl_of rule;
  in
    Term.is_Var (ObjectLogic.drop_judgment thy concl) andalso
    exists (equal_concl concl) (Thm.prems_of rule)
  end;

in

fun classical_rule rule =
  if is_elim rule then
    let
      val rule' = rule RS classical;
      val concl' = Thm.concl_of rule';
      fun redundant_hyp goal =
         equal_concl concl' goal orelse
          (case Logic.strip_assums_hyp goal of
            hyp :: hyps => exists (fn t => t aconv hyp) hyps
          | _ => false);
      val rule'' =
        rule' |> ALLGOALS (SUBGOAL (fn (goal, i) =>
          if i = 1 orelse redundant_hyp goal
          then Tactic.etac thin_rl i
          else all_tac))
        |> Seq.hd
        |> Drule.zero_var_indexes
        |> Thm.put_name_tags (Thm.get_name_tags rule);
    in if Drule.weak_eq_thm (rule, rule'') then rule else rule'' end
  else rule;

end;


(*** Useful tactics for classical reasoning ***)

val imp_elim = (*cannot use bind_thm within a structure!*)
  store_thm ("imp_elim", Thm.transfer (the_context ()) (classical_rule (Tactic.make_elim mp)));

(*Prove goal that assumes both P and ~P.
  No backtracking if it finds an equal assumption.  Perhaps should call
  ematch_tac instead of eresolve_tac, but then cannot prove ZF/cantor.*)
val contr_tac = eresolve_tac [not_elim]  THEN'
                (eq_assume_tac ORELSE' assume_tac);

(*Finds P-->Q and P in the assumptions, replaces implication by Q.
  Could do the same thing for P<->Q and P... *)
fun mp_tac i = eresolve_tac [not_elim, imp_elim] i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = ematch_tac [not_elim, imp_elim] i  THEN  eq_assume_tac i;

val swap =
  store_thm ("swap", Thm.transfer (the_context ())
    (rule_by_tactic (etac thin_rl 1) (not_elim RS classical)));

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [swap]);
fun swapped x = Attrib.no_args (fn (x, th) => (x, th RSN (2, swap))) x;

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac rls =
    let fun addrl (rl,brls) = (false, rl) :: (true, rl RSN (2,swap)) :: brls
    in  assume_tac      ORELSE'
        contr_tac       ORELSE'
        biresolve_tac (foldr addrl [] rls)
    end;

(*Duplication of hazardous rules, for complete provers*)
fun dup_intr th = zero_var_indexes (th RS classical);

fun dup_elim th =
    rule_by_tactic (TRYALL (etac revcut_rl))
      ((th RSN (2, revcut_rl)) |> assumption 2 |> Seq.hd);

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
  let val pretty_thms = map Display.pretty_thm in
    [Pretty.big_list "safe introduction rules (intro!):" (pretty_thms safeIs),
      Pretty.big_list "introduction rules (intro):" (pretty_thms hazIs),
      Pretty.big_list "safe elimination rules (elim!):" (pretty_thms safeEs),
      Pretty.big_list "elimination rules (elim):" (pretty_thms hazEs),
      Pretty.strs ("safe wrappers:" :: map #1 swrappers),
      Pretty.strs ("unsafe wrappers:" :: map #1 uwrappers)]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun rep_cs (CS args) = args;

local
  fun wrap l tac = foldr (fn ((name,tacf),w) => tacf w) tac l;
in
  fun appSWrappers (CS{swrappers,...}) = wrap swrappers;
  fun appWrappers  (CS{uwrappers,...}) = wrap uwrappers;
end;


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

fun insert_tagged_list kbrls netpr = foldr Tactic.insert_tagged_brl netpr kbrls;

(*Insert into netpair that already has nI intr rules and nE elim rules.
  Count the intr rules double (to account for swapify).  Negate to give the
  new insertions the lowest priority.*)
fun insert (nI, nE) = insert_tagged_list o (tag_brls (~(2*nI+nE))) o joinrules;
fun insert' w (nI, nE) = insert_tagged_list o tag_brls' w (~(nI + nE)) o joinrules';

fun delete_tagged_list brls netpr = foldr Tactic.delete_tagged_brl netpr brls;
fun delete x = delete_tagged_list (joinrules x);
fun delete' x = delete_tagged_list (joinrules' x);

val mem_thm = member Drule.eq_thm_prop
and rem_thm = remove Drule.eq_thm_prop;

(*Warn if the rule is already present ELSEWHERE in the claset.  The addition
  is still allowed.*)
fun warn_dup th (CS{safeIs, safeEs, hazIs, hazEs, ...}) =
       if mem_thm safeIs th then
         warning ("Rule already declared as safe introduction (intro!)\n" ^ string_of_thm th)
  else if mem_thm safeEs th then
         warning ("Rule already declared as safe elimination (elim!)\n" ^ string_of_thm th)
  else if mem_thm hazIs th then
         warning ("Rule already declared as introduction (intro)\n" ^ string_of_thm th)
  else if mem_thm hazEs th then
         warning ("Rule already declared as elimination (elim)\n" ^ string_of_thm th)
  else ();


(*** Safe rules ***)

fun addSI w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
             safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm safeIs th then
         (warning ("Ignoring duplicate safe introduction (intro!)\n" ^ string_of_thm th);
          cs)
  else
  let val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
          List.partition Thm.no_prems [th]
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
         (warning ("Ignoring duplicate safe elimination (elim!)\n" ^ string_of_thm th);
          cs)
  else if has_fewer_prems 1 th then
    	error("Ill-formed elimination rule\n" ^ string_of_thm th)
  else
  let
      val th' = classical_rule th
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

(*Give new theorem a name, if it has one already.*)
fun name_make_elim th =
    if has_fewer_prems 1 th then
    	error("Ill-formed destruction rule\n" ^ string_of_thm th)
    else
    case Thm.name_of_thm th of
        "" => Tactic.make_elim th
      | a  => Thm.name_thm (a ^ "_dest", Tactic.make_elim th);

fun cs addSDs ths = cs addSEs (map name_make_elim ths);


(*** Hazardous (unsafe) rules ***)

fun addI w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
             safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm hazIs th then
         (warning ("Ignoring duplicate introduction (intro)\n" ^ string_of_thm th);
          cs)
  else
  let val nI = length hazIs + 1
      and nE = length hazEs
  in warn_dup th cs;
     CS{hazIs   = th::hazIs,
        haz_netpair = insert (nI,nE) ([th], []) haz_netpair,
        dup_netpair = insert (nI,nE) (map dup_intr [th], []) dup_netpair,
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
         error ("Ill-formed introduction rule\n" ^ string_of_thm th);

fun addE w th
  (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
            safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if mem_thm hazEs th then
         (warning ("Ignoring duplicate elimination (elim)\n" ^ string_of_thm th);
          cs)
  else if has_fewer_prems 1 th then
    	error("Ill-formed elimination rule\n" ^ string_of_thm th)
  else
  let
      val th' = classical_rule th
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

fun cs addDs ths = cs addEs (map name_make_elim ths);


(*** Deletion of rules
     Working out what to delete, requires repeating much of the code used
        to insert.
***)

fun delSI th
          (cs as CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
                    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm safeIs th then
   let val (safe0_rls, safep_rls) = List.partition Thm.no_prems [th]
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
      val th' = classical_rule th
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
     CS{haz_netpair = delete ([th], []) haz_netpair,
        dup_netpair = delete ([dup_intr th], []) dup_netpair,
        safeIs  = safeIs,
        safeEs  = safeEs,
        hazIs   = rem_thm th hazIs,
        hazEs   = hazEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([th], []) xtra_netpair}
 else cs
 handle THM("RSN: no unifiers",_,_) => (*from dup_intr*)
        error ("Ill-formed introduction rule\n" ^ string_of_thm th);


fun delE th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  let val th' = classical_rule th in
    if mem_thm hazEs th then
     CS{haz_netpair = delete ([], [th']) haz_netpair,
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
     else cs
   end;


(*Delete ALL occurrences of "th" in the claset (perhaps from several lists)*)
fun delrule th (cs as CS {safeIs, safeEs, hazIs, hazEs, ...}) =
  let val th' = Tactic.make_elim th in
    if mem_thm safeIs th orelse mem_thm safeEs th orelse
      mem_thm hazIs th orelse mem_thm hazEs th orelse
      mem_thm safeEs th' orelse mem_thm hazEs th'
    then delSI th (delSE th (delI th (delE th (delSE th' (delE th' cs)))))
    else (warning ("Undeclared classical rule\n" ^ string_of_thm th); cs)
  end;

fun cs delrules ths = fold delrule ths cs;


(*** Modifying the wrapper tacticals ***)
fun update_swrappers
(CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) f =
 CS{safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};

fun update_uwrappers
(CS{safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) f =
 CS{safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = swrappers, uwrappers = f uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};


(*Add/replace a safe wrapper*)
fun cs addSWrapper new_swrapper = update_swrappers cs (fn swrappers =>
    overwrite_warn (swrappers, new_swrapper)
       ("Overwriting safe wrapper " ^ fst new_swrapper));

(*Add/replace an unsafe wrapper*)
fun cs addWrapper new_uwrapper = update_uwrappers cs (fn uwrappers =>
    overwrite_warn (uwrappers, new_uwrapper)
        ("Overwriting unsafe wrapper "^fst new_uwrapper));

(*Remove a safe wrapper*)
fun cs delSWrapper name = update_swrappers cs (fn swrappers =>
  let val swrappers' = filter_out (equal name o fst) swrappers in
    if length swrappers <> length swrappers' then swrappers'
    else (warning ("No such safe wrapper in claset: "^ name); swrappers)
  end);

(*Remove an unsafe wrapper*)
fun cs delWrapper name = update_uwrappers cs (fn uwrappers =>
  let val uwrappers' = filter_out (equal name o fst) uwrappers in
    if length uwrappers <> length uwrappers' then uwrappers'
    else (warning ("No such unsafe wrapper in claset: " ^ name); uwrappers)
  end);

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
fun merge_cs (cs as CS{safeIs, safeEs, hazIs, hazEs, ...},
     CS{safeIs=safeIs2, safeEs=safeEs2, hazIs=hazIs2, hazEs=hazEs2, swrappers, uwrappers, ...}) =
  let val safeIs' = gen_rems Drule.eq_thm_prop (safeIs2,safeIs)
      val safeEs' = gen_rems Drule.eq_thm_prop (safeEs2,safeEs)
      val hazIs' = gen_rems Drule.eq_thm_prop (hazIs2, hazIs)
      val hazEs' = gen_rems Drule.eq_thm_prop (hazEs2, hazEs)
      val cs1   = cs addSIs safeIs'
                     addSEs safeEs'
                     addIs  hazIs'
                     addEs  hazEs'
      val cs2 = update_swrappers cs1 (fn ws => merge_alists ws swrappers);
      val cs3 = update_uwrappers cs2 (fn ws => merge_alists ws uwrappers);
  in cs3
  end;


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
    biresolution_from_nets_tac (Tactic.orderlist o List.filter (nsubgoalsP n)) true;

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
fun inst0_step_tac (CS{safe0_netpair,safep_netpair,...}) =
  assume_tac                      APPEND'
  contr_tac                       APPEND'
  biresolve_from_nets_tac safe0_netpair;

(*These unsafe steps could generate more subgoals.*)
fun instp_step_tac (CS{safep_netpair,...}) =
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
  ObjectLogic.atomize_tac THEN' SELECT_GOAL (DEPTH_SOLVE (step_tac cs 1));

(*Slower but smarter than fast_tac*)
fun best_tac cs =
  ObjectLogic.atomize_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (step_tac cs 1));

(*even a bit smarter than best_tac*)
fun first_best_tac cs =
  ObjectLogic.atomize_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (FIRSTGOAL (step_tac cs)));

fun slow_tac cs =
  ObjectLogic.atomize_tac THEN'
  SELECT_GOAL (DEPTH_SOLVE (slow_step_tac cs 1));

fun slow_best_tac cs =
  ObjectLogic.atomize_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (slow_step_tac cs 1));


(***ASTAR with weight weight_ASTAR, by Norbert Voelker*)
val weight_ASTAR = ref 5;

fun astar_tac cs =
  ObjectLogic.atomize_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + !weight_ASTAR * lev)
      (step_tac cs 1));

fun slow_astar_tac cs =
  ObjectLogic.atomize_tac THEN'
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
fun dup_step_tac (cs as (CS{dup_netpair,...})) =
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
          case term_vars prem of
              []        => DETERM
            | _::_      => I
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
    cs |> fold_rev (add_wrapper (op addSWrapper)) swrappers
    |> fold_rev (add_wrapper (op addWrapper)) uwrappers
  end;

fun make_context_cs (swrappers, uwrappers) =
  ContextCS {swrappers = swrappers, uwrappers = uwrappers};

val empty_context_cs = make_context_cs ([], []);

fun merge_context_cs (ctxt_cs1, ctxt_cs2) =
  let
    val ContextCS {swrappers = swrappers1, uwrappers = uwrappers1} = ctxt_cs1;
    val ContextCS {swrappers = swrappers2, uwrappers = uwrappers2} = ctxt_cs2;

    val swrappers' = merge_alists swrappers1 swrappers2;
    val uwrappers' = merge_alists uwrappers1 uwrappers2;
  in make_context_cs (swrappers', uwrappers') end;



(** claset data **)

(* global claset *)

structure GlobalClaset = TheoryDataFun
(struct
  val name = "Provers/claset";
  type T = claset ref * context_cs;

  val empty = (ref empty_cs, empty_context_cs);
  fun copy (ref cs, ctxt_cs) = (ref cs, ctxt_cs): T;
  val extend = copy;
  fun merge _ ((ref cs1, ctxt_cs1), (ref cs2, ctxt_cs2)) =
    (ref (merge_cs (cs1, cs2)), merge_context_cs (ctxt_cs1, ctxt_cs2));
  fun print _ (ref cs, _) = print_cs cs;
end);

val print_claset = GlobalClaset.print;
val get_claset = ! o #1 o GlobalClaset.get;

val get_context_cs = #2 o GlobalClaset.get o ProofContext.theory_of;
fun map_context_cs f = GlobalClaset.map (apsnd
  (fn ContextCS {swrappers, uwrappers} => make_context_cs (f (swrappers, uwrappers))));

val change_claset_of = change o #1 o GlobalClaset.get;
fun change_claset f = change_claset_of (Context.the_context ()) f;

fun claset_of thy =
  let val (cs_ref, ctxt_cs) = GlobalClaset.get thy
  in context_cs (Context.init_proof thy) (! cs_ref) (ctxt_cs) end;
val claset = claset_of o Context.the_context;

fun CLASET tacf st = tacf (claset_of (Thm.theory_of_thm st)) st;
fun CLASET' tacf i st = tacf (claset_of (Thm.theory_of_thm st)) i st;

fun AddDs args = change_claset (fn cs => cs addDs args);
fun AddEs args = change_claset (fn cs => cs addEs args);
fun AddIs args = change_claset (fn cs => cs addIs args);
fun AddSDs args = change_claset (fn cs => cs addSDs args);
fun AddSEs args = change_claset (fn cs => cs addSEs args);
fun AddSIs args = change_claset (fn cs => cs addSIs args);
fun Delrules args = change_claset (fn cs => cs delrules args);


(* context dependent components *)

fun add_context_safe_wrapper wrapper = map_context_cs (apfst (merge_alists [wrapper]));
fun del_context_safe_wrapper name = map_context_cs (apfst (filter_out (equal name o #1)));

fun add_context_unsafe_wrapper wrapper = map_context_cs (apsnd (merge_alists [wrapper]));
fun del_context_unsafe_wrapper name = map_context_cs (apsnd (filter_out (equal name o #1)));


(* local claset *)

structure LocalClaset = ProofDataFun
(struct
  val name = "Provers/claset";
  type T = claset;
  val init = get_claset;
  fun print ctxt cs = print_cs (context_cs ctxt cs (get_context_cs ctxt));
end);

val print_local_claset = LocalClaset.print;
val get_local_claset = LocalClaset.get;
val put_local_claset = LocalClaset.put;

fun local_claset_of ctxt =
  context_cs ctxt (get_local_claset ctxt) (get_context_cs ctxt);


(* attributes *)

fun attrib f = Attrib.declaration (fn th =>
   fn Context.Theory thy => (change_claset_of thy (f th); Context.Theory thy)
    | Context.Proof ctxt => Context.Proof (LocalClaset.map (f th) ctxt));

fun safe_dest w = attrib (addSE w o name_make_elim);
val safe_elim = attrib o addSE;
val safe_intro = attrib o addSI;
fun haz_dest w = attrib (addE w o name_make_elim);
val haz_elim = attrib o addE;
val haz_intro = attrib o addI;
val rule_del = attrib delrule o ContextRules.rule_del;


(* tactics referring to the implicit claset *)

(*the abstraction over the proof state delays the dereferencing*)
fun Safe_tac st           = safe_tac (claset()) st;
fun Safe_step_tac i st    = safe_step_tac (claset()) i st;
fun Clarify_step_tac i st = clarify_step_tac (claset()) i st;
fun Clarify_tac i st      = clarify_tac (claset()) i st;
fun Step_tac i st         = step_tac (claset()) i st;
fun Fast_tac i st         = fast_tac (claset()) i st;
fun Best_tac i st         = best_tac (claset()) i st;
fun Slow_tac i st         = slow_tac (claset()) i st;
fun Slow_best_tac i st    = slow_best_tac (claset()) i st;
fun Deepen_tac m          = deepen_tac (claset()) m;


end;



(** concrete syntax of attributes **)

val introN = "intro";
val elimN = "elim";
val destN = "dest";
val ruleN = "rule";

val setup_attrs = Attrib.add_attributes
 [("swapped", Attrib.common swapped, "classical swap of introduction rule"),
  (destN, Attrib.common (ContextRules.add_args safe_dest haz_dest ContextRules.dest_query),
    "declaration of Classical destruction rule"),
  (elimN, Attrib.common (ContextRules.add_args safe_elim haz_elim ContextRules.elim_query),
    "declaration of Classical elimination rule"),
  (introN, Attrib.common (ContextRules.add_args safe_intro haz_intro ContextRules.intro_query),
    "declaration of Classical introduction rule"),
  (ruleN, Attrib.common (Attrib.syntax (Scan.lift Args.del >> K rule_del)),
    "remove declaration of intro/elim/dest rule")];



(** proof methods **)

fun METHOD_CLASET tac ctxt =
  Method.METHOD (tac ctxt (local_claset_of ctxt));

fun METHOD_CLASET' tac ctxt =
  Method.METHOD (HEADGOAL o tac ctxt (local_claset_of ctxt));


local

fun some_rule_tac ctxt (CS {xtra_netpair, ...}) facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = ContextRules.find_rules false facts goal ctxt;
    val rules3 = ContextRules.find_rules_netpair true facts goal xtra_netpair;
    val rules = rules1 @ rules2 @ rules3 @ rules4;
    val ruleq = Drule.multi_resolves facts rules;
  in
    Method.trace ctxt rules;
    fn st => Seq.flat (Seq.map (fn rule => Tactic.rtac rule i st) ruleq)
  end);

fun rule_tac [] ctxt cs facts = some_rule_tac ctxt cs facts
  | rule_tac rules _ _ facts = Method.rule_tac rules facts;

fun default_tac rules ctxt cs facts =
  HEADGOAL (rule_tac rules ctxt cs facts) ORELSE
  AxClass.default_intro_classes_tac facts;

in
  val rule = METHOD_CLASET' o rule_tac;
  val default = METHOD_CLASET o default_tac;
end;


(* contradiction method *)

val contradiction = Method.rule [Data.not_elim, Data.not_elim COMP Drule.swap_prems_rl];


(* automatic methods *)

val cla_modifiers =
 [Args.$$$ destN -- Args.bang_colon >> K ((I, Attrib.context (safe_dest NONE)): Method.modifier),
  Args.$$$ destN -- Args.colon >> K (I, Attrib.context (haz_dest NONE)),
  Args.$$$ elimN -- Args.bang_colon >> K (I, Attrib.context (safe_elim NONE)),
  Args.$$$ elimN -- Args.colon >> K (I, Attrib.context (haz_elim NONE)),
  Args.$$$ introN -- Args.bang_colon >> K (I, Attrib.context (safe_intro NONE)),
  Args.$$$ introN -- Args.colon >> K (I, Attrib.context (haz_intro NONE)),
  Args.del -- Args.colon >> K (I, Attrib.context rule_del)];

fun cla_meth tac prems ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN tac (local_claset_of ctxt));

fun cla_meth' tac prems ctxt = Method.METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN' tac (local_claset_of ctxt)));

val cla_method = Method.bang_sectioned_args cla_modifiers o cla_meth;
val cla_method' = Method.bang_sectioned_args cla_modifiers o cla_meth';



(** setup_methods **)

val setup_methods = Method.add_methods
 [("default", Method.thms_ctxt_args default, "apply some intro/elim rule (potentially classical)"),
  ("rule", Method.thms_ctxt_args rule, "apply some intro/elim rule (potentially classical)"),
  ("contradiction", Method.no_args contradiction, "proof by contradiction"),
  ("clarify", cla_method' (CHANGED_PROP oo clarify_tac), "repeatedly apply safe steps"),
  ("fast", cla_method' fast_tac, "classical prover (depth-first)"),
  ("slow", cla_method' slow_tac, "classical prover (slow depth-first)"),
  ("best", cla_method' best_tac, "classical prover (best-first)"),
  ("deepen", cla_method' (fn cs => deepen_tac cs 4), "classical prover (iterative deepening)"),
  ("safe", cla_method (CHANGED_PROP o safe_tac), "classical prover (apply safe rules)")];



(** theory setup **)

val setup = GlobalClaset.init #> LocalClaset.init #> setup_attrs #> setup_methods;



(** outer syntax **)

val print_clasetP =
  OuterSyntax.improper_command "print_claset" "print context of Classical Reasoner"
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o (Toplevel.keep
      (Toplevel.node_case print_claset (print_local_claset o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_clasetP];


end;
