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
infix 4 addSIs addSEs addSDs addIs addEs addDs addXIs addXEs addXDs delrules
  addSWrapper delSWrapper addWrapper delWrapper
  addSbefore addSaltern addbefore addaltern
  addD2 addE2 addSD2 addSE2;


(*should be a type abbreviation in signature CLASSICAL*)
type netpair = (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net;
type wrapper = (int -> tactic) -> (int -> tactic);

signature CLASSICAL_DATA =
sig
  val make_elim : thm -> thm    (* Tactic.make_elim or a classical version*)
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
  val rep_cs: (* BLAST_DATA in blast.ML dependent on this *)
    claset -> {safeIs: thm list, safeEs: thm list,
                 hazIs: thm list, hazEs: thm list,
                 xtraIs: thm list, xtraEs: thm list,
                 swrappers: (string * wrapper) list, 
                 uwrappers: (string * wrapper) list,
                 safe0_netpair: netpair, safep_netpair: netpair,
                 haz_netpair: netpair, dup_netpair: netpair, xtra_netpair: netpair}
  val merge_cs          : claset * claset -> claset
  val addDs             : claset * thm list -> claset
  val addEs             : claset * thm list -> claset
  val addIs             : claset * thm list -> claset
  val addSDs            : claset * thm list -> claset
  val addSEs            : claset * thm list -> claset
  val addSIs            : claset * thm list -> claset
  val addXDs            : claset * thm list -> claset
  val addXEs            : claset * thm list -> claset
  val addXIs            : claset * thm list -> claset
  val delrules          : claset * thm list -> claset
  val addSWrapper       : claset * (string * wrapper) -> claset
  val delSWrapper       : claset *  string            -> claset
  val addWrapper        : claset * (string * wrapper) -> claset
  val delWrapper        : claset *  string            -> claset
  val addSbefore        : claset * (string * (int -> tactic)) -> claset
  val addSaltern        : claset * (string * (int -> tactic)) -> claset
  val addbefore         : claset * (string * (int -> tactic)) -> claset
  val addaltern         : claset * (string * (int -> tactic)) -> claset
  val addD2             : claset * (string * thm) -> claset
  val addE2             : claset * (string * thm) -> claset
  val addSD2            : claset * (string * thm) -> claset
  val addSE2            : claset * (string * thm) -> claset
  val appSWrappers      : claset -> wrapper
  val appWrappers       : claset -> wrapper
  val trace_rules       : bool ref

  val claset_ref_of_sg: Sign.sg -> claset ref
  val claset_ref_of: theory -> claset ref
  val claset_of_sg: Sign.sg -> claset
  val claset_of: theory -> claset
  val CLASET: (claset -> tactic) -> tactic
  val CLASET': (claset -> 'a -> tactic) -> 'a -> tactic
  val claset: unit -> claset
  val claset_ref: unit -> claset ref

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
  val swap              : thm                 (* ~P ==> (~Q ==> P) ==> Q *)
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
  val AddXDs            : thm list -> unit
  val AddXEs            : thm list -> unit
  val AddXIs            : thm list -> unit
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
  val print_local_claset: Proof.context -> unit
  val get_local_claset: Proof.context -> claset
  val put_local_claset: claset -> Proof.context -> Proof.context
  val safe_dest_global: theory attribute
  val safe_elim_global: theory attribute
  val safe_intro_global: theory attribute
  val haz_dest_global: theory attribute
  val haz_elim_global: theory attribute
  val haz_intro_global: theory attribute
  val xtra_dest_global: theory attribute
  val xtra_elim_global: theory attribute
  val xtra_intro_global: theory attribute
  val rule_del_global: theory attribute
  val safe_dest_local: Proof.context attribute
  val safe_elim_local: Proof.context attribute
  val safe_intro_local: Proof.context attribute
  val haz_dest_local: Proof.context attribute
  val haz_elim_local: Proof.context attribute
  val haz_intro_local: Proof.context attribute
  val xtra_dest_local: Proof.context attribute
  val xtra_elim_local: Proof.context attribute
  val xtra_intro_local: Proof.context attribute
  val rule_del_local: Proof.context attribute
  val cla_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val cla_meth: (claset -> tactic) -> thm list -> Proof.context -> Proof.method
  val cla_meth': (claset -> int -> tactic) -> thm list -> Proof.context -> Proof.method
  val cla_method: (claset -> tactic) -> Args.src -> Proof.context -> Proof.method
  val cla_method': (claset -> int -> tactic) -> Args.src -> Proof.context -> Proof.method
  val setup: (theory -> theory) list
end;


functor ClassicalFun(Data: CLASSICAL_DATA): CLASSICAL =
struct

local open Data in

(*** Useful tactics for classical reasoning ***)

val imp_elim = (*cannot use bind_thm within a structure!*)
  store_thm ("imp_elim", Data.make_elim mp);

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
  store_thm ("swap", rule_by_tactic (etac thin_rl 1) (not_elim RS classical));

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [swap]);

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac rls = 
    let fun addrl (rl,brls) = (false, rl) :: (true, rl RSN (2,swap)) :: brls
    in  assume_tac      ORELSE' 
        contr_tac       ORELSE' 
        biresolve_tac (foldr addrl (rls,[]))
    end;

(*Duplication of hazardous rules, for complete provers*)
fun dup_intr th = zero_var_indexes (th RS classical);

fun dup_elim th =
  (case try
      (rule_by_tactic (TRYALL (etac revcut_rl)))
      (th RSN (2, revcut_rl) |> assumption 2 |> Seq.hd) of
    Some th' => th'
  | _ => error ("Bad format for elimination rule\n" ^ string_of_thm th));


(**** Classical rule sets ****)

datatype claset =
  CS of {safeIs         : thm list,             (*safe introduction rules*)
         safeEs         : thm list,             (*safe elimination rules*)
         hazIs          : thm list,             (*unsafe introduction rules*)
         hazEs          : thm list,             (*unsafe elimination rules*)
         xtraIs         : thm list,             (*extra introduction rules*)
         xtraEs         : thm list,             (*extra elimination rules*)
         swrappers      : (string * wrapper) list, (*for transf. safe_step_tac*)
         uwrappers      : (string * wrapper) list, (*for transforming step_tac*)
         safe0_netpair  : netpair,              (*nets for trivial cases*)
         safep_netpair  : netpair,              (*nets for >0 subgoals*)
         haz_netpair    : netpair,              (*nets for unsafe rules*)
         dup_netpair    : netpair,              (*nets for duplication*)
         xtra_netpair   : netpair};             (*nets for extra rules*)

(*Desired invariants are
        safe0_netpair = build safe0_brls,
        safep_netpair = build safep_brls,
        haz_netpair = build (joinrules(hazIs, hazEs)),
        dup_netpair = build (joinrules(map dup_intr hazIs, 
                                       map dup_elim hazEs)),
        xtra_netpair = build (joinrules(xtraIs, xtraEs))}

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
     xtraIs     = [],
     xtraEs     = [],
     swrappers  = [],
     uwrappers  = [],
     safe0_netpair = empty_netpair,
     safep_netpair = empty_netpair,
     haz_netpair   = empty_netpair,
     dup_netpair   = empty_netpair,
     xtra_netpair  = empty_netpair};

fun print_cs (CS {safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, ...}) =
  let val pretty_thms = map Display.pretty_thm in
    [Pretty.big_list "safe introduction rules (intro!):" (pretty_thms safeIs),
      Pretty.big_list "introduction rules (intro):" (pretty_thms hazIs),
      Pretty.big_list "extra introduction rules (intro?):" (pretty_thms xtraIs),
      Pretty.big_list "safe elimination rules (elim!):" (pretty_thms safeEs),
      Pretty.big_list "elimination rules (elim):" (pretty_thms hazEs),
      Pretty.big_list "extra elimination rules (elim?):" (pretty_thms xtraEs)]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun rep_cs (CS args) = args;

local 
  fun calc_wrap l tac = foldr (fn ((name,tacf),w) => tacf w) (l, tac);
in 
  fun appSWrappers (CS{swrappers,...}) = calc_wrap swrappers;
  fun appWrappers  (CS{uwrappers,...}) = calc_wrap uwrappers;
end;


(*** Adding (un)safe introduction or elimination rules.

    In case of overlap, new rules are tried BEFORE old ones!!
***)

(*For use with biresolve_tac.  Combines intr rules with swap to handle negated
  assumptions.  Pairs elim rules with true. *)
fun joinrules (intrs,elims) =  
    (map (pair true) (elims @ swapify intrs)  @
     map (pair false) intrs);

(*Priority: prefer rules with fewest subgoals, 
  then rules added most recently (preferring the head of the list).*)
fun tag_brls k [] = []
  | tag_brls k (brl::brls) =
      (1000000*subgoals_of_brl brl + k, brl) :: 
      tag_brls (k+1) brls;

fun insert_tagged_list kbrls netpr = foldr insert_tagged_brl (kbrls, netpr);

(*Insert into netpair that already has nI intr rules and nE elim rules.
  Count the intr rules double (to account for swapify).  Negate to give the
  new insertions the lowest priority.*)
fun insert (nI,nE) = insert_tagged_list o (tag_brls (~(2*nI+nE))) o joinrules;

fun delete_tagged_list brls netpr = foldr delete_tagged_brl (brls, netpr);

val delete = delete_tagged_list o joinrules;

val mem_thm = gen_mem eq_thm
and rem_thm = gen_rem eq_thm;

(*Warn if the rule is already present ELSEWHERE in the claset.  The addition
  is still allowed.*)
fun warn_dup th (CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, ...}) = 
       if mem_thm (th, safeIs) then 
         warning ("Rule already declared as safe introduction (intro!)\n" ^ string_of_thm th)
  else if mem_thm (th, safeEs) then
         warning ("Rule already declared as safe elimination (elim!)\n" ^ string_of_thm th)
  else if mem_thm (th, hazIs) then 
         warning ("Rule already declared as introduction (intro)\n" ^ string_of_thm th)
  else if mem_thm (th, hazEs) then 
         warning ("Rule already declared as elimination (elim)\n" ^ string_of_thm th)
  else if mem_thm (th, xtraIs) then 
         warning ("Rule already declared as extra introduction (intro?)\n" ^ string_of_thm th)
  else if mem_thm (th, xtraEs) then 
         warning ("Rule already declared as extra elimination (elim?)\n" ^ string_of_thm th)
  else ();

(*** Safe rules ***)

fun addSI (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
              safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair},
           th)  =
  if mem_thm (th, safeIs) then 
         (warning ("Ignoring duplicate safe introduction (intro!)\n" ^ string_of_thm th);
          cs)
  else
  let val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
          partition Thm.no_prems [th]
      val nI = length safeIs + 1
      and nE = length safeEs
  in warn_dup th cs;
     CS{safeIs  = th::safeIs,
        safe0_netpair = insert (nI,nE) (safe0_rls, []) safe0_netpair,
        safep_netpair = insert (nI,nE) (safep_rls, []) safep_netpair,
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        xtraIs  = xtraIs,
        xtraEs  = xtraEs,
        swrappers    = swrappers,
        uwrappers    = uwrappers,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair,
        xtra_netpair = xtra_netpair}
  end;

fun addSE (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair},
           th)  =
  if mem_thm (th, safeEs) then 
         (warning ("Ignoring duplicate safe elimination (elim!)\n" ^ string_of_thm th);
          cs)
  else
  let val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
          partition (fn rl => nprems_of rl=1) [th]
      val nI = length safeIs
      and nE = length safeEs + 1
  in warn_dup th cs;
     CS{safeEs  = th::safeEs,
        safe0_netpair = insert (nI,nE) ([], safe0_rls) safe0_netpair,
        safep_netpair = insert (nI,nE) ([], safep_rls) safep_netpair,
        safeIs  = safeIs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        xtraIs  = xtraIs,
        xtraEs  = xtraEs,
        swrappers    = swrappers,
        uwrappers    = uwrappers,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair,
        xtra_netpair = xtra_netpair}
  end;

fun rev_foldl f (e, l) = foldl f (e, rev l);

val op addSIs = rev_foldl addSI;
val op addSEs = rev_foldl addSE;

fun cs addSDs ths = cs addSEs (map Data.make_elim ths);


(*** Hazardous (unsafe) rules ***)

fun addI (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair},
          th)=
  if mem_thm (th, hazIs) then 
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
        xtraIs  = xtraIs,
        xtraEs  = xtraEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = xtra_netpair}
  end;

fun addE (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair},
          th) =
  if mem_thm (th, hazEs) then 
         (warning ("Ignoring duplicate elimination (elim)\n" ^ string_of_thm th);
          cs)
  else
  let val nI = length hazIs 
      and nE = length hazEs + 1
  in warn_dup th cs;
     CS{hazEs   = th::hazEs,
        haz_netpair = insert (nI,nE) ([], [th]) haz_netpair,
        dup_netpair = insert (nI,nE) ([], map dup_elim [th]) dup_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = hazIs,
        xtraIs  = xtraIs,
        xtraEs  = xtraEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = xtra_netpair}
  end;

val op addIs = rev_foldl addI;
val op addEs = rev_foldl addE;

fun cs addDs ths = cs addEs (map Data.make_elim ths);


(*** Extra (single step) rules ***)

fun addXI (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers,
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair},
          th)=
  if mem_thm (th, xtraIs) then 
         (warning ("Ignoring duplicate extra introduction (intro?)\n" ^ string_of_thm th);
          cs)
  else
  let val nI = length xtraIs + 1
      and nE = length xtraEs
  in warn_dup th cs;
     CS{xtraIs  = th::xtraIs,
        xtra_netpair = insert (nI,nE) ([th], []) xtra_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        xtraEs  = xtraEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair}
  end;

fun addXE (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair},
          th) =
  if mem_thm (th, xtraEs) then
         (warning ("Ignoring duplicate extra elimination (elim?)\n" ^ string_of_thm th);
          cs)
  else
  let val nI = length xtraIs 
      and nE = length xtraEs + 1
  in warn_dup th cs;
     CS{xtraEs  = th::xtraEs,
        xtra_netpair = insert (nI,nE) ([], [th]) xtra_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        xtraIs  = xtraIs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair}
  end;

val op addXIs = rev_foldl addXI;
val op addXEs = rev_foldl addXE;

fun cs addXDs ths = cs addXEs (map Data.make_elim ths);


(*** Deletion of rules 
     Working out what to delete, requires repeating much of the code used
        to insert.
     Separate functions delSI, etc., are not exported; instead delrules
        searches in all the lists and chooses the relevant delXX functions.
***)

fun delSI th 
          (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers,
                    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm (th, safeIs) then
   let val (safe0_rls, safep_rls) = partition Thm.no_prems [th]
   in CS{safe0_netpair = delete (safe0_rls, []) safe0_netpair,
         safep_netpair = delete (safep_rls, []) safep_netpair,
         safeIs = rem_thm (safeIs,th),
         safeEs = safeEs,
         hazIs  = hazIs,
         hazEs  = hazEs,
         xtraIs = xtraIs,
         xtraEs = xtraEs,
         swrappers    = swrappers,
         uwrappers    = uwrappers,
         haz_netpair  = haz_netpair,
         dup_netpair  = dup_netpair,
         xtra_netpair = xtra_netpair}
   end
 else cs;

fun delSE th
          (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm (th, safeEs) then
   let val (safe0_rls, safep_rls) = partition (fn rl => nprems_of rl=1) [th]
   in CS{safe0_netpair = delete ([], safe0_rls) safe0_netpair,
         safep_netpair = delete ([], safep_rls) safep_netpair,
         safeIs = safeIs,
         safeEs = rem_thm (safeEs,th),
         hazIs  = hazIs,
         hazEs  = hazEs,
         xtraIs = xtraIs,
         xtraEs = xtraEs,
         swrappers    = swrappers,
         uwrappers    = uwrappers,
         haz_netpair  = haz_netpair,
         dup_netpair  = dup_netpair,
         xtra_netpair = xtra_netpair}
   end
 else cs;


fun delI th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm (th, hazIs) then
     CS{haz_netpair = delete ([th], []) haz_netpair,
        dup_netpair = delete ([dup_intr th], []) dup_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = rem_thm (hazIs,th),
        hazEs   = hazEs,
        xtraIs  = xtraIs,
        xtraEs  = xtraEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = xtra_netpair}
 else cs;

fun delE th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm (th, hazEs) then
     CS{haz_netpair = delete ([], [th]) haz_netpair,
        dup_netpair = delete ([], [dup_elim th]) dup_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = rem_thm (hazEs,th),
        xtraIs  = xtraIs,
        xtraEs  = xtraEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = xtra_netpair}
 else cs;


fun delXI th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm (th, xtraIs) then
     CS{xtra_netpair = delete ([th], []) xtra_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        xtraIs  = rem_thm (xtraIs,th),
        xtraEs  = xtraEs,
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair}
 else cs;

fun delXE th
         (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
                   safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
 if mem_thm (th, xtraEs) then
     CS{xtra_netpair = delete ([], [th]) xtra_netpair,
        safeIs  = safeIs, 
        safeEs  = safeEs,
        hazIs   = hazIs,
        hazEs   = hazEs,
        xtraIs  = xtraIs,
        xtraEs  = rem_thm (xtraEs,th),
        swrappers     = swrappers,
        uwrappers     = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        haz_netpair  = haz_netpair,
        dup_netpair  = dup_netpair}
 else cs;

(*Delete ALL occurrences of "th" in the claset (perhaps from several lists)*)
fun delrule (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, ...}, th) =
  let val th' = Data.make_elim th in
    if mem_thm (th, safeIs) orelse mem_thm (th, safeEs) orelse
      mem_thm (th, hazIs)  orelse mem_thm (th, hazEs) orelse
      mem_thm (th, xtraIs)  orelse mem_thm (th, xtraEs) orelse
      mem_thm (th', safeEs) orelse mem_thm (th', hazEs) orelse mem_thm (th', xtraEs)
    then delSI th (delSE th (delI th (delE th (delXI th (delXE th
      (delSE th' (delE th' (delXE th' cs))))))))
    else (warning ("Undeclared classical rule\n" ^ (string_of_thm th)); cs)
  end;

val op delrules = foldl delrule;


(*** Modifying the wrapper tacticals ***)
fun update_swrappers 
(CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) f =
 CS{safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    xtraIs = xtraIs, xtraEs = xtraEs,
    swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};

fun update_uwrappers 
(CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, swrappers, uwrappers, 
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) f =
 CS{safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    xtraIs = xtraIs, xtraEs = xtraEs,
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
    let val (del,rest) = partition (fn (n,_) => n=name) swrappers
    in if null del then (warning ("No such safe wrapper in claset: "^ name); 
                         swrappers) else rest end);

(*Remove an unsafe wrapper*)
fun cs delWrapper name = update_uwrappers cs (fn uwrappers =>
    let val (del,rest) = partition (fn (n,_) => n=name) uwrappers
    in if null del then (warning ("No such unsafe wrapper in claset: " ^ name);
                         uwrappers) else rest end);

(*compose a safe tactic sequentially before/alternatively after safe_step_tac*)
fun cs addSbefore  (name,    tac1) = 
    cs addSWrapper (name, fn tac2 => tac1 ORELSE' tac2);
fun cs addSaltern  (name,    tac2) = 
    cs addSWrapper (name, fn tac1 => tac1 ORELSE' tac2);

(*compose a tactic sequentially before/alternatively after the step tactic*)
fun cs addbefore   (name,    tac1) = 
    cs addWrapper  (name, fn tac2 => tac1 APPEND' tac2);
fun cs addaltern   (name,    tac2) =
    cs addWrapper  (name, fn tac1 => tac1 APPEND' tac2);

fun cs addD2     (name, thm) = 
    cs addaltern (name, dtac thm THEN' atac);
fun cs addE2     (name, thm) = 
    cs addaltern (name, etac thm THEN' atac);
fun cs addSD2     (name, thm) = 
    cs addSaltern (name, dmatch_tac [thm] THEN' eq_assume_tac);
fun cs addSE2     (name, thm) = 
    cs addSaltern (name, ematch_tac [thm] THEN' eq_assume_tac);

(*Merge works by adding all new rules of the 2nd claset into the 1st claset.
  Merging the term nets may look more efficient, but the rather delicate
  treatment of priority might get muddled up.*)
fun merge_cs
    (cs as CS{safeIs, safeEs, hazIs, hazEs, xtraIs, xtraEs, ...},
     CS{safeIs=safeIs2, safeEs=safeEs2, hazIs=hazIs2, hazEs=hazEs2,
        xtraIs=xtraIs2, xtraEs=xtraEs2, swrappers, uwrappers, ...}) =
  let val safeIs' = gen_rems eq_thm (safeIs2,safeIs)
      val safeEs' = gen_rems eq_thm (safeEs2,safeEs)
      val  hazIs' = gen_rems eq_thm ( hazIs2, hazIs)
      val  hazEs' = gen_rems eq_thm ( hazEs2, hazEs)
      val xtraIs' = gen_rems eq_thm (xtraIs2, xtraIs)
      val xtraEs' = gen_rems eq_thm (xtraEs2, xtraEs)
      val cs1   = cs addSIs safeIs'
                     addSEs safeEs'
                     addIs  hazIs'
                     addEs  hazEs'
                     addXIs xtraIs'
                     addXEs xtraEs'
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
    biresolution_from_nets_tac (orderlist o filter (nsubgoalsP n)) true;

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
fun fast_tac cs = SELECT_GOAL (DEPTH_SOLVE (step_tac cs 1));

(*Slower but smarter than fast_tac*)
fun best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (step_tac cs 1));

(*even a bit smarter than best_tac*)
fun first_best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (FIRSTGOAL (step_tac cs)));

fun slow_tac cs = SELECT_GOAL (DEPTH_SOLVE (slow_step_tac cs 1));

fun slow_best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (slow_step_tac cs 1));


(***ASTAR with weight weight_ASTAR, by Norbert Voelker*) 
val weight_ASTAR = ref 5; 

fun astar_tac cs = 
  SELECT_GOAL ( ASTAR (has_fewer_prems 1
              , fn level =>(fn thm =>size_of_thm thm + !weight_ASTAR *level)) 
              (step_tac cs 1));

fun slow_astar_tac cs = 
  SELECT_GOAL ( ASTAR (has_fewer_prems 1
              , fn level =>(fn thm =>size_of_thm thm + !weight_ASTAR *level)) 
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



(** claset theory data **)

(* theory data kind 'Provers/claset' *)

structure GlobalClasetArgs =
struct
  val name = "Provers/claset";
  type T = claset ref;

  val empty = ref empty_cs;
  fun copy (ref cs) = (ref cs): T;            (*create new reference!*)
  val prep_ext = copy;
  fun merge (ref cs1, ref cs2) = ref (merge_cs (cs1, cs2));
  fun print _ (ref cs) = print_cs cs;
end;

structure GlobalClaset = TheoryDataFun(GlobalClasetArgs);
val print_claset = GlobalClaset.print;
val claset_ref_of_sg = GlobalClaset.get_sg;
val claset_ref_of = GlobalClaset.get;


(* access claset *)

val claset_of_sg = ! o claset_ref_of_sg;
val claset_of = claset_of_sg o Theory.sign_of;

fun CLASET tacf state = tacf (claset_of_sg (Thm.sign_of_thm state)) state;
fun CLASET' tacf i state = tacf (claset_of_sg (Thm.sign_of_thm state)) i state;

val claset = claset_of o Context.the_context;
val claset_ref = claset_ref_of_sg o Theory.sign_of o Context.the_context;


(* change claset *)

fun change_claset f x = claset_ref () := (f (claset (), x));

val AddDs = change_claset (op addDs);
val AddEs = change_claset (op addEs);
val AddIs = change_claset (op addIs);
val AddSDs = change_claset (op addSDs);
val AddSEs = change_claset (op addSEs);
val AddSIs = change_claset (op addSIs);
val AddXDs = change_claset (op addXDs);
val AddXEs = change_claset (op addXEs);
val AddXIs = change_claset (op addXIs);
val Delrules = change_claset (op delrules);


(* proof data kind 'Provers/claset' *)

structure LocalClasetArgs =
struct
  val name = "Provers/claset";
  type T = claset;
  val init = claset_of;
  fun print _ cs = print_cs cs;
end;

structure LocalClaset = ProofDataFun(LocalClasetArgs);
val print_local_claset = LocalClaset.print;
val get_local_claset = LocalClaset.get;
val put_local_claset = LocalClaset.put;


(* attributes *)

fun change_global_cs f (thy, th) =
  let val r = claset_ref_of thy
  in r := f (! r, [th]); (thy, th) end;

fun change_local_cs f (ctxt, th) =
  let val cs = f (get_local_claset ctxt, [th])
  in (put_local_claset cs ctxt, th) end;

val safe_dest_global = change_global_cs (op addSDs);
val safe_elim_global = change_global_cs (op addSEs);
val safe_intro_global = change_global_cs (op addSIs);
val haz_dest_global = change_global_cs (op addDs);
val haz_elim_global = change_global_cs (op addEs);
val haz_intro_global = change_global_cs (op addIs);
val xtra_dest_global = change_global_cs (op addXDs);
val xtra_elim_global = change_global_cs (op addXEs);
val xtra_intro_global = change_global_cs (op addXIs);
val rule_del_global = change_global_cs (op delrules);

val safe_dest_local = change_local_cs (op addSDs);
val safe_elim_local = change_local_cs (op addSEs);
val safe_intro_local = change_local_cs (op addSIs);
val haz_dest_local = change_local_cs (op addDs);
val haz_elim_local = change_local_cs (op addEs);
val haz_intro_local = change_local_cs (op addIs);
val xtra_dest_local = change_local_cs (op addXDs);
val xtra_elim_local = change_local_cs (op addXEs);
val xtra_intro_local = change_local_cs (op addXIs);
val rule_del_local = change_local_cs (op delrules);


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

(* add / del rules *)

val introN = "intro";
val elimN = "elim";
val destN = "dest";
val ruleN = "rule";

fun cla_att change xtra haz safe = Attrib.syntax
  (Scan.lift ((Args.query >> K xtra || Args.bang >> K safe || Scan.succeed haz) >> change));

fun cla_attr f g h = (cla_att change_global_cs f g h, cla_att change_local_cs f g h);

fun del_args att = Attrib.syntax (Scan.lift Args.del >> K att);
val rule_del_attr = (del_args rule_del_global, del_args rule_del_local);


(* setup_attrs *)

fun elim_format x = Attrib.no_args (Drule.rule_attribute (K Data.make_elim)) x;

val setup_attrs = Attrib.add_attributes
 [("elim_format", (elim_format, elim_format),
    "destruct rule turned into elimination rule format (classical)"),
  (destN, cla_attr (op addXDs) (op addDs) (op addSDs), "declaration of destruction rule"),
  (elimN, cla_attr (op addXEs) (op addEs) (op addSEs), "declaration of elimination rule"),
  (introN, cla_attr (op addXIs) (op addIs) (op addSIs), "declaration of introduction rule"),
  (ruleN, rule_del_attr, "remove declaration of intro/elim/dest rule")];



(** proof methods **)

(* get nets (appropriate order for semi-automatic methods) *)

local
  val imp_elim_netpair = insert (0, 0) ([], [imp_elim]) empty_netpair;
  val not_elim_netpair = insert (0, 0) ([], [Data.not_elim]) empty_netpair;
in
  fun get_nets (CS {safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair, ...}) =
    [imp_elim_netpair, safe0_netpair, safep_netpair, not_elim_netpair, haz_netpair, dup_netpair, xtra_netpair];
end;


(* METHOD_CLASET' *)

fun METHOD_CLASET' tac ctxt =
  Method.METHOD (HEADGOAL o tac (get_local_claset ctxt));


val trace_rules = ref false;

local

fun trace rules i =
  if not (! trace_rules) then ()
  else Pretty.writeln (Pretty.big_list ("trying standard rule(s) on goal #" ^ string_of_int i ^ ":")
    (map Display.pretty_thm rules));


fun order_rules xs = map snd (Tactic.orderlist xs);

fun find_rules concl nets =
  let fun rules_of (inet, _) = order_rules (Net.unify_term inet concl)
  in flat (map rules_of nets) end;

fun find_erules [] _ = []
  | find_erules (fact :: _) nets =
      let
        fun may_unify net = Net.unify_term net o Logic.strip_assums_concl o #prop o Thm.rep_thm;
        fun erules_of (_, enet) = order_rules (may_unify enet fact);
      in flat (map erules_of nets) end;


fun some_rule_tac cs facts =
  let
    val nets = get_nets cs;
    val erules = find_erules facts nets;

    val tac = SUBGOAL (fn (goal, i) =>
      let
        val irules = find_rules (Logic.strip_assums_concl goal) nets;
        val rules = erules @ irules;
        val ruleq = Method.multi_resolves facts rules;
      in trace rules i; fn st => Seq.flat (Seq.map (fn rule => Tactic.rtac rule i st) ruleq) end);
  in tac end;

fun rule_tac [] cs facts = some_rule_tac cs facts
  | rule_tac rules _ facts = Method.rule_tac rules facts;

in
  val rule = METHOD_CLASET' o rule_tac;
end;


(* intro / elim methods *)

local

fun intro_elim_tac netpair_of res_tac rules cs facts =
  let
    val tac =
      if null rules then FIRST' (map (bimatch_from_nets_tac o netpair_of) (get_nets cs))
      else res_tac rules;
  in Method.insert_tac facts THEN' REPEAT_ALL_NEW tac end;

val intro_tac = intro_elim_tac (fn (inet, _) => (inet, Net.empty)) Tactic.match_tac;
val elim_tac = intro_elim_tac (fn (_, enet) => (Net.empty, enet)) Tactic.ematch_tac;

in
  val intro = METHOD_CLASET' o intro_tac;
  val elim = METHOD_CLASET' o elim_tac;
end;


(* contradiction method *)

val contradiction = Method.rule [Data.not_elim, Data.not_elim COMP Drule.swap_prems_rl];


(* automatic methods *)

val cla_modifiers =
 [Args.$$$ destN -- Args.query_colon >> K ((I, xtra_dest_local):Method.modifier),
  Args.$$$ destN -- Args.bang_colon >> K (I, safe_dest_local),
  Args.$$$ destN -- Args.colon >> K (I, haz_dest_local),
  Args.$$$ elimN -- Args.query_colon >> K (I, xtra_elim_local),
  Args.$$$ elimN -- Args.bang_colon >> K (I, safe_elim_local),
  Args.$$$ elimN -- Args.colon >> K (I, haz_elim_local),
  Args.$$$ introN -- Args.query_colon >> K (I, xtra_intro_local),
  Args.$$$ introN -- Args.bang_colon >> K (I, safe_intro_local),
  Args.$$$ introN -- Args.colon >> K (I, haz_intro_local),
  Args.del -- Args.colon >> K (I, rule_del_local)];

fun cla_meth tac prems ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN tac (get_local_claset ctxt));

fun cla_meth' tac prems ctxt = Method.METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN' tac (get_local_claset ctxt)));

val cla_method = Method.bang_sectioned_args cla_modifiers o cla_meth;
val cla_method' = Method.bang_sectioned_args cla_modifiers o cla_meth';



(** setup_methods **)

val setup_methods = Method.add_methods
 [("default", Method.thms_ctxt_args rule, "apply some rule (classical)"),
  ("rule", Method.thms_ctxt_args rule, "apply some rule (classical)"),
  ("contradiction", Method.no_args contradiction, "proof by contradiction"),
  ("intro", Method.thms_ctxt_args intro, "repeatedly apply introduction rules"),
  ("elim", Method.thms_ctxt_args elim, "repeatedly apply elimination rules"),
  ("clarify", cla_method' clarify_tac, "repeatedly apply safe steps"),
  ("fast", cla_method' fast_tac, "classical prover (depth-first)"),
  ("slow", cla_method' slow_tac, "classical prover (slow depth-first)"),
  ("best", cla_method' best_tac, "classical prover (best-first)"),
  ("safe", cla_method safe_tac, "classical prover (apply safe rules)")];



(** theory setup **)

val setup = [GlobalClaset.init, LocalClaset.init, setup_attrs, setup_methods];



(** outer syntax **)

val print_clasetP =
  OuterSyntax.improper_command "print_claset" "print context of Classical Reasoner"
    OuterSyntax.Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o (Toplevel.keep
      (Toplevel.node_case print_claset (print_local_claset o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_clasetP];


end;
