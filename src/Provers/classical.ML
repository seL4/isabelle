(*  Title:      Provers/classical.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Theorem prover for classical reasoning, including predicate calculus, set
theory, etc.

Rules must be classified as intro, elim, safe, unsafe.

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
  val sizef: thm -> int  (* size function for BEST_FIRST, typically size_of_thm *)
  val hyp_subst_tacs: (Proof.context -> int -> tactic) list (* optional tactics for
    substitution in the hypotheses; assumed to be safe! *)
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
  val addSWrapper: Proof.context * (string * (Proof.context -> wrapper)) -> Proof.context
  val delSWrapper: Proof.context * string -> Proof.context
  val addWrapper: Proof.context * (string * (Proof.context -> wrapper)) -> Proof.context
  val delWrapper: Proof.context * string -> Proof.context
  val addSbefore: Proof.context * (string * (Proof.context -> int -> tactic)) -> Proof.context
  val addSafter: Proof.context * (string * (Proof.context -> int -> tactic)) -> Proof.context
  val addbefore: Proof.context * (string * (Proof.context -> int -> tactic)) -> Proof.context
  val addafter: Proof.context * (string * (Proof.context -> int -> tactic)) -> Proof.context
  val addD2: Proof.context * (string * thm) -> Proof.context
  val addE2: Proof.context * (string * thm) -> Proof.context
  val addSD2: Proof.context * (string * thm) -> Proof.context
  val addSE2: Proof.context * (string * thm) -> Proof.context
  val appSWrappers: Proof.context -> wrapper
  val appWrappers: Proof.context -> wrapper

  val claset_of: Proof.context -> claset
  val put_claset: claset -> Proof.context -> Proof.context

  val map_theory_claset: (Proof.context -> Proof.context) -> theory -> theory

  val fast_tac: Proof.context -> int -> tactic
  val slow_tac: Proof.context -> int -> tactic
  val astar_tac: Proof.context -> int -> tactic
  val slow_astar_tac: Proof.context -> int -> tactic
  val best_tac: Proof.context -> int -> tactic
  val first_best_tac: Proof.context -> int -> tactic
  val slow_best_tac: Proof.context -> int -> tactic
  val depth_tac: Proof.context -> int -> int -> tactic
  val deepen_tac: Proof.context -> int -> int -> tactic

  val contr_tac: Proof.context -> int -> tactic
  val dup_elim: Proof.context -> thm -> thm
  val dup_intr: thm -> thm
  val dup_step_tac: Proof.context -> int -> tactic
  val eq_mp_tac: Proof.context -> int -> tactic
  val unsafe_step_tac: Proof.context -> int -> tactic
  val mp_tac: Proof.context -> int -> tactic
  val safe_tac: Proof.context -> tactic
  val safe_steps_tac: Proof.context -> int -> tactic
  val safe_step_tac: Proof.context -> int -> tactic
  val clarify_tac: Proof.context -> int -> tactic
  val clarify_step_tac: Proof.context -> int -> tactic
  val step_tac: Proof.context -> int -> tactic
  val slow_step_tac: Proof.context -> int -> tactic
  val swapify: thm list -> thm list
  val swap_res_tac: Proof.context -> thm list -> int -> tactic
  val inst_step_tac: Proof.context -> int -> tactic
  val inst0_step_tac: Proof.context -> int -> tactic
  val instp_step_tac: Proof.context -> int -> tactic
end;

signature CLASSICAL =
sig
  include BASIC_CLASSICAL
  val classical_rule: Proof.context -> thm -> thm
  type rule = thm * (thm * thm list) * (thm * thm list)
  val rep_cs: claset ->
   {safeIs: rule Item_Net.T,
    safeEs: rule Item_Net.T,
    unsafeIs: rule Item_Net.T,
    unsafeEs: rule Item_Net.T,
    swrappers: (string * (Proof.context -> wrapper)) list,
    uwrappers: (string * (Proof.context -> wrapper)) list,
    safe0_netpair: Bires.netpair,
    safep_netpair: Bires.netpair,
    unsafe_netpair: Bires.netpair,
    dup_netpair: Bires.netpair,
    extra_netpair: Bires.netpair}
  val get_cs: Context.generic -> claset
  val map_cs: (claset -> claset) -> Context.generic -> Context.generic
  val safe_dest: int option -> attribute
  val safe_elim: int option -> attribute
  val safe_intro: int option -> attribute
  val unsafe_dest: int option -> attribute
  val unsafe_elim: int option -> attribute
  val unsafe_intro: int option -> attribute
  val rule_del: attribute
  val rule_tac: Proof.context -> thm list -> thm list -> int -> tactic
  val standard_tac: Proof.context -> thm list -> tactic
  val cla_modifiers: Method.modifier parser list
  val cla_method:
    (Proof.context -> tactic) -> (Proof.context -> Proof.method) context_parser
  val cla_method':
    (Proof.context -> int -> tactic) -> (Proof.context -> Proof.method) context_parser
end;


functor Classical(Data: CLASSICAL_DATA): CLASSICAL =
struct

(** classical elimination rules **)

(*
Classical reasoning requires stronger elimination rules.  For
instance, make_elim of Pure transforms the HOL rule injD into

    [| inj f; f x = f y; x = y ==> PROP W |] ==> PROP W

Such rules can cause fast_tac to fail and blast_tac to report "PROOF
FAILED"; classical_rule will strengthen this to

    [| inj f; ~ W ==> f x = f y; x = y ==> W |] ==> W
*)

fun classical_rule ctxt rule =
  if is_some (Object_Logic.elim_concl ctxt rule) then
    let
      val thy = Proof_Context.theory_of ctxt;
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
          then eresolve_tac ctxt [thin_rl] i
          else all_tac))
        |> Seq.hd
        |> Drule.zero_var_indexes;
    in if Thm.equiv_thm thy (rule, rule'') then rule else rule'' end
  else rule;

(*flatten nested meta connectives in prems*)
fun flat_rule ctxt =
  Conv.fconv_rule (Conv.prems_conv ~1 (Object_Logic.atomize_prems ctxt));


(*** Useful tactics for classical reasoning ***)

(*Prove goal that assumes both P and ~P.
  No backtracking if it finds an equal assumption.  Perhaps should call
  ematch_tac instead of eresolve_tac, but then cannot prove ZF/cantor.*)
fun contr_tac ctxt =
  eresolve_tac ctxt [Data.not_elim] THEN' (eq_assume_tac ORELSE' assume_tac ctxt);

(*Finds P-->Q and P in the assumptions, replaces implication by Q.
  Could do the same thing for P<->Q and P... *)
fun mp_tac ctxt i =
  eresolve_tac ctxt [Data.not_elim, Data.imp_elim] i THEN assume_tac ctxt i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac ctxt i = ematch_tac ctxt [Data.not_elim, Data.imp_elim] i THEN eq_assume_tac i;

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [Data.swap]);
val swapped = Thm.rule_attribute [] (fn _ => fn th => th RSN (2, Data.swap));

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac ctxt rls =
  let
    val transfer = Thm.transfer' ctxt;
    fun addrl rl brls = (false, transfer rl) :: (true, transfer rl RSN (2, Data.swap)) :: brls;
  in
    assume_tac ctxt ORELSE'
    contr_tac ctxt ORELSE'
    biresolve_tac ctxt (fold_rev addrl rls [])
  end;

(*Duplication of unsafe rules, for complete provers*)
fun dup_intr th = zero_var_indexes (th RS Data.classical);

fun dup_elim ctxt th =
  let val rl = (th RSN (2, revcut_rl)) |> Thm.assumption (SOME ctxt) 2 |> Seq.hd;
  in rule_by_tactic ctxt (TRYALL (eresolve_tac ctxt [revcut_rl])) rl end;


(**** Classical rule sets ****)

type rule = thm * (thm * thm list) * (thm * thm list);
  (*external form, internal form (possibly swapped), dup form (possibly swapped)*)

type wrapper = (int -> tactic) -> int -> tactic;

datatype claset =
  CS of
   {safeIs: rule Item_Net.T,  (*safe introduction rules*)
    safeEs: rule Item_Net.T,  (*safe elimination rules*)
    unsafeIs: rule Item_Net.T,  (*unsafe introduction rules*)
    unsafeEs: rule Item_Net.T,  (*unsafe elimination rules*)
    swrappers: (string * (Proof.context -> wrapper)) list,  (*for transforming safe_step_tac*)
    uwrappers: (string * (Proof.context -> wrapper)) list,  (*for transforming step_tac*)
    safe0_netpair: Bires.netpair,  (*nets for trivial cases*)
    safep_netpair: Bires.netpair,  (*nets for >0 subgoals*)
    unsafe_netpair: Bires.netpair,  (*nets for unsafe rules*)
    dup_netpair: Bires.netpair,  (*nets for duplication*)
    extra_netpair: Bires.netpair};  (*nets for extra rules*)

val empty_rules: rule Item_Net.T =
  Item_Net.init (Thm.eq_thm_prop o apply2 #1) (single o Thm.full_prop_of o #1);

val empty_cs =
  CS
   {safeIs = empty_rules,
    safeEs = empty_rules,
    unsafeIs = empty_rules,
    unsafeEs = empty_rules,
    swrappers = [],
    uwrappers = [],
    safe0_netpair = Bires.empty_netpair,
    safep_netpair = Bires.empty_netpair,
    unsafe_netpair = Bires.empty_netpair,
    dup_netpair = Bires.empty_netpair,
    extra_netpair = Bires.empty_netpair};

fun rep_cs (CS args) = args;


(*** Adding (un)safe introduction or elimination rules.

    In case of overlap, new rules are tried BEFORE old ones!!
***)

fun joinrules (intrs, elims) = map (pair true) elims @ map (pair false) intrs;

(*Priority: prefer rules with fewest subgoals,
  then rules added most recently (preferring the head of the list).*)
fun tag_brls k [] = []
  | tag_brls k (brl::brls) =
      ({weight = Bires.subgoals_of brl, index = k}, brl) ::
      tag_brls (k+1) brls;

fun tag_brls' _ _ [] = []
  | tag_brls' w k (brl::brls) = ({weight = w, index = k}, brl) :: tag_brls' w (k + 1) brls;

(*Insert into netpair that already has nI intr rules and nE elim rules.
  Count the intr rules double (to account for swapify).  Negate to give the
  new insertions the lowest priority.*)
fun insert (nI, nE) = Bires.insert_tagged_rules o (tag_brls (~(2*nI+nE))) o joinrules;
fun insert' w (nI, nE) = Bires.insert_tagged_rules o tag_brls' w (~(nI + nE)) o joinrules;

fun delete x = Bires.delete_tagged_rules (joinrules x);

fun bad_thm ctxt msg th = error (msg ^ "\n" ^ Thm.string_of_thm ctxt th);

fun make_elim ctxt th =
  if Thm.no_prems th then bad_thm ctxt "Ill-formed destruction rule" th
  else Tactic.make_elim th;

fun warn_thm ctxt msg th =
  if Context_Position.is_really_visible ctxt
  then warning (msg ^ Thm.string_of_thm ctxt th) else ();

fun warn_rules ctxt msg rules (r: rule) =
  Item_Net.member rules r andalso (warn_thm ctxt msg (#1 r); true);

fun warn_claset ctxt r (CS {safeIs, safeEs, unsafeIs, unsafeEs, ...}) =
  warn_rules ctxt "Rule already declared as safe introduction (intro!)\n" safeIs r orelse
  warn_rules ctxt "Rule already declared as safe elimination (elim!)\n" safeEs r orelse
  warn_rules ctxt "Rule already declared as introduction (intro)\n" unsafeIs r orelse
  warn_rules ctxt "Rule already declared as elimination (elim)\n" unsafeEs r;


(*** add rules ***)

fun add_safe_intro w r
    (cs as CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  if Item_Net.member safeIs r then cs
  else
    let
      val (th, rl, _) = r;
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
        List.partition (Thm.no_prems o fst) [rl];
      val nI = Item_Net.length safeIs + 1;
      val nE = Item_Net.length safeEs;
    in
      CS
       {safeIs = Item_Net.update r safeIs,
        safe0_netpair = insert (nI, nE) (map fst safe0_rls, maps snd safe0_rls) safe0_netpair,
        safep_netpair = insert (nI, nE) (map fst safep_rls, maps snd safep_rls) safep_netpair,
        safeEs = safeEs,
        unsafeIs = unsafeIs,
        unsafeEs = unsafeEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        unsafe_netpair = unsafe_netpair,
        dup_netpair = dup_netpair,
        extra_netpair = insert' (the_default 0 w) (nI, nE) ([th], []) extra_netpair}
    end;

fun add_safe_elim w r
    (cs as CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  if Item_Net.member safeEs r then cs
  else
    let
      val (th, rl, _) = r;
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
        List.partition (Thm.one_prem o #1) [rl];
      val nI = Item_Net.length safeIs;
      val nE = Item_Net.length safeEs + 1;
    in
      CS
       {safeEs = Item_Net.update r safeEs,
        safe0_netpair = insert (nI, nE) ([], map fst safe0_rls) safe0_netpair,
        safep_netpair = insert (nI, nE) ([], map fst safep_rls) safep_netpair,
        safeIs = safeIs,
        unsafeIs = unsafeIs,
        unsafeEs = unsafeEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        unsafe_netpair = unsafe_netpair,
        dup_netpair = dup_netpair,
        extra_netpair = insert' (the_default 0 w) (nI, nE) ([], [th]) extra_netpair}
    end;

fun add_unsafe_intro w r
    (cs as CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  if Item_Net.member unsafeIs r then cs
  else
    let
      val (th, rl, dup_rl) = r;
      val nI = Item_Net.length unsafeIs + 1;
      val nE = Item_Net.length unsafeEs;
    in
      CS
       {unsafeIs = Item_Net.update r unsafeIs,
        unsafe_netpair = insert (nI, nE) ([fst rl], snd rl) unsafe_netpair,
        dup_netpair = insert (nI, nE) ([fst dup_rl], snd dup_rl) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        unsafeEs = unsafeEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        extra_netpair = insert' (the_default 1 w) (nI, nE) ([th], []) extra_netpair}
    end;

fun add_unsafe_elim w r
    (cs as CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  if Item_Net.member unsafeEs r then cs
  else
    let
      val (th, rl, dup_rl) = r;
      val nI = Item_Net.length unsafeIs;
      val nE = Item_Net.length unsafeEs + 1;
    in
      CS
       {unsafeEs = Item_Net.update r unsafeEs,
        unsafe_netpair = insert (nI, nE) ([], [fst rl]) unsafe_netpair,
        dup_netpair = insert (nI, nE) ([], [fst dup_rl]) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        unsafeIs = unsafeIs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        extra_netpair = insert' (the_default 1 w) (nI, nE) ([], [th]) extra_netpair}
    end;

fun trim_context (th, (th1, ths1), (th2, ths2)) =
  (Thm.trim_context th,
    (Thm.trim_context th1, map Thm.trim_context ths1),
    (Thm.trim_context th2, map Thm.trim_context ths2));

fun addSI w ctxt th (cs as CS {safeIs, ...}) =
  let
    val th' = flat_rule ctxt th;
    val rl = (th', swapify [th']);
    val r = trim_context (th, rl, rl);
    val _ =
      warn_rules ctxt "Ignoring duplicate safe introduction (intro!)\n" safeIs r orelse
      warn_claset ctxt r cs;
  in add_safe_intro w r cs end;

fun addSE w ctxt th (cs as CS {safeEs, ...}) =
  let
    val _ = Thm.no_prems th andalso bad_thm ctxt "Ill-formed elimination rule" th;
    val th' = classical_rule ctxt (flat_rule ctxt th);
    val rl = (th', []);
    val r = trim_context (th, rl, rl);
    val _ =
      warn_rules ctxt "Ignoring duplicate safe elimination (elim!)\n" safeEs r orelse
      warn_claset ctxt r cs;
  in add_safe_elim w r cs end;

fun addSD w ctxt th = addSE w ctxt (make_elim ctxt th);

fun addI w ctxt th (cs as CS {unsafeIs, ...}) =
  let
    val th' = flat_rule ctxt th;
    val dup_th' = dup_intr th' handle THM _ => bad_thm ctxt "Ill-formed introduction rule" th;
    val r = trim_context (th, (th', swapify [th']), (dup_th', swapify [dup_th']));
    val _ =
      warn_rules ctxt "Ignoring duplicate introduction (intro)\n" unsafeIs r orelse
      warn_claset ctxt r cs;
  in add_unsafe_intro w r cs end;

fun addE w ctxt th (cs as CS {unsafeEs, ...}) =
  let
    val _ = Thm.no_prems th andalso bad_thm ctxt "Ill-formed elimination rule" th;
    val th' = classical_rule ctxt (flat_rule ctxt th);
    val dup_th' = dup_elim ctxt th' handle THM _ => bad_thm ctxt "Ill-formed elimination rule" th;
    val r = trim_context (th, (th', []), (dup_th', []));
    val _ =
      warn_rules ctxt "Ignoring duplicate elimination (elim)\n" unsafeEs r orelse
      warn_claset ctxt r cs;
  in add_unsafe_elim w r cs end;

fun addD w ctxt th = addE w ctxt (make_elim ctxt th);


(*** delete rules ***)

local

fun del_safe_intro (r: rule)
  (CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  let
    val (th, rl, _) = r;
    val (safe0_rls, safep_rls) = List.partition (Thm.no_prems o fst) [rl];
  in
    CS
     {safe0_netpair = delete (map fst safe0_rls, maps snd safe0_rls) safe0_netpair,
      safep_netpair = delete (map fst safep_rls, maps snd safep_rls) safep_netpair,
      safeIs = Item_Net.remove r safeIs,
      safeEs = safeEs,
      unsafeIs = unsafeIs,
      unsafeEs = unsafeEs,
      swrappers = swrappers,
      uwrappers = uwrappers,
      unsafe_netpair = unsafe_netpair,
      dup_netpair = dup_netpair,
      extra_netpair = delete ([th], []) extra_netpair}
  end;

fun del_safe_elim (r: rule)
  (CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  let
    val (th, rl, _) = r;
    val (safe0_rls, safep_rls) = List.partition (Thm.one_prem o #1) [rl];
  in
    CS
     {safe0_netpair = delete ([], map fst safe0_rls) safe0_netpair,
      safep_netpair = delete ([], map fst safep_rls) safep_netpair,
      safeIs = safeIs,
      safeEs = Item_Net.remove r safeEs,
      unsafeIs = unsafeIs,
      unsafeEs = unsafeEs,
      swrappers = swrappers,
      uwrappers = uwrappers,
      unsafe_netpair = unsafe_netpair,
      dup_netpair = dup_netpair,
      extra_netpair = delete ([], [th]) extra_netpair}
  end;

fun del_unsafe_intro (r as (th, (th', swapped_th'), (dup_th', swapped_dup_th')))
  (CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  CS
   {unsafe_netpair = delete ([th'], swapped_th') unsafe_netpair,
    dup_netpair = delete ([dup_th'], swapped_dup_th') dup_netpair,
    safeIs = safeIs,
    safeEs = safeEs,
    unsafeIs = Item_Net.remove r unsafeIs,
    unsafeEs = unsafeEs,
    swrappers = swrappers,
    uwrappers = uwrappers,
    safe0_netpair = safe0_netpair,
    safep_netpair = safep_netpair,
    extra_netpair = delete ([th], []) extra_netpair};

fun del_unsafe_elim (r as (th, (th', _), (dup_th', _)))
  (CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  CS
   {unsafe_netpair = delete ([], [th']) unsafe_netpair,
    dup_netpair = delete ([], [dup_th']) dup_netpair,
    safeIs = safeIs,
    safeEs = safeEs,
    unsafeIs = unsafeIs,
    unsafeEs = Item_Net.remove r unsafeEs,
    swrappers = swrappers,
    uwrappers = uwrappers,
    safe0_netpair = safe0_netpair,
    safep_netpair = safep_netpair,
    extra_netpair = delete ([], [th]) extra_netpair};

fun del f rules th cs =
  fold f (Item_Net.lookup rules (th, (th, []), (th, []))) cs;

in

fun delrule ctxt th (cs as CS {safeIs, safeEs, unsafeIs, unsafeEs, ...}) =
  let
    val th' = Tactic.make_elim th;
    val r = (th, (th, []), (th, []));
    val r' = (th', (th', []), (th', []));
  in
    if Item_Net.member safeIs r orelse Item_Net.member safeEs r orelse
      Item_Net.member unsafeIs r orelse Item_Net.member unsafeEs r orelse
      Item_Net.member safeEs r' orelse Item_Net.member unsafeEs r'
    then
      cs
      |> del del_safe_intro safeIs th
      |> del del_safe_elim safeEs th
      |> del del_safe_elim safeEs th'
      |> del del_unsafe_intro unsafeIs th
      |> del del_unsafe_elim unsafeEs th
      |> del del_unsafe_elim unsafeEs th'
    else (warn_thm ctxt "Undeclared classical rule\n" th; cs)
  end;

end;



(** claset data **)

(* wrappers *)

fun map_swrappers f
  (CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, unsafeIs = unsafeIs, unsafeEs = unsafeEs,
    swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    unsafe_netpair = unsafe_netpair, dup_netpair = dup_netpair, extra_netpair = extra_netpair};

fun map_uwrappers f
  (CS {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, unsafeIs = unsafeIs, unsafeEs = unsafeEs,
    swrappers = swrappers, uwrappers = f uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    unsafe_netpair = unsafe_netpair, dup_netpair = dup_netpair, extra_netpair = extra_netpair};


(* merge_cs *)

(*Merge works by adding all new rules of the 2nd claset into the 1st claset,
  in order to preserve priorities reliably.*)

fun merge_thms add thms1 thms2 =
  fold_rev (fn thm => if Item_Net.member thms1 thm then I else add thm) (Item_Net.content thms2);

fun merge_cs (cs as CS {safeIs, safeEs, unsafeIs, unsafeEs, ...},
    cs' as CS {safeIs = safeIs2, safeEs = safeEs2, unsafeIs = unsafeIs2, unsafeEs = unsafeEs2,
      swrappers, uwrappers, ...}) =
  if pointer_eq (cs, cs') then cs
  else
    cs
    |> merge_thms (add_safe_intro NONE) safeIs safeIs2
    |> merge_thms (add_safe_elim NONE) safeEs safeEs2
    |> merge_thms (add_unsafe_intro NONE) unsafeIs unsafeIs2
    |> merge_thms (add_unsafe_elim NONE) unsafeEs unsafeEs2
    |> map_swrappers (fn ws => AList.merge (op =) (K true) (ws, swrappers))
    |> map_uwrappers (fn ws => AList.merge (op =) (K true) (ws, uwrappers));


(* data *)

structure Claset = Generic_Data
(
  type T = claset;
  val empty = empty_cs;
  val merge = merge_cs;
);

val claset_of = Claset.get o Context.Proof;
val rep_claset_of = rep_cs o claset_of;

val get_cs = Claset.get;
val map_cs = Claset.map;

fun map_theory_claset f thy =
  let
    val ctxt' = f (Proof_Context.init_global thy);
    val thy' = Proof_Context.theory_of ctxt';
  in Context.theory_map (Claset.map (K (claset_of ctxt'))) thy' end;

fun map_claset f = Context.proof_map (map_cs f);
fun put_claset cs = map_claset (K cs);

fun print_claset ctxt =
  let
    val {safeIs, safeEs, unsafeIs, unsafeEs, swrappers, uwrappers, ...} = rep_claset_of ctxt;
    val pretty_thms = map (Thm.pretty_thm_item ctxt o #1) o Item_Net.content;
  in
    [Pretty.big_list "safe introduction rules (intro!):" (pretty_thms safeIs),
      Pretty.big_list "introduction rules (intro):" (pretty_thms unsafeIs),
      Pretty.big_list "safe elimination rules (elim!):" (pretty_thms safeEs),
      Pretty.big_list "elimination rules (elim):" (pretty_thms unsafeEs),
      Pretty.strs ("safe wrappers:" :: map #1 swrappers),
      Pretty.strs ("unsafe wrappers:" :: map #1 uwrappers)]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* old-style declarations *)

fun decl f (ctxt, ths) = map_claset (fold_rev (f ctxt) ths) ctxt;

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
fun ctxt addSWrapper new_swrapper = ctxt |> map_claset
  (map_swrappers (update_warn ("Overwriting safe wrapper " ^ fst new_swrapper) new_swrapper));

(*Add/replace an unsafe wrapper*)
fun ctxt addWrapper new_uwrapper = ctxt |> map_claset
  (map_uwrappers (update_warn ("Overwriting unsafe wrapper " ^ fst new_uwrapper) new_uwrapper));

(*Remove a safe wrapper*)
fun ctxt delSWrapper name = ctxt |> map_claset
  (map_swrappers (delete_warn ("No such safe wrapper in claset: " ^ name) name));

(*Remove an unsafe wrapper*)
fun ctxt delWrapper name = ctxt |> map_claset
  (map_uwrappers (delete_warn ("No such unsafe wrapper in claset: " ^ name) name));

(* compose a safe tactic alternatively before/after safe_step_tac *)
fun ctxt addSbefore (name, tac1) =
  ctxt addSWrapper (name, fn ctxt => fn tac2 => tac1 ctxt ORELSE' tac2);
fun ctxt addSafter (name, tac2) =
  ctxt addSWrapper (name, fn ctxt => fn tac1 => tac1 ORELSE' tac2 ctxt);

(*compose a tactic alternatively before/after the step tactic *)
fun ctxt addbefore (name, tac1) =
  ctxt addWrapper (name, fn ctxt => fn tac2 => tac1 ctxt APPEND' tac2);
fun ctxt addafter (name, tac2) =
  ctxt addWrapper (name, fn ctxt => fn tac1 => tac1 APPEND' tac2 ctxt);

fun ctxt addD2 (name, thm) =
  ctxt addafter (name, fn ctxt' => dresolve_tac ctxt' [thm] THEN' assume_tac ctxt');
fun ctxt addE2 (name, thm) =
  ctxt addafter (name, fn ctxt' => eresolve_tac ctxt' [thm] THEN' assume_tac ctxt');
fun ctxt addSD2 (name, thm) =
  ctxt addSafter (name, fn ctxt' => dmatch_tac ctxt' [thm] THEN' eq_assume_tac);
fun ctxt addSE2 (name, thm) =
  ctxt addSafter (name, fn ctxt' => ematch_tac ctxt' [thm] THEN' eq_assume_tac);



(**** Simple tactics for theorem proving ****)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun safe_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    appSWrappers ctxt
      (FIRST'
       [eq_assume_tac,
        eq_mp_tac ctxt,
        Bires.bimatch_from_nets_tac ctxt safe0_netpair,
        FIRST' (map (fn tac => tac ctxt) Data.hyp_subst_tacs),
        Bires.bimatch_from_nets_tac ctxt safep_netpair])
  end;

(*Repeatedly attack a subgoal using safe inferences -- it's deterministic!*)
fun safe_steps_tac ctxt =
  REPEAT_DETERM1 o (fn i => COND (has_fewer_prems i) no_tac (safe_step_tac ctxt i));

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun safe_tac ctxt = REPEAT_DETERM1 (FIRSTGOAL (safe_steps_tac ctxt));


(*** Clarify_tac: do safe steps without causing branching ***)

(*version of Bires.bimatch_from_nets_tac that only applies rules that
  create precisely n subgoals.*)
fun n_bimatch_from_nets_tac ctxt n =
  Bires.biresolution_from_nets_tac ctxt Bires.tag_ord
    (SOME (fn rl => Bires.subgoals_of rl = n)) true;

fun eq_contr_tac ctxt i = ematch_tac ctxt [Data.not_elim] i THEN eq_assume_tac i;
fun eq_assume_contr_tac ctxt = eq_assume_tac ORELSE' eq_contr_tac ctxt;

(*Two-way branching is allowed only if one of the branches immediately closes*)
fun bimatch2_tac ctxt netpair i =
  n_bimatch_from_nets_tac ctxt 2 netpair i THEN
  (eq_assume_contr_tac ctxt i ORELSE eq_assume_contr_tac ctxt (i + 1));

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun clarify_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    appSWrappers ctxt
     (FIRST'
       [eq_assume_contr_tac ctxt,
        Bires.bimatch_from_nets_tac ctxt safe0_netpair,
        FIRST' (map (fn tac => tac ctxt) Data.hyp_subst_tacs),
        n_bimatch_from_nets_tac ctxt 1 safep_netpair,
        bimatch2_tac ctxt safep_netpair])
  end;

fun clarify_tac ctxt = SELECT_GOAL (REPEAT_DETERM (clarify_step_tac ctxt 1));


(*** Unsafe steps instantiate variables or lose information ***)

(*Backtracking is allowed among the various these unsafe ways of
  proving a subgoal.  *)
fun inst0_step_tac ctxt =
  assume_tac ctxt APPEND'
  contr_tac ctxt APPEND'
  Bires.biresolve_from_nets_tac ctxt (#safe0_netpair (rep_claset_of ctxt));

(*These unsafe steps could generate more subgoals.*)
fun instp_step_tac ctxt =
  Bires.biresolve_from_nets_tac ctxt (#safep_netpair (rep_claset_of ctxt));

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac ctxt = inst0_step_tac ctxt APPEND' instp_step_tac ctxt;

fun unsafe_step_tac ctxt =
  Bires.biresolve_from_nets_tac ctxt (#unsafe_netpair (rep_claset_of ctxt));

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac ctxt i =
  safe_tac ctxt ORELSE appWrappers ctxt (inst_step_tac ctxt ORELSE' unsafe_step_tac ctxt) i;

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac ctxt i =
  safe_tac ctxt ORELSE appWrappers ctxt (inst_step_tac ctxt APPEND' unsafe_step_tac ctxt) i;


(**** The following tactics all fail unless they solve one goal ****)

(*Dumb but fast*)
fun fast_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN' SELECT_GOAL (DEPTH_SOLVE (step_tac ctxt 1));

(*Slower but smarter than fast_tac*)
fun best_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN'
  SELECT_GOAL (BEST_FIRST (Thm.no_prems, Data.sizef) (step_tac ctxt 1));

(*even a bit smarter than best_tac*)
fun first_best_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN'
  SELECT_GOAL (BEST_FIRST (Thm.no_prems, Data.sizef) (FIRSTGOAL (step_tac ctxt)));

fun slow_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN'
  SELECT_GOAL (DEPTH_SOLVE (slow_step_tac ctxt 1));

fun slow_best_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN'
  SELECT_GOAL (BEST_FIRST (Thm.no_prems, Data.sizef) (slow_step_tac ctxt 1));


(***ASTAR with weight weight_ASTAR, by Norbert Voelker*)

val weight_ASTAR = 5;

fun astar_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN'
  SELECT_GOAL
    (ASTAR (Thm.no_prems, fn lev => fn thm => Data.sizef thm + weight_ASTAR * lev)
      (step_tac ctxt 1));

fun slow_astar_tac ctxt =
  Object_Logic.atomize_prems_tac ctxt THEN'
  SELECT_GOAL
    (ASTAR (Thm.no_prems, fn lev => fn thm => Data.sizef thm + weight_ASTAR * lev)
      (slow_step_tac ctxt 1));


(**** Complete tactic, loosely based upon LeanTaP.  This tactic is the outcome
  of much experimentation!  Changing APPEND to ORELSE below would prove
  easy theorems faster, but loses completeness -- and many of the harder
  theorems such as 43. ****)

(*Non-deterministic!  Could always expand the first unsafe connective.
  That's hard to implement and did not perform better in experiments, due to
  greater search depth required.*)
fun dup_step_tac ctxt =
  Bires.biresolve_from_nets_tac ctxt (#dup_netpair (rep_claset_of ctxt));

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
  Thm.declaration_attribute (fn th => fn context =>
    map_cs (f (Context.proof_of context) th) context);

val safe_elim = attrib o addSE;
val safe_intro = attrib o addSI;
val safe_dest = attrib o addSD;
val unsafe_elim = attrib o addE;
val unsafe_intro = attrib o addI;
val unsafe_dest = attrib o addD;

val rule_del =
  Thm.declaration_attribute (fn th => fn context =>
    context
    |> map_cs (delrule (Context.proof_of context) th)
    |> Thm.attribute_declaration Context_Rules.rule_del th);



(** concrete syntax of attributes **)

val introN = "intro";
val elimN = "elim";
val destN = "dest";

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>swapped\<close> (Scan.succeed swapped)
      "classical swap of introduction rule" #>
    Attrib.setup \<^binding>\<open>dest\<close> (Context_Rules.add safe_dest unsafe_dest Context_Rules.dest_query)
      "declaration of Classical destruction rule" #>
    Attrib.setup \<^binding>\<open>elim\<close> (Context_Rules.add safe_elim unsafe_elim Context_Rules.elim_query)
      "declaration of Classical elimination rule" #>
    Attrib.setup \<^binding>\<open>intro\<close> (Context_Rules.add safe_intro unsafe_intro Context_Rules.intro_query)
      "declaration of Classical introduction rule" #>
    Attrib.setup \<^binding>\<open>rule\<close> (Scan.lift Args.del >> K rule_del)
      "remove declaration of intro/elim/dest rule");



(** proof methods **)

local

fun some_rule_tac ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = Context_Rules.find_rules ctxt false facts goal;
    val {extra_netpair, ...} = rep_claset_of ctxt;
    val rules3 = Context_Rules.find_rules_netpair ctxt true facts goal extra_netpair;
    val rules = rules1 @ rules2 @ rules3 @ rules4;
    val ruleq = Drule.multi_resolves (SOME ctxt) facts rules;
    val _ = Method.trace ctxt rules;
  in
    fn st => Seq.maps (fn rule => resolve_tac ctxt [rule] i st) ruleq
  end)
  THEN_ALL_NEW Goal.norm_hhf_tac ctxt;

in

fun rule_tac ctxt [] facts = some_rule_tac ctxt facts
  | rule_tac ctxt rules facts = Method.rule_tac ctxt rules facts;

fun standard_tac ctxt facts =
  HEADGOAL (some_rule_tac ctxt facts) ORELSE
  Class.standard_intro_classes_tac ctxt facts;

end;


(* automatic methods *)

val cla_modifiers =
 [Args.$$$ destN -- Args.bang_colon >> K (Method.modifier (safe_dest NONE) \<^here>),
  Args.$$$ destN -- Args.colon >> K (Method.modifier (unsafe_dest NONE) \<^here>),
  Args.$$$ elimN -- Args.bang_colon >> K (Method.modifier (safe_elim NONE) \<^here>),
  Args.$$$ elimN -- Args.colon >> K (Method.modifier (unsafe_elim NONE) \<^here>),
  Args.$$$ introN -- Args.bang_colon >> K (Method.modifier (safe_intro NONE) \<^here>),
  Args.$$$ introN -- Args.colon >> K (Method.modifier (unsafe_intro NONE) \<^here>),
  Args.del -- Args.colon >> K (Method.modifier rule_del \<^here>)];

fun cla_method tac = Method.sections cla_modifiers >> K (SIMPLE_METHOD o tac);
fun cla_method' tac = Method.sections cla_modifiers >> K (SIMPLE_METHOD' o tac);



(** method setup **)

val _ =
  Theory.setup
   (Method.setup \<^binding>\<open>standard\<close> (Scan.succeed (METHOD o standard_tac))
      "standard proof step: classical intro/elim rule or class introduction" #>
    Method.setup \<^binding>\<open>rule\<close>
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o rule_tac ctxt rules)))
      "apply some intro/elim rule (potentially classical)" #>
    Method.setup \<^binding>\<open>contradiction\<close>
      (Scan.succeed (fn ctxt => Method.rule ctxt [Data.not_elim, Drule.rotate_prems 1 Data.not_elim]))
      "proof by contradiction" #>
    Method.setup \<^binding>\<open>clarify\<close> (cla_method' (CHANGED_PROP oo clarify_tac))
      "repeatedly apply safe steps" #>
    Method.setup \<^binding>\<open>fast\<close> (cla_method' fast_tac) "classical prover (depth-first)" #>
    Method.setup \<^binding>\<open>slow\<close> (cla_method' slow_tac) "classical prover (slow depth-first)" #>
    Method.setup \<^binding>\<open>best\<close> (cla_method' best_tac) "classical prover (best-first)" #>
    Method.setup \<^binding>\<open>deepen\<close>
      (Scan.lift (Scan.optional Parse.nat 4) --| Method.sections cla_modifiers
        >> (fn n => fn ctxt => SIMPLE_METHOD' (deepen_tac ctxt n)))
      "classical prover (iterative deepening)" #>
    Method.setup \<^binding>\<open>safe\<close> (cla_method (CHANGED_PROP o safe_tac))
      "classical prover (apply safe rules)" #>
    Method.setup \<^binding>\<open>safe_step\<close> (cla_method' safe_step_tac)
      "single classical step (safe rules)" #>
    Method.setup \<^binding>\<open>inst_step\<close> (cla_method' inst_step_tac)
      "single classical step (safe rules, allow instantiations)" #>
    Method.setup \<^binding>\<open>step\<close> (cla_method' step_tac)
      "single classical step (safe and unsafe rules)" #>
    Method.setup \<^binding>\<open>slow_step\<close> (cla_method' slow_step_tac)
      "single classical step (safe and unsafe rules, allow backtracking)" #>
    Method.setup \<^binding>\<open>clarify_step\<close> (cla_method' clarify_step_tac)
      "single classical step (safe rules, without splitting)");


(** outer syntax **)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_claset\<close> "print context of Classical Reasoner"
    (Scan.succeed (Toplevel.keep (print_claset o Toplevel.context_of)));

end;
