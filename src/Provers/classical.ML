(*  Title:      Provers/classical.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Theorem prover for classical reasoning, including predicate calculus, set
theory, etc.

Rules must be classified as intro, elim, safe, unsafe.

A rule is unsafe unless it can be applied blindly without harmful results.
For a rule to be safe, its premises and conclusion should be logically
equivalent.  There should be no variables in the premises that are not in
the conclusion.

Rules are maintained in "canonical reverse order", meaning that later
declarations take precedence.
*)

(*higher precedence than := facilitates use of references*)
infix 4 addSIs addSEs addSDs addIs addEs addDs delrules
  addSWrapper delSWrapper addWrapper delWrapper
  addSbefore addSafter addbefore addafter
  addD2 addE2 addSD2 addSE2;

signature CLASSICAL_DATA =
sig
  val imp_elim: thm  (* P \<longrightarrow> Q \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R *)
  val not_elim: thm  (* \<not> P \<Longrightarrow> P \<Longrightarrow> R *)
  val swap: thm  (* \<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R *)
  val classical: thm  (* (\<not> P \<Longrightarrow> P) \<Longrightarrow> P *)
  val sizef: thm -> int  (*size function for BEST_FIRST, typically size_of_thm*)
  val hyp_subst_tacs: (Proof.context -> int -> tactic) list
    (*optional tactics for substitution in the hypotheses; assumed to be safe!*)
end;

signature BASIC_CLASSICAL =
sig
  type wrapper = (int -> tactic) -> int -> tactic
  type claset
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
  val swap_res_tac: Proof.context -> thm list -> int -> tactic
  val inst_step_tac: Proof.context -> int -> tactic
  val inst0_step_tac: Proof.context -> int -> tactic
  val instp_step_tac: Proof.context -> int -> tactic

  val print_claset: Proof.context -> unit
end;

signature CLASSICAL =
sig
  include BASIC_CLASSICAL
  val classical_rule: Proof.context -> thm -> thm
  type rl = thm * thm option
  type info = {rl: rl, dup_rl: rl, plain: thm}
  type decl = info Bires.decl
  type decls = info Bires.decls
  val safe0_netpair_of: Proof.context -> Bires.netpair
  val safep_netpair_of: Proof.context -> Bires.netpair
  val unsafe_netpair_of: Proof.context -> Bires.netpair
  val dup_netpair_of: Proof.context -> Bires.netpair
  val extra_netpair_of: Proof.context -> Bires.netpair
  val dest_decls: Proof.context -> ((thm * decl) -> bool) -> (thm * decl) list
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

(** Support for classical reasoning **)

(* classical elimination rules *)

(*Classical reasoning requires stronger elimination rules.  For
  instance, make_elim of Pure transforms the HOL rule injD into

    \<lbrakk>inj f; f x = f y; x = y \<Longrightarrow> PROP W\<rbrakk> \<Longrightarrow> PROP W

  Such rules can cause fast_tac to fail and blast_tac to report "PROOF
  FAILED"; classical_rule will strengthen this to

    \<lbrakk>inj f; \<not> W \<Longrightarrow> f x = f y; x = y \<Longrightarrow> W\<rbrakk> \<Longrightarrow> W
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


(* flatten nested meta connectives in prems *)

fun flat_rule ctxt =
  Conv.fconv_rule (Conv.prems_conv ~1 (Object_Logic.atomize_prems ctxt));


(* Useful tactics for classical reasoning *)

(*Prove goal that assumes both P and \<not> P.
  No backtracking if it finds an equal assumption.  Perhaps should call
  ematch_tac instead of eresolve_tac, but then cannot prove ZF/cantor.*)
fun contr_tac ctxt =
  eresolve_tac ctxt [Data.not_elim] THEN' (eq_assume_tac ORELSE' assume_tac ctxt);

(*Finds P \<longrightarrow> Q and P in the assumptions, replaces implication by Q.
  Could do the same thing for P \<longleftrightarrow> Q and P.*)
fun mp_tac ctxt i =
  eresolve_tac ctxt [Data.not_elim, Data.imp_elim] i THEN assume_tac ctxt i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac ctxt i = ematch_tac ctxt [Data.not_elim, Data.imp_elim] i THEN eq_assume_tac i;

(*Creates rules to eliminate \<not> A, from rules to introduce A*)
fun maybe_swap_rule th =
  (case [th] RLN (2, [Data.swap]) of
    [] => NONE
  | [res] => SOME res
  | _ => raise THM ("RSN: multiple unifiers", 2, [th, Data.swap]));

fun swap_rule intr = intr RSN (2, Data.swap);
val swapped = Thm.rule_attribute [] (K swap_rule);

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac ctxt rls =
  let
    fun addrl rl brls = (false, rl) :: (true, swap_rule rl) :: brls;
  in
    assume_tac ctxt ORELSE'
    contr_tac ctxt ORELSE'
    biresolve_tac ctxt (fold_rev (addrl o Thm.transfer' ctxt) rls [])
  end;

(*Duplication of unsafe rules, for complete provers*)
fun dup_intr th = zero_var_indexes (th RS Data.classical);

fun dup_elim ctxt th =
  let val rl = (th RSN (2, revcut_rl)) |> Thm.assumption (SOME ctxt) 2 |> Seq.hd;
  in rule_by_tactic ctxt (TRYALL (eresolve_tac ctxt [revcut_rl])) rl end;



(** Classical rule sets **)

type rl = thm * thm option;  (*internal form, with possibly swapped version*)
type info = {rl: rl, dup_rl: rl, plain: thm};
type rule = thm * info;  (*external form, internal forms*)

type decl = info Bires.decl;
type decls = info Bires.decls;

fun maybe_swapped_rl th : rl = (th, maybe_swap_rule th);
fun no_swapped_rl th : rl = (th, NONE);

fun make_info rl dup_rl plain : info = {rl = rl, dup_rl = dup_rl, plain = plain};
fun make_info1 rl plain : info = make_info rl rl plain;

type wrapper = (int -> tactic) -> int -> tactic;

datatype claset =
  CS of
   {decls: decls,  (*rule declarations in canonical order*)
    swrappers: (string * (Proof.context -> wrapper)) list,  (*for transforming safe_step_tac*)
    uwrappers: (string * (Proof.context -> wrapper)) list,  (*for transforming step_tac*)
    safe0_netpair: Bires.netpair,  (*nets for trivial cases*)
    safep_netpair: Bires.netpair,  (*nets for >0 subgoals*)
    unsafe_netpair: Bires.netpair,  (*nets for unsafe rules*)
    dup_netpair: Bires.netpair,  (*nets for duplication*)
    extra_netpair: Bires.netpair};  (*nets for extra rules*)

val empty_cs =
  CS
   {decls = Bires.empty_decls,
    swrappers = [],
    uwrappers = [],
    safe0_netpair = Bires.empty_netpair,
    safep_netpair = Bires.empty_netpair,
    unsafe_netpair = Bires.empty_netpair,
    dup_netpair = Bires.empty_netpair,
    extra_netpair = Bires.empty_netpair};

fun rep_cs (CS args) = args;


(* netpair primitives to insert / delete rules *)

fun insert_brl i brl =
  Bires.insert_tagged_rule ({weight = Bires.subgoals_of brl, index = i}, brl);

fun insert_rl kind k ((th, swapped): rl) =
  insert_brl (2 * k + 1) (Bires.kind_rule kind th) #>
  (case swapped of NONE => I | SOME th' => insert_brl (2 * k) (true, th'));

fun delete_rl k ((th, swapped): rl) =
  Bires.delete_tagged_rule (2 * k + 1, th) #>
  (case swapped of NONE => I | SOME th' => Bires.delete_tagged_rule (2 * k, th'));

fun insert_plain_rule ({kind, tag, info = {plain = th, ...}}: decl) =
  Bires.insert_tagged_rule (tag, (Bires.kind_rule kind th));

fun delete_plain_rule ({tag = {index, ...}, info = {plain = th, ...}, ...}: decl) =
  Bires.delete_tagged_rule (index, th);


(* erros and warnings *)

fun err_thm ctxt msg th = error (msg () ^ "\n" ^ Thm.string_of_thm ctxt th);

fun err_thm_illformed ctxt kind th =
  err_thm ctxt (fn () => "Ill-formed " ^ Bires.kind_name kind) th;

fun init_decl kind opt_weight info : decl =
  let val weight = the_default (Bires.kind_index kind) opt_weight
  in {kind = kind, tag = Bires.weight_tag weight, info = info} end;

fun warn_thm ctxt msg th =
  if Context_Position.is_really_visible ctxt
  then warning (msg () ^ "\n" ^ Thm.string_of_thm ctxt th) else ();

fun warn_kind ctxt prefix th kind =
  if Context_Position.is_really_visible ctxt then
    warn_thm ctxt (fn () => prefix ^ " " ^ Bires.kind_description kind) th
  else ();

fun warn_other_kinds ctxt decls th =
  if Context_Position.is_really_visible ctxt then
    (case Bires.get_decls decls th of
      [] => ()
    | ds =>
        Bires.kind_domain
        |> filter (member (op =) (map #kind ds))
        |> List.app (warn_kind ctxt "Rule already declared as" th))
  else ();


(* extend and merge rules *)

local

type netpairs = (Bires.netpair * Bires.netpair) * (Bires.netpair * Bires.netpair);

fun add_safe_rule (decl: decl) (netpairs: netpairs) =
  let
    val {kind, tag = {index, ...}, info = {rl, ...}} = decl;
    val no_subgoals = Bires.no_subgoals (Bires.kind_rule kind (#1 rl));
  in (apfst o (if no_subgoals then apfst else apsnd)) (insert_rl kind index rl) netpairs end;

fun add_unsafe_rule (decl: decl) ((safe_netpairs, (unsafe_netpair, dup_netpair)): netpairs) =
  let
    val {kind, tag = {index, ...}, info = {rl, dup_rl, ...}} = decl;
    val unsafe_netpair' = insert_rl kind index rl unsafe_netpair;
    val dup_netpair' = insert_rl kind index dup_rl dup_netpair;
  in (safe_netpairs, (unsafe_netpair', dup_netpair')) end;

fun add_rule (decl as {kind, ...}: decl) =
  if Bires.kind_safe kind then add_safe_rule decl
  else if Bires.kind_unsafe kind then add_unsafe_rule decl
  else raise Fail "Bad rule kind";


fun trim_context_rl (th1, opt_th2) =
  (Thm.trim_context th1, Option.map Thm.trim_context opt_th2);

fun trim_context_info {rl, dup_rl, plain} : info =
  {rl = trim_context_rl rl, dup_rl = trim_context_rl dup_rl, plain = Thm.trim_context plain};

fun ext_info ctxt kind th =
  if kind = Bires.intro_bang_kind then
    make_info1 (maybe_swapped_rl (flat_rule ctxt th)) th
  else if kind = Bires.elim_bang_kind orelse kind = Bires.dest_bang_kind then
    let
      val _ = Thm.no_prems th andalso err_thm_illformed ctxt kind th;
      val elim = Bires.kind_make_elim kind th;
    in make_info1 (no_swapped_rl (classical_rule ctxt (flat_rule ctxt elim))) elim end
  else if kind = Bires.intro_kind then
    let
      val th' = flat_rule ctxt th;
      val dup_th' = dup_intr th' handle THM _ => err_thm_illformed ctxt kind th;
    in make_info (maybe_swapped_rl th') (maybe_swapped_rl dup_th') th end
  else if kind = Bires.elim_kind orelse kind = Bires.dest_kind then
    let
      val _ = Thm.no_prems th andalso err_thm_illformed ctxt kind th;
      val elim = Bires.kind_make_elim kind th;
      val th' = classical_rule ctxt (flat_rule ctxt elim);
      val dup_th' = dup_elim ctxt th' handle THM _ => err_thm_illformed ctxt kind th;
    in make_info (no_swapped_rl th') (no_swapped_rl dup_th') elim end
  else raise Fail "Bad rule kind";

in

fun extend_rules ctxt kind opt_weight th cs =
  let
    val th' = Thm.trim_context th;
    val decl' = init_decl kind opt_weight (trim_context_info (ext_info ctxt kind th));
    val CS {decls, swrappers, uwrappers, safe0_netpair, safep_netpair,
      unsafe_netpair, dup_netpair, extra_netpair} = cs;
  in
    (case Bires.extend_decls (th', decl') decls of
      (NONE, _) => (warn_kind ctxt "Ignoring duplicate" th kind; cs)
    | (SOME new_decl, decls') =>
        let
          val _ = warn_other_kinds ctxt decls th;
          val ((safe0_netpair', safep_netpair'), (unsafe_netpair', dup_netpair')) =
            add_rule new_decl ((safe0_netpair, safep_netpair), (unsafe_netpair, dup_netpair));
          val extra_netpair' = insert_plain_rule new_decl extra_netpair;
        in
          CS {
            decls = decls',
            swrappers = swrappers,
            uwrappers = uwrappers,
            safe0_netpair = safe0_netpair',
            safep_netpair = safep_netpair',
            unsafe_netpair = unsafe_netpair',
            dup_netpair = dup_netpair',
            extra_netpair = extra_netpair'}
        end)
  end;

fun merge_cs (cs, cs2) =
  if pointer_eq (cs, cs2) then cs
  else
    let
      val CS {decls, swrappers, uwrappers, safe0_netpair, safep_netpair,
        unsafe_netpair, dup_netpair, extra_netpair} = cs;
      val CS {decls = decls2, swrappers = swrappers2, uwrappers = uwrappers2, ...} = cs2;

      val (new_decls, decls') = Bires.merge_decls (decls, decls2);
      val ((safe0_netpair', safep_netpair'), (unsafe_netpair', dup_netpair')) =
        fold add_rule new_decls ((safe0_netpair, safep_netpair), (unsafe_netpair, dup_netpair));
      val extra_netpair' = fold insert_plain_rule new_decls extra_netpair;
    in
      CS {
        decls = decls',
        swrappers = AList.merge (op =) (K true) (swrappers, swrappers2),
        uwrappers = AList.merge (op =) (K true) (uwrappers, uwrappers2),
        safe0_netpair = safe0_netpair',
        safep_netpair = safep_netpair',
        unsafe_netpair = unsafe_netpair',
        dup_netpair = dup_netpair',
        extra_netpair = extra_netpair'}
    end;

end;


(* delete rules *)

fun delrule ctxt warn th cs =
  let
    val CS {decls, swrappers, uwrappers,
      safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair} = cs;
    val (old_decls, decls') = Bires.remove_decls th decls;
    val _ =
      if Bires.has_decls decls (Tactic.make_elim th) then
        warn_thm ctxt
          (fn () => "Not deleting elim format --- need to to declare proper dest rule") th
      else ();
  in
    if null old_decls then
      (if warn then warn_thm ctxt (fn () => "Undeclared classical rule") th else (); cs)
    else
      let
        fun del which ({tag = {index, ...}, info, ...}: decl) = delete_rl index (which info);
        val safe0_netpair' = fold (del #rl) old_decls safe0_netpair;
        val safep_netpair' = fold (del #rl) old_decls safep_netpair;
        val unsafe_netpair' = fold (del #rl) old_decls unsafe_netpair;
        val dup_netpair' = fold (del #dup_rl) old_decls dup_netpair;
        val extra_netpair' = fold delete_plain_rule old_decls extra_netpair;
      in
        CS {
          decls = decls',
          swrappers = swrappers,
          uwrappers = uwrappers,
          safe0_netpair = safe0_netpair',
          safep_netpair = safep_netpair',
          unsafe_netpair = unsafe_netpair',
          dup_netpair = dup_netpair',
          extra_netpair = extra_netpair'}
      end
  end;


(* Claset context data *)

structure Claset = Generic_Data
(
  type T = claset;
  val empty = empty_cs;
  val merge = merge_cs;
);

val claset_of = Claset.get o Context.Proof;
val rep_claset_of = rep_cs o claset_of;

val dest_decls = Bires.dest_decls o #decls o rep_claset_of;

val safe0_netpair_of = #safe0_netpair o rep_claset_of;
val safep_netpair_of = #safep_netpair o rep_claset_of;
val unsafe_netpair_of = #unsafe_netpair o rep_claset_of;
val dup_netpair_of = #dup_netpair o rep_claset_of;
val extra_netpair_of = #extra_netpair o rep_claset_of;

val get_cs = Claset.get;
val map_cs = Claset.map;

fun map_theory_claset f thy =
  let
    val ctxt' = f (Proof_Context.init_global thy);
    val thy' = Proof_Context.theory_of ctxt';
  in Context.theory_map (Claset.map (K (claset_of ctxt'))) thy' end;

fun map_claset f = Context.proof_map (map_cs f);
fun put_claset cs = map_claset (K cs);


(* old-style ML declarations *)

fun ml_decl kind (ctxt, ths) =
  map_claset (fold_rev (extend_rules ctxt kind NONE) ths) ctxt;

val op addSIs = ml_decl Bires.intro_bang_kind;
val op addSEs = ml_decl Bires.elim_bang_kind;
val op addSDs = ml_decl Bires.dest_bang_kind;
val op addIs = ml_decl Bires.intro_kind;
val op addEs = ml_decl Bires.elim_kind;
val op addDs = ml_decl Bires.dest_kind;

fun ctxt delrules ths = map_claset (fold_rev (delrule ctxt true) ths) ctxt;



(** Modifying the wrapper tacticals **)

fun map_swrappers f
  (CS {decls, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  CS {decls = decls, swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    unsafe_netpair = unsafe_netpair, dup_netpair = dup_netpair, extra_netpair = extra_netpair};

fun map_uwrappers f
  (CS {decls, swrappers, uwrappers,
    safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair, extra_netpair}) =
  CS {decls = decls, swrappers = swrappers, uwrappers = f uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    unsafe_netpair = unsafe_netpair, dup_netpair = dup_netpair, extra_netpair = extra_netpair};

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

(*compose a safe tactic alternatively before/after safe_step_tac*)
fun ctxt addSbefore (name, tac1) =
  ctxt addSWrapper (name, fn ctxt => fn tac2 => tac1 ctxt ORELSE' tac2);
fun ctxt addSafter (name, tac2) =
  ctxt addSWrapper (name, fn ctxt => fn tac1 => tac1 ORELSE' tac2 ctxt);

(*compose a tactic alternatively before/after the step tactic*)
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



(** Simple tactics for theorem proving **)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun safe_step_tac ctxt =
  appSWrappers ctxt
    (FIRST'
     [eq_assume_tac,
      eq_mp_tac ctxt,
      Bires.bimatch_from_nets_tac ctxt (safe0_netpair_of ctxt),
      FIRST' (map (fn tac => tac ctxt) Data.hyp_subst_tacs),
      Bires.bimatch_from_nets_tac ctxt (safep_netpair_of ctxt)]);

(*Repeatedly attack a subgoal using safe inferences -- it's deterministic!*)
fun safe_steps_tac ctxt =
  REPEAT_DETERM1 o (fn i => COND (has_fewer_prems i) no_tac (safe_step_tac ctxt i));

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun safe_tac ctxt = REPEAT_DETERM1 (FIRSTGOAL (safe_steps_tac ctxt));



(** Clarify_tac: do safe steps without causing branching **)

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
  appSWrappers ctxt
   (FIRST'
     [eq_assume_contr_tac ctxt,
      Bires.bimatch_from_nets_tac ctxt (safe0_netpair_of ctxt),
      FIRST' (map (fn tac => tac ctxt) Data.hyp_subst_tacs),
      n_bimatch_from_nets_tac ctxt 1 (safep_netpair_of ctxt),
      bimatch2_tac ctxt (safep_netpair_of ctxt)]);

fun clarify_tac ctxt = SELECT_GOAL (REPEAT_DETERM (clarify_step_tac ctxt 1));



(** Unsafe steps instantiate variables or lose information **)

(*Backtracking is allowed among the various these unsafe ways of
  proving a subgoal.  *)
fun inst0_step_tac ctxt =
  assume_tac ctxt APPEND'
  contr_tac ctxt APPEND'
  Bires.biresolve_from_nets_tac ctxt (safe0_netpair_of ctxt);

(*These unsafe steps could generate more subgoals.*)
fun instp_step_tac ctxt =
  Bires.biresolve_from_nets_tac ctxt (safep_netpair_of ctxt);

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac ctxt = inst0_step_tac ctxt APPEND' instp_step_tac ctxt;

fun unsafe_step_tac ctxt =
  Bires.biresolve_from_nets_tac ctxt (unsafe_netpair_of ctxt);

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac ctxt i =
  safe_tac ctxt ORELSE appWrappers ctxt (inst_step_tac ctxt ORELSE' unsafe_step_tac ctxt) i;

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac ctxt i =
  safe_tac ctxt ORELSE appWrappers ctxt (inst_step_tac ctxt APPEND' unsafe_step_tac ctxt) i;


(** The following tactics all fail unless they solve one goal **)

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


(** ASTAR with weight weight_ASTAR, by Norbert Voelker **)

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


(** Complete tactic, loosely based upon LeanTaP.  This tactic is the outcome
  of much experimentation!  Changing APPEND to ORELSE below would prove
  easy theorems faster, but loses completeness -- and many of the harder
  theorems such as 43. **)

(*Non-deterministic!  Could always expand the first unsafe connective.
  That's hard to implement and did not perform better in experiments, due to
  greater search depth required.*)
fun dup_step_tac ctxt =
  Bires.biresolve_from_nets_tac ctxt (dup_netpair_of ctxt);

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



(** attributes **)

(* declarations *)

fun attrib kind w =
  Thm.declaration_attribute (fn th => fn context =>
    map_cs (extend_rules (Context.proof_of context) kind w th) context);

val safe_intro = attrib Bires.intro_bang_kind;
val safe_elim = attrib Bires.elim_bang_kind;
val safe_dest = attrib Bires.dest_bang_kind;
val unsafe_intro = attrib Bires.intro_kind;
val unsafe_elim = attrib Bires.elim_kind;
val unsafe_dest = attrib Bires.dest_kind;

val rule_del =
  Thm.declaration_attribute (fn th => fn context =>
    context
    |> map_cs (delrule (Context.proof_of context) (not (Context_Rules.declared_rule context th)) th)
    |> Thm.attribute_declaration Context_Rules.rule_del th);


(* concrete syntax *)

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
      "remove declaration of Classical intro/elim/dest rule");



(** proof methods **)

local

fun some_rule_tac ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = Context_Rules.find_rules ctxt false facts goal;
    val rules3 = Context_Rules.find_rules_netpair ctxt true facts goal (extra_netpair_of ctxt);
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


(* method setup *)

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



(** outer syntax commands **)

fun print_claset ctxt =
  let
    val {decls, swrappers, uwrappers, ...} = rep_claset_of ctxt;
    val prt_wrappers =
     [Pretty.strs ("safe wrappers:" :: map #1 swrappers),
      Pretty.strs ("unsafe wrappers:" :: map #1 uwrappers)];
  in Pretty.writeln (Pretty.chunks (Bires.pretty_decls ctxt decls @ prt_wrappers)) end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_claset\<close> "print context of Classical Reasoner"
    (Scan.succeed (Toplevel.keep (print_claset o Toplevel.context_of)));

end;
