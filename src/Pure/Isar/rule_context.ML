(*  Title:      Pure/Isar/rule_context.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Declarations of intro/elim/dest rules in Pure; see
Provers/classical.ML for a more specialized version.

TODO:
  - del rules;
  - tactics;
  - add/del ML interface (?);
*)

signature RULE_CONTEXT =
sig
  type T
  val empty_rules: T
  val print_global_rules: theory -> unit
  val print_local_rules: Proof.context -> unit
  val intro_bang_global: int option -> theory attribute
  val elim_bang_global: int option -> theory attribute
  val dest_bang_global: int option -> theory attribute
  val intro_global: int option -> theory attribute
  val elim_global: int option -> theory attribute
  val dest_global: int option -> theory attribute
  val intro_query_global: int option -> theory attribute
  val elim_query_global: int option -> theory attribute
  val dest_query_global: int option -> theory attribute
  val intro_bang_local: int option -> Proof.context attribute
  val elim_bang_local: int option -> Proof.context attribute
  val dest_bang_local: int option -> Proof.context attribute
  val intro_local: int option -> Proof.context attribute
  val elim_local: int option -> Proof.context attribute
  val dest_local: int option -> Proof.context attribute
  val intro_query_local: int option -> Proof.context attribute
  val elim_query_local: int option -> Proof.context attribute
  val dest_query_local: int option -> Proof.context attribute
  val setup: (theory -> theory) list
end;

structure RuleContext: RULE_CONTEXT =
struct


(** rule declaration contexts **)

(* rule kinds *)

val intro_bangK = (0, false);
val elim_bangK = (0, true);
val introK = (1, false);
val elimK = (1, true);
val intro_queryK = (2, false);
val elim_queryK = (2, true);

val kind_names =
 [(intro_bangK, "safe introduction rules (intro!)"),
  (elim_bangK, "safe elimination rules (elim!)"),
  (introK, "introduction rules (intro)"),
  (elimK, "elimination rules (elim)"),
  (intro_queryK, "extra introduction rules (intro?)"),
  (elim_queryK, "extra elimination rules (elim?)")];

val rule_kinds = map #1 kind_names;
val rule_indexes = distinct (map #1 rule_kinds);


(* netpairs *)

type net = ((int * int) * (bool * thm)) Net.net;

val empty_netpairs = replicate (length rule_indexes) (Net.empty: net, Net.empty: net);

fun make_netpairs rules =
  let
    fun add (netpairs, (n, (w, ((i, b), th)))) =
      map_nth_elem i (curry insert_tagged_brl ((w, n), (b, th))) netpairs;
    val next = ~ (length rules);
  in (next - 1, foldl add (empty_netpairs, next upto ~1 ~~ rules)) end;


(* rules *)

datatype T = Rules of
 {next: int,
  rules: (int * ((int * bool) * thm)) list,
  netpairs: (net * net) list,
  wrappers: ((bool * ((int -> tactic) -> int -> tactic)) * stamp) list};

val empty_rules = Rules {next = ~1, rules = [], netpairs = empty_netpairs, wrappers = []};

fun add_rule (i, b) opt_w th (Rules {next, rules, netpairs, wrappers}) =
  let val w = (case opt_w of Some w => w | None => Tactic.subgoals_of_brl (b, th)) in
    Rules {next = next - 1,
      rules = (w, ((i, b), th)) :: rules,
      netpairs = map_nth_elem i (curry insert_tagged_brl ((w, next), (b, th))) netpairs,
      wrappers = wrappers}
  end;

fun print_rules prt x (Rules {rules, ...}) =
  let
    fun prt_kind (i, b) =
      Pretty.big_list (the (assoc (kind_names, (i, b))) ^ ":")
        (mapfilter (fn (_, (k, th)) => if k = (i, b) then Some (prt x th) else None) rules);
  in Pretty.writeln (Pretty.chunks (map prt_kind rule_kinds)) end;


(* theory and proof data *)

structure GlobalRulesArgs =
struct
  val name = "Isar/rule_context";
  type T = T;

  val empty = empty_rules;
  val copy = I;
  val prep_ext = I;

  fun merge (Rules {rules = rules1, wrappers = wrappers1, ...},
      Rules {rules = rules2, wrappers = wrappers2, ...}) =
    let
      val wrappers = gen_merge_lists' eq_snd wrappers1 wrappers2;
      val rules = gen_merge_lists' (fn ((_, (k1, th1)), (_, (k2, th2))) =>
          k1 = k2 andalso Thm.eq_thm (th1, th2)) rules1 rules2;
      val next = ~ (length rules);
      val netpairs = foldl (fn (nps, (n, (w, ((i, b), th)))) =>
          map_nth_elem i (curry insert_tagged_brl ((w, n), (b, th))) nps)
        (empty_netpairs, next upto ~1 ~~ rules);
    in Rules {next = next - 1, rules = rules, netpairs = netpairs, wrappers = wrappers} end;

  val print = print_rules Display.pretty_thm_sg;
end;

structure GlobalRules = TheoryDataFun(GlobalRulesArgs);
val print_global_rules = GlobalRules.print;

structure LocalRulesArgs =
struct
  val name = GlobalRulesArgs.name;
  type T = GlobalRulesArgs.T;
  val init = GlobalRules.get;
  val print = print_rules ProofContext.pretty_thm;
end;

structure LocalRules = ProofDataFun(LocalRulesArgs);
val print_local_rules = LocalRules.print;



(** attributes **)

(* add rules *)

local

fun mk_att k view map_data opt_w (x, th) = (map_data (add_rule k opt_w th) x, th);

in

val intro_bang_global  = mk_att intro_bangK I GlobalRules.map;
val elim_bang_global   = mk_att elim_bangK I GlobalRules.map;
val dest_bang_global   = mk_att elim_bangK Tactic.make_elim GlobalRules.map;
val intro_global       = mk_att introK I GlobalRules.map;
val elim_global        = mk_att elimK I GlobalRules.map;
val dest_global        = mk_att elimK Tactic.make_elim GlobalRules.map;
val intro_query_global = mk_att intro_queryK I GlobalRules.map;
val elim_query_global  = mk_att elim_queryK I GlobalRules.map;
val dest_query_global  = mk_att elim_queryK Tactic.make_elim GlobalRules.map;

val intro_bang_local   = mk_att intro_bangK I LocalRules.map;
val elim_bang_local    = mk_att elim_bangK I LocalRules.map;
val dest_bang_local    = mk_att elim_bangK Tactic.make_elim LocalRules.map;
val intro_local        = mk_att introK I LocalRules.map;
val elim_local         = mk_att elimK I LocalRules.map;
val dest_local         = mk_att elimK Tactic.make_elim LocalRules.map;
val intro_query_local  = mk_att intro_queryK I LocalRules.map;
val elim_query_local   = mk_att elim_queryK I LocalRules.map;
val dest_query_local   = mk_att elim_queryK Tactic.make_elim LocalRules.map;

end;


(* concrete syntax *)

fun add_args a b c x = Attrib.syntax
  (Scan.lift (Scan.option (Args.bracks Args.nat) --
    (Args.bang >> K a || Args.query >> K c || Scan.succeed b) >> op |>)) x;

val rule_atts =
 [("intro",
   (add_args intro_bang_global intro_global intro_query_global,
    add_args intro_bang_local intro_local intro_query_local),
    "declaration of introduction rule"),
  ("elim",
   (add_args elim_bang_global elim_global elim_query_global,
    add_args elim_bang_local elim_local elim_query_local),
    "declaration of elimination rule"),
  ("dest",
   (add_args dest_bang_global dest_global dest_query_global,
    add_args dest_bang_local dest_local dest_query_local),
    "declaration of destruction rule")];



(** theory setup **)

val setup =
 [GlobalRules.init, LocalRules.init
  (*FIXME Attrib.add_attributes rule_atts*)];


end;
