(*  Title:      Pure/Isar/context_rules.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Declarations of intro/elim/dest rules in Pure; see
Provers/classical.ML for a more specialized version of the same idea.
*)

signature CONTEXT_RULES =
sig
  type netpair
  type T
  val netpair_bang: Proof.context -> netpair
  val netpair: Proof.context -> netpair
  val netpairs: Proof.context -> netpair list
  val orderlist: ((int * int) * 'a) list -> 'a list
  val orderlist_no_weight: ((int * int) * 'a) list -> 'a list
  val print_global_rules: theory -> unit
  val print_local_rules: Proof.context -> unit
  val addSWrapper: ((int -> tactic) -> int -> tactic) -> theory -> theory
  val addWrapper: ((int -> tactic) -> int -> tactic) -> theory -> theory
  val Swrap: Proof.context -> (int -> tactic) -> int -> tactic
  val wrap: Proof.context -> (int -> tactic) -> int -> tactic
  val intro_bang_global: int option -> theory attribute
  val elim_bang_global: int option -> theory attribute
  val dest_bang_global: int option -> theory attribute
  val intro_global: int option -> theory attribute
  val elim_global: int option -> theory attribute
  val dest_global: int option -> theory attribute
  val intro_query_global: int option -> theory attribute
  val elim_query_global: int option -> theory attribute
  val dest_query_global: int option -> theory attribute
  val rule_del_global: theory attribute
  val intro_bang_local: int option -> Proof.context attribute
  val elim_bang_local: int option -> Proof.context attribute
  val dest_bang_local: int option -> Proof.context attribute
  val intro_local: int option -> Proof.context attribute
  val elim_local: int option -> Proof.context attribute
  val dest_local: int option -> Proof.context attribute
  val intro_query_local: int option -> Proof.context attribute
  val elim_query_local: int option -> Proof.context attribute
  val dest_query_local: int option -> Proof.context attribute
  val rule_del_local: Proof.context attribute
  val setup: (theory -> theory) list
end;

structure ContextRules: CONTEXT_RULES =
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


(* raw data *)

type netpair = ((int * int) * (bool * thm)) Net.net * ((int * int) * (bool * thm)) Net.net;
val empty_netpairs: netpair list = replicate (length rule_indexes) (Net.empty, Net.empty);

datatype T = Rules of
 {next: int,
  rules: (int * ((int * bool) * thm)) list,
  netpairs: netpair list,
  wrappers: (((int -> tactic) -> int -> tactic) * stamp) list *
    (((int -> tactic) -> int -> tactic) * stamp) list};

fun make_rules next rules netpairs wrappers =
  Rules {next = next, rules = rules, netpairs = netpairs, wrappers = wrappers};

fun add_rule (i, b) opt_w th (Rules {next, rules, netpairs, wrappers}) =
  let val w = (case opt_w of Some w => w | None => Tactic.subgoals_of_brl (b, th)) in
    make_rules (next - 1) ((w, ((i, b), th)) :: rules)
      (map_nth_elem i (curry insert_tagged_brl ((w, next), (b, th))) netpairs) wrappers
  end;

fun del_rule th (rs as Rules {next, rules, netpairs, wrappers}) =
  let
    fun eq_th (_, (_, th')) = Thm.eq_thm (th, th');
    fun del b netpair = delete_tagged_brl ((b, th), netpair) handle Net.DELETE => netpair;
  in
    if not (exists eq_th rules) then rs
    else make_rules next (filter_out eq_th rules) (map (del false o del true) netpairs) wrappers
  end;

fun print_rules prt x (Rules {rules, ...}) =
  let
    fun prt_kind (i, b) =
      Pretty.big_list (the (assoc (kind_names, (i, b))) ^ ":")
        (mapfilter (fn (_, (k, th)) => if k = (i, b) then Some (prt x th) else None)
          (sort (int_ord o pairself fst) rules));
  in Pretty.writeln (Pretty.chunks (map prt_kind rule_kinds)) end;


(* theory and proof data *)

structure GlobalRulesArgs =
struct
  val name = "Isar/rule_context";
  type T = T;

  val empty = make_rules ~1 [] empty_netpairs ([], []);
  val copy = I;
  val prep_ext = I;

  fun merge (Rules {rules = rules1, wrappers = (ws1, ws1'), ...},
      Rules {rules = rules2, wrappers = (ws2, ws2'), ...}) =
    let
      val wrappers = (gen_merge_lists' eq_snd ws1 ws2, gen_merge_lists' eq_snd ws1' ws2');
      val rules = gen_merge_lists' (fn ((_, (k1, th1)), (_, (k2, th2))) =>
          k1 = k2 andalso Thm.eq_thm (th1, th2)) rules1 rules2;
      val next = ~ (length rules);
      val netpairs = foldl (fn (nps, (n, (w, ((i, b), th)))) =>
          map_nth_elem i (curry insert_tagged_brl ((w, n), (b, th))) nps)
        (empty_netpairs, next upto ~1 ~~ rules);
    in make_rules (next - 1) rules netpairs wrappers end;

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


(* access data *)

fun netpairs ctxt = let val Rules {netpairs, ...} = LocalRules.get ctxt in netpairs end;
val netpair_bang = hd o netpairs;
val netpair = hd o tl o netpairs;


fun untaglist [] = []
  | untaglist [(k : int * int, x)] = [x]
  | untaglist ((k, x) :: (rest as (k', x') :: _)) =
      if k = k' then untaglist rest
      else x :: untaglist rest;

fun orderlist brls = untaglist (sort (prod_ord int_ord int_ord o pairself fst) brls);
fun orderlist_no_weight brls = untaglist (sort (int_ord o pairself (snd o fst)) brls);


fun gen_add_wrapper upd w = GlobalRules.map (fn (rs as Rules {next, rules, netpairs, wrappers}) =>
  make_rules next rules netpairs (upd (fn ws => (w, stamp ()) :: ws) wrappers));

val addSWrapper = gen_add_wrapper Library.apfst;
val addWrapper = gen_add_wrapper Library.apsnd;


fun gen_wrap which ctxt =
  let val Rules {wrappers, ...} = LocalRules.get ctxt
  in fn tac => foldr (fn ((w, _), t) => w t) (which wrappers, tac) end;

val Swrap = gen_wrap #1;
val wrap = gen_wrap #2;



(** attributes **)

(* add and del rules *)

local

fun del map_data (x, th) =
  (map_data (del_rule th o del_rule (Tactic.make_elim th)) x, th);

fun add k view map_data opt_w =
  (fn (x, th) => (map_data (add_rule k opt_w th) x, th)) o del map_data;

in

val intro_bang_global  = add intro_bangK I GlobalRules.map;
val elim_bang_global   = add elim_bangK I GlobalRules.map;
val dest_bang_global   = add elim_bangK Tactic.make_elim GlobalRules.map;
val intro_global       = add introK I GlobalRules.map;
val elim_global        = add elimK I GlobalRules.map;
val dest_global        = add elimK Tactic.make_elim GlobalRules.map;
val intro_query_global = add intro_queryK I GlobalRules.map;
val elim_query_global  = add elim_queryK I GlobalRules.map;
val dest_query_global  = add elim_queryK Tactic.make_elim GlobalRules.map;
val rule_del_global    = del GlobalRules.map;

val intro_bang_local   = add intro_bangK I LocalRules.map;
val elim_bang_local    = add elim_bangK I LocalRules.map;
val dest_bang_local    = add elim_bangK Tactic.make_elim LocalRules.map;
val intro_local        = add introK I LocalRules.map;
val elim_local         = add elimK I LocalRules.map;
val dest_local         = add elimK Tactic.make_elim LocalRules.map;
val intro_query_local  = add intro_queryK I LocalRules.map;
val elim_query_local   = add elim_queryK I LocalRules.map;
val dest_query_local   = add elim_queryK Tactic.make_elim LocalRules.map;
val rule_del_local     = del LocalRules.map;

end;


(* concrete syntax *)

fun add_args a b c x = Attrib.syntax
  (Scan.lift (Scan.option Args.nat --
    (Args.bang >> K a || Args.query >> K c || Scan.succeed b) >> op |>)) x;

fun del_args att = Attrib.syntax (Scan.lift Args.del >> K att);


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
    "declaration of destruction rule"),
  ("rule", (del_args rule_del_global, del_args rule_del_local),
    "remove declaration of intro/elim/dest rule")];



(** theory setup **)

val setup =
 [GlobalRules.init, LocalRules.init, Attrib.add_attributes rule_atts];


end;
