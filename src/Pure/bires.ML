(*  Title:      Pure/bires.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Biresolution and resolution using nets.
*)

signature BIRES =
sig
  type rule = bool * thm
  val subgoals_of: rule -> int
  val subgoals_ord: rule ord
  val no_subgoals: rule -> bool

  type tag = {weight: int, index: int}
  val tag_weight_ord: tag ord
  val tag_index_ord: tag ord
  val tag_ord: tag ord
  val weighted_tag_ord: bool -> tag ord
  val tag_order: (tag * 'a) list -> 'a list
  val weight_tag: int -> tag

  eqtype kind
  val intro_bang_kind: kind
  val elim_bang_kind: kind
  val intro_kind: kind
  val elim_kind: kind
  val intro_query_kind: kind
  val elim_query_kind: kind
  val kind_index: kind -> int
  val kind_elim: kind -> bool
  val kind_domain: kind list
  val kind_values: 'a -> 'a list
  val kind_map: kind -> ('a -> 'a) -> 'a list -> 'a list
  val kind_rule: kind -> thm -> rule
  val kind_title: kind -> string

  type 'a decl = {kind: kind, tag: tag, info: 'a}
  val decl_ord: 'a decl ord
  type 'a decls
  val has_decls: 'a decls -> thm -> bool
  val list_decls: (thm * 'a decl -> bool) -> 'a decls -> (thm * 'a decl) list
  val pretty_decls: Proof.context -> kind list -> 'a decls -> Pretty.T list
  val merge_decls: 'a decls * 'a decls -> (thm * 'a decl) list * 'a decls
  val extend_decls: thm * 'a decl -> 'a decls -> ((thm * 'a decl) * 'a decls) option
  val remove_decls: thm -> 'a decls -> 'a decls option
  val empty_decls: 'a decls

  type netpair = (tag * rule) Net.net * (tag * rule) Net.net
  val empty_netpair: netpair
  val insert_tagged_rule: tag * rule -> netpair -> netpair
  val insert_tagged_rules: (tag * rule) list -> netpair -> netpair
  val delete_tagged_rule: rule -> netpair -> netpair
  val delete_tagged_rules: rule list -> netpair -> netpair
  val insert_rule: thm * 'a decl -> netpair -> netpair
  val remove_rule: thm -> netpair -> netpair

  val biresolution_from_nets_tac: Proof.context -> tag ord -> (rule -> bool) option ->
    bool -> netpair -> int -> tactic
  val biresolve_from_nets_tac: Proof.context -> netpair -> int -> tactic
  val bimatch_from_nets_tac: Proof.context -> netpair -> int -> tactic

  type net = (int * thm) Net.net
  val build_net: thm list -> net
  val filt_resolve_from_net_tac: Proof.context -> int -> net -> int -> tactic
  val resolve_from_net_tac: Proof.context -> net -> int -> tactic
  val match_from_net_tac: Proof.context -> net -> int -> tactic
end

structure Bires: BIRES =
struct

(** Rule kinds and declarations **)

(* type rule *)

type rule = bool * thm;  (*see Thm.biresolution*)

fun subgoals_of (true, thm) = Thm.nprems_of thm - 1
  | subgoals_of (false, thm) = Thm.nprems_of thm;

val subgoals_ord = int_ord o apply2 subgoals_of;

fun no_subgoals (true, thm) = Thm.one_prem thm
  | no_subgoals (false, thm) = Thm.no_prems thm;


(* tagged rules *)

type tag = {weight: int, index: int};

val tag_weight_ord: tag ord = int_ord o apply2 #weight;
val tag_index_ord: tag ord = int_ord o apply2 #index;

val tag_ord: tag ord = tag_weight_ord ||| tag_index_ord;

fun weighted_tag_ord weighted = if weighted then tag_ord else tag_index_ord;

fun tag_order list = make_order_list tag_ord NONE list;

fun weight_tag weight : tag = {weight = weight, index = 0};

fun next_tag next ({weight, ...}: tag) = {weight = weight, index = next};


(* kind: intro! / elim! / intro / elim / intro? / elim? *)

datatype kind = Kind of int * bool;

val intro_bang_kind = Kind (0, false);
val elim_bang_kind = Kind (0, true);
val intro_kind = Kind (1, false);
val elim_kind = Kind (1, true);
val intro_query_kind = Kind (2, false);
val elim_query_kind = Kind (2, true);

val kind_infos =
 [(intro_bang_kind, ("safe introduction", "(intro!)")),
  (elim_bang_kind, ("safe elimination", "(elim!)")),
  (intro_kind, ("introduction", "(intro)")),
  (elim_kind, ("elimination", "(elim)")),
  (intro_query_kind, ("extra introduction", "(intro?)")),
  (elim_query_kind, ("extra elimination", "(elim?)"))];

fun kind_index (Kind (i, _)) = i;
fun kind_elim (Kind (_, b)) = b;

val kind_domain = map #1 kind_infos;

fun kind_values x =
  replicate (length (distinct (op =) (map kind_index kind_domain))) x;

fun kind_map kind f = nth_map (kind_index kind) f;
fun kind_rule kind thm : rule = (kind_elim kind, thm);

val the_kind_info = the o AList.lookup (op =) kind_infos;

fun kind_title kind =
  let val (a, b) = the_kind_info kind
  in a ^ " rules " ^ b end;


(* rule declarations in canonical order *)

type 'a decl = {kind: kind, tag: tag, info: 'a};

fun decl_ord (args: 'a decl * 'a decl) = tag_index_ord (apply2 #tag args);

fun decl_equiv (decl1: 'a decl, decl2: 'a decl) =
  #kind decl1 = #kind decl2 andalso
  is_equal (tag_weight_ord (#tag decl1, #tag decl2));

fun next_decl next ({kind, tag, info}: 'a decl) : 'a decl =
  {kind = kind, tag = next_tag next tag, info = info};


abstype 'a decls = Decls of {next: int, rules: 'a decl list Thmtab.table}
with

local

fun dest_decls pred (Decls {rules, ...}) =
  build (rules |> Thmtab.fold (fn (th, ds) => ds |> fold (fn d => pred (th, d) ? cons (th, d))));

fun dup_decls (Decls {rules, ...}) (thm, decl) =
  member decl_equiv (Thmtab.lookup_list rules thm) decl;

fun add_decls (thm, decl) (Decls {next, rules}) =
  let
    val decl' = next_decl next decl;
    val decls' = Decls {next = next - 1, rules = Thmtab.cons_list (thm, decl') rules};
  in ((thm, decl'), decls') end;

in

fun has_decls (Decls {rules, ...}) = Thmtab.defined rules;

fun list_decls pred =
  dest_decls pred #> sort (rev_order o decl_ord o apply2 #2);

fun pretty_decls ctxt kinds decls =
  kinds |> map (fn kind =>
    Pretty.big_list (kind_title kind ^ ":")
      (dest_decls (fn (_, {kind = kind', ...}) => kind = kind') decls
        |> sort (tag_ord o apply2 (#tag o #2))
        |> map (fn (th, _) => Thm.pretty_thm_item ctxt th)));

fun merge_decls (decls1, decls2) =
  decls1 |> fold_map add_decls (list_decls (not o dup_decls decls1) decls2);

fun extend_decls (thm, decl) decls =
  if dup_decls decls (thm, decl) then NONE
  else SOME (add_decls (thm, decl) decls);

fun remove_decls thm (decls as Decls {next, rules}) =
  if has_decls decls thm
  then SOME (Decls {next = next, rules = Thmtab.delete thm rules})
  else NONE;

val empty_decls = Decls {next = ~1, rules = Thmtab.empty};

end;

end;


(* discrimination nets for intr/elim rules *)

type netpair = (tag * rule) Net.net * (tag * rule) Net.net;

val empty_netpair: netpair = (Net.empty, Net.empty);


(** Natural Deduction using (bires_flg, rule) pairs **)

(** To preserve the order of the rules, tag them with decreasing integers **)

fun insert_tagged_rule (tagged_rule as (_, (eres, th))) ((inet, enet): netpair) =
  if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.insert_term (K false) (prem, tagged_rule) enet)
    | NONE => error "insert_tagged_rule: elimination rule with no premises")
  else (Net.insert_term (K false) (Thm.concl_of th, tagged_rule) inet, enet);

fun insert_tagged_rules rls = fold_rev insert_tagged_rule rls;


local
  fun eq_kbrl ((_, (_, th)), (_, (_, th'))) = Thm.eq_thm_prop (th, th')
in

fun delete_tagged_rule (brl as (eres, th)) ((inet, enet): netpair) =
  (if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.delete_term eq_kbrl (prem, ((), brl)) enet)
    | NONE => (inet, enet))  (*no major premise: ignore*)
  else (Net.delete_term eq_kbrl (Thm.concl_of th, ((), brl)) inet, enet))
  handle Net.DELETE => (inet,enet);

end;

fun delete_tagged_rules rls = fold_rev delete_tagged_rule rls;


fun insert_rule (thm, {kind, tag, ...}: 'a decl) netpair =
  insert_tagged_rule (tag, kind_rule kind thm) netpair;

fun remove_rule thm =
  delete_tagged_rule (false, thm) o delete_tagged_rule (true, thm);


(*biresolution using a pair of nets rather than rules:
   boolean "match" indicates matching or unification.*)
fun biresolution_from_nets_tac ctxt ord pred match ((inet, enet): netpair) =
  SUBGOAL
    (fn (prem, i) =>
      let
        val hyps = Logic.strip_assums_hyp prem;
        val concl = Logic.strip_assums_concl prem;
        val tagged_rules = Net.unify_term inet concl @ maps (Net.unify_term enet) hyps;
        val order = make_order_list ord pred;
      in PRIMSEQ (Thm.biresolution (SOME ctxt) match (order tagged_rules) i) end);

(*versions taking pre-built nets.  No filtering of brls*)
fun biresolve_from_nets_tac ctxt = biresolution_from_nets_tac ctxt tag_ord NONE false;
fun bimatch_from_nets_tac ctxt = biresolution_from_nets_tac ctxt tag_ord NONE true;


(** Simpler version for resolve_tac -- only one net, and no hyps **)

type net = (int * thm) Net.net;

(*build a net of rules for resolution*)
fun build_net rls : net =
  fold_rev (fn (k, th) => Net.insert_term (K false) (Thm.concl_of th, (k, th)))
    (tag_list 1 rls) Net.empty;

(*resolution using a net rather than rules; pred supports filt_resolve_tac*)
fun filt_resolution_from_net_tac ctxt match pred net =
  SUBGOAL (fn (prem, i) =>
    let val krls = Net.unify_term net (Logic.strip_assums_concl prem) in
      if pred krls then
        PRIMSEQ (Thm.biresolution (SOME ctxt) match (map (pair false) (order_list krls)) i)
      else no_tac
    end);

(*Resolve the subgoal using the rules (making a net) unless too flexible,
   which means more than maxr rules are unifiable.      *)
fun filt_resolve_from_net_tac ctxt maxr net =
  let fun pred krls = length krls <= maxr
  in filt_resolution_from_net_tac ctxt false pred net end;

(*versions taking pre-built nets*)
fun resolve_from_net_tac ctxt = filt_resolution_from_net_tac ctxt false (K true);
fun match_from_net_tac ctxt = filt_resolution_from_net_tac ctxt true (K true);

end;
