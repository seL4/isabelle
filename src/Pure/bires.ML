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
  val dest_bang_kind: kind
  val intro_kind: kind
  val elim_kind: kind
  val dest_kind: kind
  val intro_query_kind: kind
  val elim_query_kind: kind
  val dest_query_kind: kind
  val kind_safe: kind -> bool
  val kind_unsafe: kind -> bool
  val kind_extra: kind -> bool
  val kind_index: kind -> int
  val kind_is_elim: kind -> bool
  val kind_make_elim: kind -> thm -> thm
  val kind_name: kind -> string
  val kind_domain: kind list
  val kind_values: 'a -> 'a list
  val kind_map: kind -> ('a -> 'a) -> 'a list -> 'a list
  val kind_rule: kind -> thm -> rule
  val kind_description: kind -> string
  val kind_title: kind -> string

  type 'a decl = {kind: kind, tag: tag, info: 'a}
  val decl_ord: 'a decl ord
  val decl_eq_kind: 'a decl * 'a decl -> bool
  type 'a decls
  val has_decls: 'a decls -> thm -> bool
  val get_decls: 'a decls -> thm -> 'a decl list
  val dest_decls: 'a decls -> (thm * 'a decl -> bool) -> (thm * 'a decl) list
  val pretty_decls: Proof.context -> 'a decls -> Pretty.T list
  val merge_decls: 'a decls * 'a decls -> 'a decl list * 'a decls
  val extend_decls: thm * 'a decl -> 'a decls -> 'a decl option * 'a decls
  val remove_decls: thm -> 'a decls -> 'a decl list * 'a decls
  val empty_decls: 'a decls

  type netpair = (tag * rule) Net.net * (tag * rule) Net.net
  val empty_netpair: netpair
  val pretty_netpair: Proof.context -> string -> netpair -> Pretty.T list
  val insert_tagged_rule: tag * rule -> netpair -> netpair
  val delete_tagged_rule: int * thm -> netpair -> netpair

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


(* kind: intro/elim/dest *)

datatype kind = Kind of {index: int, is_elim: bool, make_elim: bool};

fun make_intro_kind i = Kind {index = i, is_elim = false, make_elim = false};
fun make_elim_kind i = Kind {index = i, is_elim = true, make_elim = false};
fun make_dest_kind i = Kind {index = i, is_elim = true, make_elim = true};

val intro_bang_kind = make_intro_kind 0;
val elim_bang_kind = make_elim_kind 0;
val dest_bang_kind = make_dest_kind 0;

val intro_kind = make_intro_kind 1;
val elim_kind = make_elim_kind 1;
val dest_kind = make_dest_kind 1;

val intro_query_kind = make_intro_kind 2;
val elim_query_kind = make_elim_kind 2;
val dest_query_kind = make_dest_kind 2;

val kind_infos =
 [(intro_bang_kind, ("safe introduction", "(intro!)")),
  (elim_bang_kind, ("safe elimination", "(elim!)")),
  (dest_bang_kind, ("safe destruction", "(dest!)")),
  (intro_kind, ("unsafe introduction", "(intro)")),
  (elim_kind, ("unsafe elimination", "(elim)")),
  (dest_kind, ("unsafe destruction", "(dest)")),
  (intro_query_kind, ("extra introduction", "(intro?)")),
  (elim_query_kind, ("extra elimination", "(elim?)")),
  (dest_query_kind, ("extra destruction", "(dest?)"))];

fun kind_safe (Kind {index, ...}) = index = 0;
fun kind_unsafe (Kind {index, ...}) = index = 1;
fun kind_extra (Kind {index, ...}) = index = 2;
fun kind_index (Kind {index, ...}) = index;
fun kind_is_elim (Kind {is_elim, ...}) = is_elim;
fun kind_make_elim (Kind {make_elim, ...}) = make_elim ? Tactic.make_elim;

val kind_ord = int_ord o apply2 kind_index ||| bool_ord o apply2 kind_is_elim;

fun kind_name (Kind {is_elim, make_elim, ...}) =
  if is_elim andalso make_elim then "destruction rule"
  else if is_elim then "elimination rule"
  else "introduction rule";

val kind_domain = map #1 kind_infos;

fun kind_values x =
  replicate (length (distinct (op =) (map kind_index kind_domain))) x;

fun kind_map kind f = nth_map (kind_index kind) f;
fun kind_rule kind thm : rule = (kind_is_elim kind, thm);

val the_kind_info = the o AList.lookup (op =) kind_infos;

fun kind_description kind =
  let val (a, b) = the_kind_info kind
  in a ^ " " ^ b end;

fun kind_title kind =
  let val (a, b) = the_kind_info kind
  in a ^ " rules " ^ b end;


(* rule declarations in canonical order *)

type 'a decl = {kind: kind, tag: tag, info: 'a};

fun decl_ord (args: 'a decl * 'a decl) =
  (case kind_ord (apply2 #kind args) of
    EQUAL => tag_index_ord (apply2 #tag args)
  | ord => ord);

fun decl_eq_kind ({kind, ...}: 'a decl, {kind = kind', ...}: 'a decl) = kind = kind';

fun next_decl next ({kind, tag, info}: 'a decl) : 'a decl =
  {kind = kind, tag = next_tag next tag, info = info};


abstype 'a decls = Decls of {next: int, rules: 'a decl list Proptab.table}
with

local

fun dup_decls (Decls {rules, ...}) (thm, decl) =
  member decl_eq_kind (Proptab.lookup_list rules thm) decl;

fun add_decls (thm, decl) (Decls {next, rules}) =
  let
    val decl' = next_decl next decl;
    val decls' = Decls {next = next - 1, rules = Proptab.cons_list (thm, decl') rules};
  in (decl', decls') end;

in

fun has_decls (Decls {rules, ...}) = Proptab.defined rules;

fun get_decls (Decls {rules, ...}) = Proptab.lookup_list rules;

fun dest_decls (Decls {rules, ...}) pred =
  build (rules |> Proptab.fold (fn (th, ds) => ds |> fold (fn d => pred (th, d) ? cons (th, d))))
  |> sort (decl_ord o apply2 #2);

fun pretty_decls ctxt decls =
  kind_domain |> map_filter (fn kind =>
    (case dest_decls decls (fn (_, {kind = kind', ...}) => kind = kind') of
      [] => NONE
    | ds =>
        SOME (Pretty.big_list (kind_title kind ^ ":")
          (map (Thm.pretty_thm_item ctxt o #1) ds))));

fun merge_decls (decls1, decls2) =
  decls1 |> fold_map add_decls (rev (dest_decls decls2 (not o dup_decls decls1)));

fun extend_decls (thm, decl) decls =
  if dup_decls decls (thm, decl) then (NONE, decls)
  else add_decls (thm, decl) decls |>> SOME;

fun remove_decls thm (decls as Decls {next, rules}) =
  (case get_decls decls thm of
    [] => ([], decls)
  | old_decls => (old_decls, Decls {next = next, rules = Proptab.delete thm rules}));

val empty_decls = Decls {next = ~1, rules = Proptab.empty};

end;

end;


(* discrimination nets for intr/elim rules *)

type netpair = (tag * rule) Net.net * (tag * rule) Net.net;

val empty_netpair: netpair = (Net.empty, Net.empty);

fun pretty_netpair ctxt title (inet, enet) =
  let
    fun pretty_entry ({weight, ...}: tag, (_, thm): rule) =
      Pretty.item [Pretty.str (string_of_int weight), Pretty.brk 1, Thm.pretty_thm ctxt thm];

    fun pretty_net elim net =
      (case Net.content net |> sort_distinct (tag_ord o apply2 #1) |> map pretty_entry of
        [] => NONE
      | prts => SOME (Pretty.big_list (title ^ " " ^ (if elim then "elim" else "intro")) prts));
  in map_filter I [pretty_net false inet, pretty_net true enet] end;


(** Natural Deduction using (bires_flg, rule) pairs **)

(** To preserve the order of the rules, tag them with decreasing integers **)

fun insert_tagged_rule (tagged_rule as (_, (eres, th))) ((inet, enet): netpair) =
  if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.insert_term (K false) (prem, tagged_rule) enet)
    | NONE => error "insert_tagged_rule: elimination rule with no premises")
  else (Net.insert_term (K false) (Thm.concl_of th, tagged_rule) inet, enet);

fun delete_tagged_rule (index, th) ((inet, enet): netpair) =
  let
    fun eq ((), ({index = index', ...}, _)) = index = index';
    val inet' = Net.delete_term_safe eq (Thm.concl_of th, ()) inet;
    val enet' =
      (case try Thm.major_prem_of th of
        SOME prem => Net.delete_term_safe eq (prem, ()) enet
      | NONE => enet);
  in (inet', enet') end;


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
