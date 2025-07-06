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
  val tag0_ord: tag ord
  val tag_ord: tag ord
  val weighted_tag_ord: bool -> tag ord
  val tag_order: (tag * 'a) list -> 'a list

  type netpair = (tag * rule) Net.net * (tag * rule) Net.net
  val empty_netpair: netpair

  val insert_tagged_rule: tag * rule -> netpair -> netpair
  val insert_tagged_rules: (tag * rule) list -> netpair -> netpair
  val delete_tagged_rule: rule -> netpair -> netpair
  val delete_tagged_rules: rule list -> netpair -> netpair
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

(** Natural Deduction using (bires_flg, rule) pairs **)

(* type rule *)

type rule = bool * thm;  (*see Thm.biresolution*)

fun subgoals_of (true, thm) = Thm.nprems_of thm - 1
  | subgoals_of (false, thm) = Thm.nprems_of thm;

val subgoals_ord = int_ord o apply2 subgoals_of;

fun no_subgoals (true, thm) = Thm.one_prem thm
  | no_subgoals (false, thm) = Thm.no_prems thm;


(* tagged rules *)

type tag = {weight: int, index: int};

val tag0_ord: tag ord = int_ord o apply2 #index;
val tag_ord: tag ord = int_ord o apply2 #weight ||| tag0_ord;

fun weighted_tag_ord weighted = if weighted then tag_ord else tag0_ord;

fun tag_order list = make_order_list tag_ord NONE list;


(* discrimination nets for intr/elim rules *)

type netpair = (tag * rule) Net.net * (tag * rule) Net.net;

val empty_netpair: netpair = (Net.empty, Net.empty);


(** To preserve the order of the rules, tag them with increasing integers **)

(*insert one tagged brl into the pair of nets*)
fun insert_tagged_rule (tagged_rule as (_, (eres, th))) ((inet, enet): netpair) =
  if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.insert_term (K false) (prem, tagged_rule) enet)
    | NONE => error "insert_tagged_rule: elimination rule with no premises")
  else (Net.insert_term (K false) (Thm.concl_of th, tagged_rule) inet, enet);

fun insert_tagged_rules rls = fold_rev insert_tagged_rule rls;


(*delete one kbrl from the pair of nets*)
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

fun delete_tagged_rules rls = fold_rev delete_tagged_rule rls;

end;

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


(*** Simpler version for resolve_tac -- only one net, and no hyps ***)

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

