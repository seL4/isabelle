(*  Title:      Pure/bires.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Biresolution and resolution using nets.
*)

signature BIRES =
sig
  val insert_tagged_brl: 'a * (bool * thm) ->
    ('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net ->
      ('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net
  val delete_tagged_brl: bool * thm ->
    ('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net ->
      ('a * (bool * thm)) Net.net * ('a * (bool * thm)) Net.net
  val eq_kbrl: ('a * (bool * thm)) * ('a * (bool * thm)) -> bool
  val build_net: thm list -> (int * thm) Net.net
  val biresolution_from_nets_tac: Proof.context ->
    ('a list -> (bool * thm) list) -> bool -> 'a Net.net * 'a Net.net -> int -> tactic
  val biresolve_from_nets_tac: Proof.context ->
    (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net -> int -> tactic
  val bimatch_from_nets_tac: Proof.context ->
    (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net -> int -> tactic
  val filt_resolve_from_net_tac: Proof.context -> int -> (int * thm) Net.net -> int -> tactic
  val resolve_from_net_tac: Proof.context -> (int * thm) Net.net -> int -> tactic
  val match_from_net_tac: Proof.context -> (int * thm) Net.net -> int -> tactic
end

structure Bires: BIRES =
struct

(** To preserve the order of the rules, tag them with increasing integers **)

(*insert one tagged brl into the pair of nets*)
fun insert_tagged_brl (kbrl as (k, (eres, th))) (inet, enet) =
  if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.insert_term (K false) (prem, kbrl) enet)
    | NONE => error "insert_tagged_brl: elimination rule with no premises")
  else (Net.insert_term (K false) (Thm.concl_of th, kbrl) inet, enet);

(*delete one kbrl from the pair of nets*)
fun eq_kbrl ((_, (_, th)), (_, (_, th'))) = Thm.eq_thm_prop (th, th')

fun delete_tagged_brl (brl as (eres, th)) (inet, enet) =
  (if eres then
    (case try Thm.major_prem_of th of
      SOME prem => (inet, Net.delete_term eq_kbrl (prem, ((), brl)) enet)
    | NONE => (inet, enet))  (*no major premise: ignore*)
  else (Net.delete_term eq_kbrl (Thm.concl_of th, ((), brl)) inet, enet))
  handle Net.DELETE => (inet,enet);


(*biresolution using a pair of nets rather than rules.
    function "order" must sort and possibly filter the list of brls.
    boolean "match" indicates matching or unification.*)
fun biresolution_from_nets_tac ctxt order match (inet, enet) =
  SUBGOAL
    (fn (prem, i) =>
      let
        val hyps = Logic.strip_assums_hyp prem;
        val concl = Logic.strip_assums_concl prem;
        val kbrls = Net.unify_term inet concl @ maps (Net.unify_term enet) hyps;
      in PRIMSEQ (Thm.biresolution (SOME ctxt) match (order kbrls) i) end);

(*versions taking pre-built nets.  No filtering of brls*)
fun biresolve_from_nets_tac ctxt = biresolution_from_nets_tac ctxt order_list false;
fun bimatch_from_nets_tac ctxt = biresolution_from_nets_tac ctxt order_list true;


(*** Simpler version for resolve_tac -- only one net, and no hyps ***)

(*insert one tagged rl into the net*)
fun insert_krl (krl as (k,th)) =
  Net.insert_term (K false) (Thm.concl_of th, krl);

(*build a net of rules for resolution*)
fun build_net rls =
  fold_rev insert_krl (tag_list 1 rls) Net.empty;

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

