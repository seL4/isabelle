(*  Title:      Pure/more_thm.ML
    ID:         $Id$
    Author:     Makarius

Further operations on type thm, outside the inference kernel.
*)

signature THM =
sig
  include THM
  val thm_ord: thm * thm -> order
  val eq_thm: thm * thm -> bool
  val eq_thms: thm list * thm list -> bool
  val eq_thm_thy: thm * thm -> bool
  val eq_thm_prop: thm * thm -> bool
  val equiv_thm: thm * thm -> bool
  val plain_prop_of: thm -> term
  val fold_terms: (term -> 'a -> 'a) -> thm -> 'a -> 'a
  val axiomK: string
  val assumptionK: string
  val definitionK: string
  val theoremK: string
  val lemmaK: string
  val corollaryK: string
  val internalK: string
  val rule_attribute: (Context.generic -> thm -> thm) -> attribute
  val declaration_attribute: (thm -> Context.generic -> Context.generic) -> attribute
  val theory_attributes: attribute list -> theory * thm -> theory * thm
  val proof_attributes: attribute list -> Proof.context * thm -> Proof.context * thm
  val no_attributes: 'a -> 'a * 'b list
  val simple_fact: 'a -> ('a * 'b list) list
  val read_def_cterms:
    theory * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ)list
    -> cterm list * (indexname * typ)list
  val read_cterm: theory -> string * typ -> cterm
end;

structure Thm: THM =
struct

(** basic operations **)

(* order: ignores theory context! *)

fun thm_ord (th1, th2) =
  let
    val {shyps = shyps1, hyps = hyps1, tpairs = tpairs1, prop = prop1, ...} = Thm.rep_thm th1;
    val {shyps = shyps2, hyps = hyps2, tpairs = tpairs2, prop = prop2, ...} = Thm.rep_thm th2;
  in
    (case Term.fast_term_ord (prop1, prop2) of
      EQUAL =>
        (case list_ord (prod_ord Term.fast_term_ord Term.fast_term_ord) (tpairs1, tpairs2) of
          EQUAL =>
            (case list_ord Term.fast_term_ord (hyps1, hyps2) of
              EQUAL => list_ord Term.sort_ord (shyps1, shyps2)
            | ord => ord)
        | ord => ord)
    | ord => ord)
  end;


(* equality *)

fun eq_thm ths =
  Context.joinable (pairself Thm.theory_of_thm ths) andalso
  thm_ord ths = EQUAL;

val eq_thms = eq_list eq_thm;

val eq_thm_thy = eq_thy o pairself Thm.theory_of_thm;
val eq_thm_prop = op aconv o pairself Thm.full_prop_of;


(* pattern equivalence *)

fun equiv_thm ths =
  Pattern.equiv (Theory.merge (pairself Thm.theory_of_thm ths)) (pairself Thm.full_prop_of ths);


(* misc operations *)

fun plain_prop_of raw_thm =
  let
    val thm = Thm.strip_shyps raw_thm;
    fun err msg = raise THM ("plain_prop_of: " ^ msg, 0, [thm]);
    val {hyps, prop, tpairs, ...} = Thm.rep_thm thm;
  in
    if not (null hyps) then
      err "theorem may not contain hypotheses"
    else if not (null (Thm.extra_shyps thm)) then
      err "theorem may not contain sort hypotheses"
    else if not (null tpairs) then
      err "theorem may not contain flex-flex pairs"
    else prop
  end;

fun fold_terms f th =
  let val {tpairs, prop, hyps, ...} = Thm.rep_thm th
  in fold (fn (t, u) => f t #> f u) tpairs #> f prop #> fold f hyps end;



(** theorem kinds **)

val axiomK = "axiom";
val assumptionK = "assumption";
val definitionK = "definition";
val theoremK = "theorem";
val lemmaK = "lemma";
val corollaryK = "corollary";
val internalK = "internal";



(** attributes **)

fun rule_attribute f (x, th) = (x, f x th);
fun declaration_attribute f (x, th) = (f th x, th);

fun apply_attributes mk dest =
  let
    fun app [] = I
      | app ((f: attribute) :: fs) = fn (x, th) => f (mk x, th) |>> dest |> app fs;
  in app end;

val theory_attributes = apply_attributes Context.Theory Context.the_theory;
val proof_attributes = apply_attributes Context.Proof Context.the_proof;

fun no_attributes x = (x, []);
fun simple_fact x = [(x, [])];


(** read/certify terms (obsolete) **)    (*exception ERROR*)

fun read_def_cterms (thy, types, sorts) used freeze sTs =
  let
    val (ts', tye) = Sign.read_def_terms (thy, types, sorts) used freeze sTs;
    val cts = map (Thm.cterm_of thy) ts'
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in (cts, tye) end;

fun read_cterm thy sT =
  let val ([ct], _) = read_def_cterms (thy, K NONE, K NONE) [] true [sT]
  in ct end;


open Thm;

end;

structure Thmtab = TableFun(type key = thm val ord = Thm.thm_ord);
