(*  Title:      Pure/more_thm.ML
    ID:         $Id$
    Author:     Makarius

Further operations on type ctyp/cterm/thm, outside the inference kernel.
*)

infix aconvc;

signature THM =
sig
  include THM
  val aconvc: cterm * cterm -> bool
  val add_cterm_frees: cterm -> cterm list -> cterm list
  val mk_binop: cterm -> cterm -> cterm -> cterm
  val dest_binop: cterm -> cterm * cterm
  val dest_implies: cterm -> cterm * cterm
  val dest_equals: cterm -> cterm * cterm
  val dest_equals_lhs: cterm -> cterm
  val dest_equals_rhs: cterm -> cterm
  val lhs_of: thm -> cterm
  val rhs_of: thm -> cterm
  val thm_ord: thm * thm -> order
  val is_reflexive: thm -> bool
  val eq_thm: thm * thm -> bool
  val eq_thms: thm list * thm list -> bool
  val eq_thm_thy: thm * thm -> bool
  val eq_thm_prop: thm * thm -> bool
  val equiv_thm: thm * thm -> bool
  val is_dummy: thm -> bool
  val plain_prop_of: thm -> term
  val fold_terms: (term -> 'a -> 'a) -> thm -> 'a -> 'a
  val add_thm: thm -> thm list -> thm list
  val del_thm: thm -> thm list -> thm list
  val merge_thms: thm list * thm list -> thm list
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
  val elim_implies: thm -> thm -> thm
  val unvarify: thm -> thm
  val add_axiom: term list -> bstring * term -> theory -> thm * theory
  val add_def: bool -> bool -> bstring * term -> theory -> thm * theory
end;

structure Thm: THM =
struct

(** basic operations **)

(* collecting cterms *)

val op aconvc = op aconv o pairself Thm.term_of;

fun add_cterm_frees ct =
  let
    val cert = Thm.cterm_of (Thm.theory_of_cterm ct);
    val t = Thm.term_of ct;
  in Term.fold_aterms (fn v as Free _ => insert (op aconvc) (cert v) | _ => I) t end;


(* cterm constructors and destructors *)

fun mk_binop c a b = Thm.capply (Thm.capply c a) b;
fun dest_binop ct = (Thm.dest_arg1 ct, Thm.dest_arg ct);

fun dest_implies ct =
  (case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => dest_binop ct
  | _ => raise TERM ("dest_implies", [Thm.term_of ct]));

fun dest_equals ct =
  (case Thm.term_of ct of
    Const ("==", _) $ _ $ _ => dest_binop ct
  | _ => raise TERM ("dest_equals", [Thm.term_of ct]));

fun dest_equals_lhs ct =
  (case Thm.term_of ct of
    Const ("==", _) $ _ $ _ => Thm.dest_arg1 ct
  | _ => raise TERM ("dest_equals_lhs", [Thm.term_of ct]));

fun dest_equals_rhs ct =
  (case Thm.term_of ct of
    Const ("==", _) $ _ $ _ => Thm.dest_arg ct
  | _ => raise TERM ("dest_equals_rhs", [Thm.term_of ct]));

val lhs_of = dest_equals_lhs o Thm.cprop_of;
val rhs_of = dest_equals_rhs o Thm.cprop_of;


(* thm order: ignores theory context! *)

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

fun is_reflexive th = op aconv (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

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

fun is_dummy thm =
  (case try Logic.dest_term (Thm.concl_of thm) of
    NONE => false
  | SOME t => Term.is_dummy_pattern t);

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


(* lists of theorems in canonical order *)

val add_thm = update eq_thm_prop;
val del_thm = remove eq_thm_prop;
val merge_thms = merge eq_thm_prop;



(** theorem kinds **)

val axiomK = "axiom";
val assumptionK = "assumption";
val definitionK = "definition";
val theoremK = "theorem";
val lemmaK = "lemma";
val corollaryK = "corollary";
val internalK = Markup.internalK;



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



(** basic derived rules **)

(*Elimination of implication
  A    A ==> B
  ------------
        B
*)
fun elim_implies thA thAB = Thm.implies_elim thAB thA;

(*global schematic variables*)
fun unvarify th =
  let
    val thy = Thm.theory_of_thm th;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;

    val prop = Thm.full_prop_of th;
    val _ = map Logic.unvarify (prop :: Thm.hyps_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);

    val instT0 = rev (Term.add_tvars prop []) |> map (fn v as ((a, _), S) => (v, TFree (a, S)));
    val instT = map (fn (v, T) => (certT (TVar v), certT T)) instT0;
    val inst = rev (Term.add_vars prop []) |> map (fn ((a, i), T) =>
      let val T' = TermSubst.instantiateT instT0 T
      in (cert (Var ((a, i), T')), cert (Free ((a, T')))) end);
  in Thm.instantiate (instT, inst) th end;



(** specification primitives **)

fun add_axiom hyps (name, prop) thy =
  let
    val name' = if name = "" then "axiom_" ^ serial_string () else name;
    val prop' = Logic.list_implies (hyps, prop);
    val thy' = thy |> Theory.add_axioms_i [(name', prop')];
    val axm = unvarify (Thm.get_axiom_i thy' (Sign.full_name thy' name'));
    val prems = map (Thm.assume o Thm.cterm_of thy') hyps;
    val thm = fold elim_implies prems axm;
  in (thm, thy') end;

fun add_def unchecked overloaded (name, prop) thy =
  let
    val tfrees = rev (map TFree (Term.add_tfrees prop []));
    val tfrees' = map (fn a => TFree (a, [])) (Name.invents Name.context Name.aT (length tfrees));
    val strip_sorts = tfrees ~~ tfrees';
    val recover_sorts = map (pairself (Thm.ctyp_of thy o Logic.varifyT)) (tfrees' ~~ tfrees);

    val prop' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip_sorts))) prop;
    val thy' = Theory.add_defs_i unchecked overloaded [(name, prop')] thy;
    val axm' = Thm.get_axiom_i thy' (Sign.full_name thy' name);
    val thm = unvarify (Thm.instantiate (recover_sorts, []) axm');
  in (thm, thy') end;

open Thm;

end;

val op aconvc = Thm.aconvc;

structure Thmtab = TableFun(type key = thm val ord = Thm.thm_ord);
