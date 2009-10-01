(*  Title:      Pure/more_thm.ML
    Author:     Makarius

Further operations on type ctyp/cterm/thm, outside the inference kernel.
*)

infix aconvc;

signature BASIC_THM =
sig
  include BASIC_THM
  structure Ctermtab: TABLE
  structure Thmtab: TABLE
  val aconvc: cterm * cterm -> bool
end;

signature THM =
sig
  include THM
  structure Ctermtab: TABLE
  structure Thmtab: TABLE
  val aconvc: cterm * cterm -> bool
  val add_cterm_frees: cterm -> cterm list -> cterm list
  val all_name: string * cterm -> cterm -> cterm
  val all: cterm -> cterm -> cterm
  val mk_binop: cterm -> cterm -> cterm -> cterm
  val dest_binop: cterm -> cterm * cterm
  val dest_implies: cterm -> cterm * cterm
  val dest_equals: cterm -> cterm * cterm
  val dest_equals_lhs: cterm -> cterm
  val dest_equals_rhs: cterm -> cterm
  val lhs_of: thm -> cterm
  val rhs_of: thm -> cterm
  val thm_ord: thm * thm -> order
  val cterm_cache: (cterm -> 'a) -> cterm -> 'a
  val thm_cache: (thm -> 'a) -> thm -> 'a
  val is_reflexive: thm -> bool
  val eq_thm: thm * thm -> bool
  val eq_thms: thm list * thm list -> bool
  val eq_thm_thy: thm * thm -> bool
  val eq_thm_prop: thm * thm -> bool
  val equiv_thm: thm * thm -> bool
  val class_triv: theory -> class -> thm
  val of_sort: ctyp * sort -> thm list
  val check_shyps: sort list -> thm -> thm
  val is_dummy: thm -> bool
  val plain_prop_of: thm -> term
  val add_thm: thm -> thm list -> thm list
  val del_thm: thm -> thm list -> thm list
  val merge_thms: thm list * thm list -> thm list
  val intro_rules: thm Item_Net.T
  val elim_rules: thm Item_Net.T
  val elim_implies: thm -> thm -> thm
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val certify_inst: theory ->
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list ->
    (ctyp * ctyp) list * (cterm * cterm) list
  val certify_instantiate:
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list -> thm -> thm
  val unvarify: thm -> thm
  val close_derivation: thm -> thm
  val add_axiom: binding * term -> theory -> thm * theory
  val add_def: bool -> bool -> binding * term -> theory -> thm * theory
  type binding = binding * attribute list
  val empty_binding: binding
  val rule_attribute: (Context.generic -> thm -> thm) -> attribute
  val declaration_attribute: (thm -> Context.generic -> Context.generic) -> attribute
  val theory_attributes: attribute list -> theory * thm -> theory * thm
  val proof_attributes: attribute list -> Proof.context * thm -> Proof.context * thm
  val no_attributes: 'a -> 'a * 'b list
  val simple_fact: 'a -> ('a * 'b list) list
  val tag_rule: Properties.property -> thm -> thm
  val untag_rule: string -> thm -> thm
  val tag: Properties.property -> attribute
  val untag: string -> attribute
  val position_of: thm -> Position.T
  val default_position: Position.T -> thm -> thm
  val default_position_of: thm -> thm -> thm
  val def_name: string -> string
  val def_name_optional: string -> string -> string
  val def_binding_optional: Binding.binding -> Binding.binding -> Binding.binding
  val has_name_hint: thm -> bool
  val get_name_hint: thm -> string
  val put_name_hint: string -> thm -> thm
  val get_group: thm -> string option
  val put_group: string -> thm -> thm
  val group: string -> attribute
  val axiomK: string
  val assumptionK: string
  val definitionK: string
  val theoremK: string
  val generatedK : string
  val lemmaK: string
  val corollaryK: string
  val internalK: string
  val has_kind: thm -> bool
  val get_kind: thm -> string
  val kind_rule: string -> thm -> thm
  val kind: string -> attribute
  val kind_internal: attribute
  val has_internal: Properties.property list -> bool
  val is_internal: thm -> bool
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

fun all_name (x, t) A =
  let
    val cert = Thm.cterm_of (Thm.theory_of_cterm t);
    val T = #T (Thm.rep_cterm t);
  in Thm.capply (cert (Const ("all", (T --> propT) --> propT))) (Thm.cabs_name (x, t) A) end;

fun all t A = all_name ("", t) A;

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
    (case TermOrd.fast_term_ord (prop1, prop2) of
      EQUAL =>
        (case list_ord (prod_ord TermOrd.fast_term_ord TermOrd.fast_term_ord) (tpairs1, tpairs2) of
          EQUAL =>
            (case list_ord TermOrd.fast_term_ord (hyps1, hyps2) of
              EQUAL => list_ord TermOrd.sort_ord (shyps1, shyps2)
            | ord => ord)
        | ord => ord)
    | ord => ord)
  end;


(* tables and caches *)

structure Ctermtab = Table(type key = cterm val ord = TermOrd.fast_term_ord o pairself Thm.term_of);
structure Thmtab = Table(type key = thm val ord = thm_ord);

fun cterm_cache f = Cache.create Ctermtab.empty Ctermtab.lookup Ctermtab.update f;
fun thm_cache f = Cache.create Thmtab.empty Thmtab.lookup Thmtab.update f;


(* equality *)

fun is_reflexive th = op aconv (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

fun eq_thm ths =
  Context.joinable (pairself Thm.theory_of_thm ths) andalso
  is_equal (thm_ord ths);

val eq_thms = eq_list eq_thm;

val eq_thm_thy = Theory.eq_thy o pairself Thm.theory_of_thm;
val eq_thm_prop = op aconv o pairself Thm.full_prop_of;


(* pattern equivalence *)

fun equiv_thm ths =
  Pattern.equiv (Theory.merge (pairself Thm.theory_of_thm ths)) (pairself Thm.full_prop_of ths);


(* type classes and sorts *)

fun class_triv thy c =
  Thm.of_class (Thm.ctyp_of thy (TVar ((Name.aT, 0), [c])), c);

fun of_sort (T, S) = map (fn c => Thm.of_class (T, c)) S;

fun check_shyps sorts raw_th =
  let
    val th = Thm.strip_shyps raw_th;
    val prt_sort = Syntax.pretty_sort_global (Thm.theory_of_thm th);
    val pending = Sorts.subtract sorts (Thm.extra_shyps th);
  in
    if null pending then th
    else error (Pretty.string_of (Pretty.block (Pretty.str "Pending sort hypotheses:" ::
      Pretty.brk 1 :: Pretty.commas (map prt_sort pending))))
  end;


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


(* collections of theorems in canonical order *)

val add_thm = update eq_thm_prop;
val del_thm = remove eq_thm_prop;
val merge_thms = merge eq_thm_prop;

val intro_rules = Item_Net.init eq_thm_prop Thm.concl_of;
val elim_rules = Item_Net.init eq_thm_prop Thm.major_prem_of;



(** basic derived rules **)

(*Elimination of implication
  A    A ==> B
  ------------
        B
*)
fun elim_implies thA thAB = Thm.implies_elim thAB thA;


(* forall_elim_var(s) *)

local

fun forall_elim_vars_aux strip_vars i th =
  let
    val thy = Thm.theory_of_thm th;
    val {tpairs, prop, ...} = Thm.rep_thm th;
    val add_used = Term.fold_aterms
      (fn Var ((x, j), _) => if i = j then insert (op =) x else I | _ => I);
    val used = fold (fn (t, u) => add_used t o add_used u) tpairs (add_used prop []);
    val vars = strip_vars prop;
    val cvars = (Name.variant_list used (map #1 vars), vars)
      |> ListPair.map (fn (x, (_, T)) => Thm.cterm_of thy (Var ((x, i), T)));
  in fold Thm.forall_elim cvars th end;

in

val forall_elim_vars = forall_elim_vars_aux Term.strip_all_vars;

fun forall_elim_var i th = forall_elim_vars_aux
  (fn Const ("all", _) $ Abs (a, T, _) => [(a, T)]
  | _ => raise THM ("forall_elim_vars", i, [th])) i th;

end;


(* certify_instantiate *)

fun certify_inst thy (instT, inst) =
  (map (fn (v, T) => (Thm.ctyp_of thy (TVar v), Thm.ctyp_of thy T)) instT,
    map (fn (v, t) => (Thm.cterm_of thy (Var v), Thm.cterm_of thy t)) inst);

fun certify_instantiate insts th =
  Thm.instantiate (certify_inst (Thm.theory_of_thm th) insts) th;


(* unvarify: global schematic variables *)

fun unvarify th =
  let
    val prop = Thm.full_prop_of th;
    val _ = map Logic.unvarify (prop :: Thm.hyps_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);

    val instT = rev (Term.add_tvars prop []) |> map (fn v as ((a, _), S) => (v, TFree (a, S)));
    val inst = rev (Term.add_vars prop []) |> map (fn ((a, i), T) =>
      let val T' = Term_Subst.instantiateT instT T
      in (((a, i), T'), Free ((a, T'))) end);
  in certify_instantiate (instT, inst) th end;


(* close_derivation *)

fun close_derivation thm =
  if Thm.get_name thm = "" then Thm.put_name "" thm
  else thm;



(** specification primitives **)

(* rules *)

fun add_axiom (b, prop) thy =
  let
    val b' = if Binding.is_empty b
      then Binding.name ("axiom_" ^ serial_string ()) else b;
    val thy' = thy |> Theory.add_axioms_i [(b', prop)];
    val axm = unvarify (Thm.axiom thy' (Sign.full_name thy' b'));
  in (axm, thy') end;

fun add_def unchecked overloaded (b, prop) thy =
  let
    val tfrees = rev (map TFree (Term.add_tfrees prop []));
    val tfrees' = map (fn a => TFree (a, [])) (Name.invents Name.context Name.aT (length tfrees));
    val strip_sorts = tfrees ~~ tfrees';
    val recover_sorts = map (pairself (Thm.ctyp_of thy o Logic.varifyT)) (tfrees' ~~ tfrees);

    val prop' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip_sorts))) prop;
    val thy' = Theory.add_defs_i unchecked overloaded [(b, prop')] thy;
    val axm' = Thm.axiom thy' (Sign.full_name thy' b);
    val thm = unvarify (Thm.instantiate (recover_sorts, []) axm');
  in (thm, thy') end;



(** attributes **)

type binding = binding * attribute list;
val empty_binding: binding = (Binding.empty, []);

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



(*** theorem tags ***)

(* add / delete tags *)

fun tag_rule tg = Thm.map_tags (insert (op =) tg);
fun untag_rule s = Thm.map_tags (filter_out (fn (s', _) => s = s'));

fun tag tg x = rule_attribute (K (tag_rule tg)) x;
fun untag s x = rule_attribute (K (untag_rule s)) x;


(* position *)

val position_of = Position.of_properties o Thm.get_tags;

fun default_position pos = Thm.map_tags (Position.default_properties pos);
val default_position_of = default_position o position_of;


(* def_name *)

fun def_name c = c ^ "_def";

fun def_name_optional c "" = def_name c
  | def_name_optional _ name = name;

fun def_binding_optional b name =
  if Binding.is_empty name then Binding.map_name def_name b else name;


(* unofficial theorem names *)

fun the_name_hint thm = the (AList.lookup (op =) (Thm.get_tags thm) Markup.nameN);

val has_name_hint = can the_name_hint;
val get_name_hint = the_default "??.unknown" o try the_name_hint;

fun put_name_hint name = untag_rule Markup.nameN #> tag_rule (Markup.nameN, name);


(* theorem groups *)

fun get_group thm = Properties.get (Thm.get_tags thm) Markup.groupN;

fun put_group name = if name = "" then I else Thm.map_tags (Properties.put (Markup.groupN, name));

fun group name = rule_attribute (K (put_group name));


(* theorem kinds *)

val axiomK = "axiom";
val assumptionK = "assumption";
val definitionK = "definition";
val theoremK = "theorem";
val generatedK = "generatedK"
val lemmaK = "lemma";
val corollaryK = "corollary";
val internalK = Markup.internalK;

fun the_kind thm = the (Properties.get (Thm.get_tags thm) Markup.kindN);

val has_kind = can the_kind;
val get_kind = the_default "" o try the_kind;

fun kind_rule k = tag_rule (Markup.kindN, k) o untag_rule Markup.kindN;
fun kind k x = if k = "" then x else rule_attribute (K (kind_rule k)) x;
fun kind_internal x = kind internalK x;
fun has_internal tags = exists (fn tg => tg = (Markup.kindN, internalK)) tags;
val is_internal = has_internal o Thm.get_tags;


open Thm;

end;

structure Basic_Thm: BASIC_THM = Thm;
open Basic_Thm;

