(*  Title:      Pure/proofterm.ML
    Author:     Stefan Berghofer, TU Muenchen

LF style proof terms.
*)

infix 8 % %% %>;

signature PROOFTERM =
sig
  type thm_header =
    {serial: serial, pos: Position.T list, theory_name: string, thm_name: Thm_Name.T,
      prop: term, types: typ list option}
  type thm_body
  type thm_node
  datatype proof =
     MinProof
   | PBound of int
   | Abst of string * typ option * proof
   | AbsP of string * term option * proof
   | % of proof * term option
   | %% of proof * proof
   | Hyp of term
   | PAxm of string * term * typ list option
   | PClass of typ * class
   | Oracle of string * term * typ list option
   | PThm of thm_header * thm_body
  and proof_body = PBody of
    {oracles: ((string * Position.T) * term option) Ord_List.T,
     thms: (serial * thm_node) Ord_List.T,
     zboxes: ZTerm.zboxes,
     zproof: zproof,
     proof: proof}
  type oracle = (string * Position.T) * term option
  type thm = serial * thm_node
  exception MIN_PROOF of unit
  val zproof_of: proof_body -> zproof
  val proof_of: proof_body -> proof
  val join_proof: proof_body future -> proof
  val map_proof_of: (proof -> proof) -> proof_body -> proof_body
  val thm_header: serial -> Position.T list -> string -> Thm_Name.T -> term -> typ list option ->
    thm_header
  val thm_body: proof_body -> thm_body
  val thm_body_proof_raw: thm_body -> proof
  val thm_body_proof_open: thm_body -> proof
  val thm_node_theory_name: thm_node -> string
  val thm_node_name: thm_node -> Thm_Name.T
  val thm_node_prop: thm_node -> term
  val thm_node_body: thm_node -> proof_body future
  val thm_node_thms: thm_node -> thm list
  val join_thms: thm list -> proof_body list
  val make_thm: thm_header -> thm_body -> thm
  val fold_proof_atoms: bool -> (proof -> 'a -> 'a) -> proof list -> 'a -> 'a
  val fold_body_thms:
    ({serial: serial, thm_name: Thm_Name.T, prop: term, body: proof_body} -> 'a -> 'a) ->
    proof_body list -> 'a -> 'a
  val oracle_ord: oracle ord
  val thm_ord: thm ord
  val union_oracles: oracle Ord_List.T -> oracle Ord_List.T -> oracle Ord_List.T
  val unions_oracles: oracle Ord_List.T list -> oracle Ord_List.T
  val union_thms: thm Ord_List.T -> thm Ord_List.T -> thm Ord_List.T
  val unions_thms: thm Ord_List.T list -> thm Ord_List.T
  val no_proof_body: zproof -> proof -> proof_body
  val no_thm_names: proof -> proof
  val no_thm_proofs: proof -> proof
  val no_body_proofs: proof -> proof

  val encode: Consts.T -> proof XML.Encode.T
  val encode_body: Consts.T -> proof_body XML.Encode.T
  val encode_standard_term: Consts.T -> term XML.Encode.T
  val encode_standard_proof: Consts.T -> proof XML.Encode.T
  val decode: Consts.T -> proof XML.Decode.T
  val decode_body: Consts.T -> proof_body XML.Decode.T

  val %> : proof * term -> proof

  (*primitive operations*)
  val zproof_enabled: int -> bool
  val proof_enabled: int -> bool
  val oracle_enabled: int -> bool
  val get_proofs_level: unit -> int
  val proofs: int Unsynchronized.ref
  val any_proofs_enabled: unit -> bool
  val proof_combt: proof * term list -> proof
  val proof_combt': proof * term option list -> proof
  val proof_combP: proof * proof list -> proof
  val strip_combt: proof -> proof * term option list
  val strip_combP: proof -> proof * proof list
  val any_head_of: proof -> proof
  val term_head_of: proof -> proof
  val proof_head_of: proof -> proof
  val compact_proof: proof -> bool
  val strip_thm_body: proof_body -> proof_body
  val map_proof_same: term Same.operation -> typ Same.operation
    -> (typ * class -> proof) -> proof Same.operation
  val map_proof_terms_same: term Same.operation -> typ Same.operation -> proof Same.operation
  val map_proof_types_same: typ Same.operation -> proof Same.operation
  val map_proof_terms: (term -> term) -> (typ -> typ) -> proof -> proof
  val map_proof_types: (typ -> typ) -> proof -> proof
  val fold_proof_terms: (term -> 'a -> 'a) -> proof -> 'a -> 'a
  val fold_proof_terms_types: (term -> 'a -> 'a) -> (typ -> 'a -> 'a) -> proof -> 'a -> 'a
  val maxidx_proof: proof -> int -> int
  val change_types: typ list option -> proof -> proof
  val abstract_over: term -> proof -> proof
  val incr_bv_same: int -> int -> int -> int -> proof Same.operation
  val incr_bv: int -> int -> int -> int -> proof -> proof
  val incr_boundvars: int -> int -> proof -> proof
  val prf_loose_bvar1: proof -> int -> bool
  val prf_loose_Pbvar1: proof -> int -> bool
  val prf_add_loose_bnos: int -> int -> proof -> int list * int list -> int list * int list
  val norm_proof: Envir.env -> proof -> proof
  val norm_proof_remove_types: Envir.env -> proof -> proof
  val subst_bounds: term list -> proof -> proof
  val subst_pbounds: proof list -> proof -> proof
  val freeze_thaw_prf: proof -> proof * (proof -> proof)

  (*proof terms for specific inference rules*)
  val trivial_proof: proof
  val implies_intr_proof: term -> proof -> proof
  val implies_intr_proof': term -> proof -> proof
  val forall_intr_proof: string * term -> typ option -> proof -> proof
  val forall_intr_proof': term -> proof -> proof
  val varifyT_proof: ((string * sort) * (indexname * sort)) list -> proof -> proof
  val legacy_freezeT: term -> proof -> proof
  val rotate_proof: term list -> term -> (string * typ) list -> term list -> int -> proof -> proof
  val permute_prems_proof: term list -> int -> int -> proof -> proof
  val generalize_proof: Names.set * Names.set -> int -> term -> proof -> proof
  val instantiate: typ TVars.table * term Vars.table -> proof -> proof
  val lift_proof: term -> int -> term list -> proof -> proof
  val incr_indexes: int -> proof -> proof
  val assumption_proof: term list -> term -> int -> proof -> proof
  val bicompose_proof: Envir.env -> int -> bool -> term list -> term list -> term option ->
    term list -> int -> int -> proof -> proof -> proof
  val reflexive_axm: proof
  val symmetric_axm: proof
  val transitive_axm: proof
  val equal_intr_axm: proof
  val equal_elim_axm: proof
  val abstract_rule_axm: proof
  val combination_axm: proof
  val reflexive_proof: proof
  val symmetric_proof: proof -> proof
  val transitive_proof: typ -> term -> proof -> proof -> proof
  val equal_intr_proof: term -> term -> proof -> proof -> proof
  val equal_elim_proof: term -> term -> proof -> proof -> proof
  val abstract_rule_proof: string * term -> proof -> proof
  val combination_proof: term -> term -> term -> term -> proof -> proof -> proof
  val could_unify: proof * proof -> bool
  type sorts_proof = (class * class -> proof) * (string * class list list * class -> proof)
  val of_sort_proof: Sorts.algebra -> sorts_proof -> (typ * class -> proof) -> typ * sort -> proof list
  val axiom_proof: string -> term -> proof
  val oracle_proof: string -> term -> proof
  val shrink_proof: proof -> proof

  (*rewriting on proof terms*)
  val add_prf_rrule: proof * proof -> theory -> theory
  val add_prf_rproc: (typ list -> term option list -> proof -> (proof * proof) option) -> theory -> theory
  val set_preproc: (theory -> proof -> proof) -> theory -> theory
  val apply_preproc: theory -> proof -> proof
  val forall_intr_variables_term: term -> term
  val forall_intr_variables: term -> proof -> proof
  val no_skel: proof
  val normal_skel: proof
  val rewrite_proof: theory -> (proof * proof) list *
    (typ list -> term option list -> proof -> (proof * proof) option) list -> proof -> proof
  val rewrite_proof_notypes: (proof * proof) list *
    (typ list -> term option list -> proof -> (proof * proof) option) list -> proof -> proof
  val rew_proof: theory -> proof -> proof

  val reconstruct_proof: theory -> term -> proof -> proof
  val prop_of': term list -> proof -> term
  val prop_of: proof -> term
  val expand_name_empty: thm_header -> Thm_Name.T option
  val expand_proof: theory -> (thm_header -> Thm_Name.T option) -> proof -> proof

  val standard_vars: Name.context -> term * proof option -> term * proof option
  val standard_vars_term: Name.context -> term -> term
  val add_standard_vars: proof -> (string * typ) list -> (string * typ) list
  val add_standard_vars_term: term -> (string * typ) list -> (string * typ) list

  val export_enabled: unit -> bool
  val export_standard_enabled: unit -> bool
  val export_proof_boxes_required: theory -> bool
  val export_proof_boxes: proof_body list -> unit
  val fulfill_norm_proof: theory -> (serial * proof_body) list -> proof_body -> proof_body
  val thm_proof: theory -> sorts_proof -> Thm_Name.P -> sort list -> term list ->
    term -> (serial * proof_body future) list -> proof_body -> proof_body
  val unconstrain_thm_proof: theory -> sorts_proof -> sort list ->
    term -> (serial * proof_body future) list -> proof_body -> term * proof_body
  val get_identity: sort list -> term list -> term -> proof ->
    {serial: serial, theory_name: string, thm_name: Thm_Name.T} option
  val get_approximative_name: sort list -> term list -> term -> proof -> Thm_Name.T
  type thm_id = {serial: serial, theory_name: string}
  val make_thm_id: serial * string -> thm_id
  val thm_header_id: thm_header -> thm_id
  val thm_id: thm -> thm_id
  val get_id: sort list -> term list -> term -> proof -> thm_id option
  val this_id: thm_id option -> thm_id -> bool
  val proof_boxes: {excluded: thm_id -> bool, included: thm_id -> bool} ->
    proof list -> (thm_header * proof) list  (*exception MIN_PROOF*)
end

structure Proofterm : PROOFTERM =
struct

(** datatype proof **)

type thm_header =
  {serial: serial, pos: Position.T list, theory_name: string, thm_name: Thm_Name.T,
    prop: term, types: typ list option};

datatype proof =
   MinProof
 | PBound of int
 | Abst of string * typ option * proof
 | AbsP of string * term option * proof
 | op % of proof * term option
 | op %% of proof * proof
 | Hyp of term
 | PAxm of string * term * typ list option
 | PClass of typ * class
 | Oracle of string * term * typ list option
 | PThm of thm_header * thm_body
and proof_body = PBody of
  {oracles: ((string * Position.T) * term option) Ord_List.T,
   thms: (serial * thm_node) Ord_List.T,
   zboxes: ZTerm.zboxes,
   zproof: zproof,
   proof: proof}
and thm_body =
  Thm_Body of {open_proof: proof -> proof, body: proof_body future}
and thm_node =
  Thm_Node of {theory_name: string, thm_name: Thm_Name.T, prop: term,
    body: proof_body future, export: unit lazy, consolidate: unit lazy};

type oracle = (string * Position.T) * term option;
val oracle_ord: oracle ord =
  prod_ord (prod_ord fast_string_ord Position.ord) (option_ord Term_Ord.fast_term_ord);

type thm = serial * thm_node;
val thm_ord: thm ord = fn ((i, _), (j, _)) => int_ord (j, i);


exception MIN_PROOF of unit;

fun proof_of (PBody {proof, ...}) = proof;
fun zproof_of (PBody {zproof, ...}) = zproof;
val join_proof = Future.join #> proof_of;

fun map_proof_of f (PBody {oracles, thms, zboxes, zproof, proof}) =
  PBody {oracles = oracles, thms = thms, zboxes = zboxes, zproof = zproof, proof = f proof};

fun no_proof (PBody {oracles, thms, zboxes, zproof, ...}) =
  PBody {oracles = oracles, thms = thms, zboxes = zboxes, zproof = zproof, proof = MinProof};

fun thm_header serial pos theory_name thm_name prop types : thm_header =
  {serial = serial, pos = pos, theory_name = theory_name, thm_name = thm_name,
    prop = prop, types = types};

fun thm_body body = Thm_Body {open_proof = I, body = Future.value body};
fun thm_body_proof_raw (Thm_Body {body, ...}) = join_proof body;
fun thm_body_proof_open (Thm_Body {open_proof, body, ...}) = open_proof (join_proof body);

fun rep_thm_node (Thm_Node args) = args;
val thm_node_theory_name = #theory_name o rep_thm_node;
val thm_node_name = #thm_name o rep_thm_node;
val thm_node_prop = #prop o rep_thm_node;
val thm_node_body = #body o rep_thm_node;
val thm_node_thms = thm_node_body #> Future.join #> (fn PBody {thms, ...} => thms);
val thm_node_export = #export o rep_thm_node;
val thm_node_consolidate = #consolidate o rep_thm_node;

fun join_thms (thms: thm list) =
  Future.joins (map (thm_node_body o #2) thms);

val consolidate_bodies =
  maps (fn PBody {thms, ...} => map (thm_node_consolidate o #2) thms)
  #> Lazy.consolidate #> map Lazy.force #> ignore;

fun make_thm_node theory_name thm_name prop body export =
  let
    val consolidate =
      Lazy.lazy_name "Proofterm.make_thm_node" (fn () =>
        let val PBody {thms, ...} = Future.join body
        in consolidate_bodies (join_thms thms) end);
  in
    Thm_Node {theory_name = theory_name, thm_name = thm_name, prop = prop, body = body,
      export = export, consolidate = consolidate}
  end;

val no_export = Lazy.value ();

fun make_thm ({serial, theory_name, thm_name, prop, ...}: thm_header) (Thm_Body {body, ...}) =
  (serial, make_thm_node theory_name thm_name prop body no_export);


(* proof atoms *)

fun fold_proof_atoms all f =
  let
    fun app (Abst (_, _, prf)) = app prf
      | app (AbsP (_, _, prf)) = app prf
      | app (prf % _) = app prf
      | app (prf1 %% prf2) = app prf1 #> app prf2
      | app (prf as PThm ({serial = i, ...}, Thm_Body {body, ...})) = (fn (x, seen) =>
          if Intset.member seen i then (x, seen)
          else
            let val (x', seen') =
              (if all then app (join_proof body) else I) (x, Intset.insert i seen)
            in (f prf x', seen') end)
      | app prf = (fn (x, seen) => (f prf x, seen));
  in fn prfs => fn x => #1 (fold app prfs (x, Intset.empty)) end;

fun fold_body_thms f =
  let
    fun app (PBody {thms, ...}) =
      tap join_thms thms |> fold (fn (i, thm_node) => fn (x, seen) =>
        if Intset.member seen i then (x, seen)
        else
          let
            val thm_name = thm_node_name thm_node;
            val prop = thm_node_prop thm_node;
            val body = Future.join (thm_node_body thm_node);
            val (x', seen') = app body (x, Intset.insert i seen);
          in (f {serial = i, thm_name = thm_name, prop = prop, body = body} x', seen') end);
  in fn bodies => fn x => #1 (fold app bodies (x, Intset.empty)) end;


(* proof body *)

val union_oracles = Ord_List.union oracle_ord;
val unions_oracles = Ord_List.unions oracle_ord;

val union_thms = Ord_List.union thm_ord;
val unions_thms = Ord_List.unions thm_ord;

fun no_proof_body zproof proof =
  PBody {oracles = [], thms = [], zboxes = [], zproof = zproof, proof = proof};
val no_thm_body = thm_body (no_proof_body ZNop MinProof);

fun no_thm_names (Abst (x, T, prf)) = Abst (x, T, no_thm_names prf)
  | no_thm_names (AbsP (x, t, prf)) = AbsP (x, t, no_thm_names prf)
  | no_thm_names (prf % t) = no_thm_names prf % t
  | no_thm_names (prf1 %% prf2) = no_thm_names prf1 %% no_thm_names prf2
  | no_thm_names (PThm ({serial, pos, theory_name, thm_name = _, prop, types}, thm_body)) =
      PThm (thm_header serial pos theory_name Thm_Name.empty prop types, thm_body)
  | no_thm_names a = a;

fun no_thm_proofs (Abst (x, T, prf)) = Abst (x, T, no_thm_proofs prf)
  | no_thm_proofs (AbsP (x, t, prf)) = AbsP (x, t, no_thm_proofs prf)
  | no_thm_proofs (prf % t) = no_thm_proofs prf % t
  | no_thm_proofs (prf1 %% prf2) = no_thm_proofs prf1 %% no_thm_proofs prf2
  | no_thm_proofs (PThm (header, _)) = PThm (header, no_thm_body)
  | no_thm_proofs a = a;

fun no_body_proofs (Abst (x, T, prf)) = Abst (x, T, no_body_proofs prf)
  | no_body_proofs (AbsP (x, t, prf)) = AbsP (x, t, no_body_proofs prf)
  | no_body_proofs (prf % t) = no_body_proofs prf % t
  | no_body_proofs (prf1 %% prf2) = no_body_proofs prf1 %% no_body_proofs prf2
  | no_body_proofs (PThm (header, Thm_Body {open_proof, body})) =
      let
        val PBody {zproof, proof, ...} = Future.join body;
        val body' = Future.value (no_proof_body zproof proof);
        val thm_body' = Thm_Body {open_proof = open_proof, body = body'};
      in PThm (header, thm_body') end
  | no_body_proofs a = a;



(** XML data representation **)

(* encode *)

local

open XML.Encode Term_XML.Encode;

fun proof consts prf = prf |> variant
 [fn MinProof => ([], []),
  fn PBound a => ([], int a),
  fn Abst (a, b, c) => ([a], pair (option typ) (proof consts) (b, c)),
  fn AbsP (a, b, c) => ([a], pair (option (term consts)) (proof consts) (b, c)),
  fn a % b => ([], pair (proof consts) (option (term consts)) (a, b)),
  fn a %% b => ([], pair (proof consts) (proof consts) (a, b)),
  fn Hyp a => ([], term consts a),
  fn PAxm (a, b, c) => ([a], pair (term consts) (option (list typ)) (b, c)),
  fn PClass (a, b) => ([b], typ a),
  fn Oracle (a, b, c) => ([a], pair (term consts) (option (list typ)) (b, c)),
  fn PThm ({serial, pos, theory_name, thm_name, prop, types}, Thm_Body {open_proof, body, ...}) =>
    ([int_atom serial, theory_name, #1 thm_name, int_atom (#2 thm_name)],
      pair (list properties) (pair (term consts) (pair (option (list typ)) (proof_body consts)))
        (map Position.properties_of pos,
          (prop, (types, map_proof_of open_proof (Future.join body)))))]
and proof_body consts (PBody {oracles, thms, zboxes = _, zproof = _, proof = prf}) =
  triple (list (pair (pair string (properties o Position.properties_of))
      (option (term consts)))) (list (thm consts)) (proof consts) (oracles, thms, prf)
and thm consts (a, thm_node) =
  pair int (pair string (pair Thm_Name.encode (pair (term consts) (proof_body consts))))
    (a, (thm_node_theory_name thm_node, (thm_node_name thm_node, (thm_node_prop thm_node,
      (Future.join (thm_node_body thm_node))))));

fun standard_term consts t = t |> variant
 [fn Const (a, b) => ([a], list typ (Consts.typargs consts (a, b))),
  fn Free (a, _) => ([a], []),
  fn Var (a, _) => (indexname a, []),
  fn Bound a => ([], int a),
  fn Abs (a, b, c) => ([a], pair typ (standard_term consts) (b, c)),
  fn op $ a => ([], pair (standard_term consts) (standard_term consts) a)];

fun standard_proof consts prf = prf |> variant
 [fn MinProof => ([], []),
  fn PBound a => ([], int a),
  fn Abst (a, SOME b, c) => ([a], pair typ (standard_proof consts) (b, c)),
  fn AbsP (a, SOME b, c) => ([a], pair (standard_term consts) (standard_proof consts) (b, c)),
  fn a % SOME b => ([], pair (standard_proof consts) (standard_term consts) (a, b)),
  fn a %% b => ([], pair (standard_proof consts) (standard_proof consts) (a, b)),
  fn Hyp a => ([], standard_term consts a),
  fn PAxm (name, _, SOME Ts) => ([name], list typ Ts),
  fn PClass (T, c) => ([c], typ T),
  fn Oracle (name, prop, SOME Ts) => ([name], pair (standard_term consts) (list typ) (prop, Ts)),
  fn PThm ({serial, theory_name, thm_name, types = SOME Ts, ...}, _) =>
    ([int_atom serial, theory_name, #1 thm_name, int_atom (#2 thm_name)], list typ Ts)];

in

val encode = proof;
val encode_body = proof_body;
val encode_standard_term = standard_term;
val encode_standard_proof = standard_proof;

end;


(* decode *)

local

open XML.Decode Term_XML.Decode;

fun proof consts prf = prf |> variant
 [fn ([], []) => MinProof,
  fn ([], a) => PBound (int a),
  fn ([a], b) => let val (c, d) = pair (option typ) (proof consts) b in Abst (a, c, d) end,
  fn ([a], b) => let val (c, d) = pair (option (term consts)) (proof consts) b in AbsP (a, c, d) end,
  fn ([], a) => op % (pair (proof consts) (option (term consts)) a),
  fn ([], a) => op %% (pair (proof consts) (proof consts) a),
  fn ([], a) => Hyp (term consts a),
  fn ([a], b) => let val (c, d) = pair (term consts) (option (list typ)) b in PAxm (a, c, d) end,
  fn ([b], a) => PClass (typ a, b),
  fn ([a], b) => let val (c, d) = pair (term consts) (option (list typ)) b in Oracle (a, c, d) end,
  fn ([a, b, c, d], e) =>
    let
      val ((x, (y, (z, w)))) =
        pair (list properties) (pair (term consts) (pair (option (list typ)) (proof_body consts))) e;
      val header = thm_header (int_atom a) (map Position.of_properties x) b (c, int_atom d) y z;
    in PThm (header, thm_body w) end]
and proof_body consts x =
  let
    val (a, b, c) =
      triple (list (pair (pair string (Position.of_properties o properties))
        (option (term consts)))) (list (thm consts)) (proof consts) x;
  in PBody {oracles = a, thms = b, zboxes = [], zproof = ZNop, proof = c} end
and thm consts x =
  let
    val (a, (b, (c, (d, e)))) =
      pair int (pair string (pair Thm_Name.decode (pair (term consts) (proof_body consts)))) x
  in (a, make_thm_node b c d (Future.value e) no_export) end;

in

val decode = proof;
val decode_body = proof_body;

end;


(** proof objects with different levels of detail **)

fun zproof_enabled proofs = proofs = 4 orelse proofs = 5 orelse proofs = 6;
fun proof_enabled proofs = proofs = 2 orelse proofs = 6;
fun oracle_enabled proofs = not (proofs = 0 orelse proofs = 4);

val proofs = Unsynchronized.ref 6;

fun get_proofs_level () =
  let val proofs = ! proofs in
    if 0 <= proofs andalso proofs <= 6 andalso proofs <> 3 then proofs
    else error ("Illegal level of detail for proof objects: " ^ string_of_int proofs)
  end;

fun any_proofs_enabled () =
  let val proofs = get_proofs_level ()
  in zproof_enabled proofs orelse proof_enabled proofs end;

fun (p %> t) = p % SOME t;

val proof_combt = Library.foldl (op %>);
val proof_combt' = Library.foldl (op %);
val proof_combP = Library.foldl (op %%);

fun strip_combt prf =
  let
    fun strip (p % t, ts) = strip (p, t :: ts)
      | strip res = res;
  in strip (prf, []) end;

fun strip_combP prf =
  let
    fun strip (p %% q, qs) = strip (p, q :: qs)
      | strip res = res;
  in strip (prf, []) end;

fun any_head_of (p %% _) = any_head_of p
  | any_head_of (p % _) = any_head_of p
  | any_head_of p = p;

fun term_head_of (p % _) = term_head_of p
  | term_head_of p = p;

fun proof_head_of (p %% _) = proof_head_of p
  | proof_head_of p = p;

val atomic_proof =
  (fn Abst _ => false | AbsP _ => false
    | op % _ => false | op %% _ => false
    | MinProof => false
    | _ => true);

fun compact_proof (p % _) = compact_proof p
  | compact_proof (p %% q) = atomic_proof q andalso compact_proof p
  | compact_proof p = atomic_proof p;

fun strip_thm_body (body as PBody {proof, ...}) =
  (case term_head_of (proof_head_of proof) of
    PThm (_, Thm_Body {body = body', ...}) => Future.join body'
  | _ => body);

val mk_Abst = fold_rev (fn (x, _: typ) => fn prf => Abst (x, NONE, prf));
val mk_AbsP = fold_rev (fn _: term => fn prf => AbsP ("H", NONE, prf));

fun map_proof_same term typ ofclass =
  let
    val typs = Same.map typ;

    fun proof (Abst (s, T, prf)) =
          (Abst (s, Same.map_option typ T, Same.commit proof prf)
            handle Same.SAME => Abst (s, T, proof prf))
      | proof (AbsP (s, t, prf)) =
          (AbsP (s, Same.map_option term t, Same.commit proof prf)
            handle Same.SAME => AbsP (s, t, proof prf))
      | proof (prf % t) =
          (proof prf % Same.commit (Same.map_option term) t
            handle Same.SAME => prf % Same.map_option term t)
      | proof (prf1 %% prf2) =
          (proof prf1 %% Same.commit proof prf2
            handle Same.SAME => prf1 %% proof prf2)
      | proof (PAxm (a, prop, SOME Ts)) = PAxm (a, prop, SOME (typs Ts))
      | proof (PClass C) = ofclass C
      | proof (Oracle (a, prop, SOME Ts)) = Oracle (a, prop, SOME (typs Ts))
      | proof (PThm ({serial, pos, theory_name, thm_name, prop, types = SOME Ts}, thm_body)) =
          PThm (thm_header serial pos theory_name thm_name prop (SOME (typs Ts)), thm_body)
      | proof _ = raise Same.SAME;
  in proof end;

fun map_proof_terms_same term typ = map_proof_same term typ (fn (T, c) => PClass (typ T, c));
fun map_proof_types_same typ = map_proof_terms_same (Term.map_types_same typ) typ;

fun map_proof_terms f g =
  Same.commit (map_proof_terms_same (Same.function_eq (op =) f) (Same.function_eq (op =) g));

fun map_proof_types f =
  Same.commit (map_proof_types_same (Same.function_eq (op =) f));

fun fold_proof_terms f (Abst (_, _, prf)) = fold_proof_terms f prf
  | fold_proof_terms f (AbsP (_, SOME t, prf)) = f t #> fold_proof_terms f prf
  | fold_proof_terms f (AbsP (_, NONE, prf)) = fold_proof_terms f prf
  | fold_proof_terms f (prf % SOME t) = fold_proof_terms f prf #> f t
  | fold_proof_terms f (prf % NONE) = fold_proof_terms f prf
  | fold_proof_terms f (prf1 %% prf2) = fold_proof_terms f prf1 #> fold_proof_terms f prf2
  | fold_proof_terms _ _ = I;

fun fold_proof_terms_types f g (Abst (_, SOME T, prf)) = g T #> fold_proof_terms_types f g prf
  | fold_proof_terms_types f g (Abst (_, NONE, prf)) = fold_proof_terms_types f g prf
  | fold_proof_terms_types f g (AbsP (_, SOME t, prf)) = f t #> fold_proof_terms_types f g prf
  | fold_proof_terms_types f g (AbsP (_, NONE, prf)) = fold_proof_terms_types f g prf
  | fold_proof_terms_types f g (prf % SOME t) = fold_proof_terms_types f g prf #> f t
  | fold_proof_terms_types f g (prf % NONE) = fold_proof_terms_types f g prf
  | fold_proof_terms_types f g (prf1 %% prf2) =
      fold_proof_terms_types f g prf1 #> fold_proof_terms_types f g prf2
  | fold_proof_terms_types _ g (PAxm (_, _, SOME Ts)) = fold g Ts
  | fold_proof_terms_types _ g (PClass (T, _)) = g T
  | fold_proof_terms_types _ g (Oracle (_, _, SOME Ts)) = fold g Ts
  | fold_proof_terms_types _ g (PThm ({types = SOME Ts, ...}, _)) = fold g Ts
  | fold_proof_terms_types _ _ _ = I;

fun maxidx_proof prf = fold_proof_terms_types Term.maxidx_term Term.maxidx_typ prf;

fun change_types types (PAxm (name, prop, _)) = PAxm (name, prop, types)
  | change_types (SOME [T]) (PClass (_, c)) = PClass (T, c)
  | change_types types (Oracle (name, prop, _)) = Oracle (name, prop, types)
  | change_types types (PThm ({serial, pos, theory_name, thm_name, prop, types = _}, thm_body)) =
      PThm (thm_header serial pos theory_name thm_name prop types, thm_body)
  | change_types _ prf = prf;


(*Abstraction of a proof term over its occurrences of v,
    which must contain no loose bound variables.
  The resulting proof term is ready to become the body of an Abst.*)

fun abstract_over v =
  let
    fun term lev u =
      if v aconv u then Bound lev
      else
        (case u of
           Abs (a, T, t) => Abs (a, T, term (lev + 1) t)
         | t $ u =>
            (term lev t $ Same.commit (term lev) u
              handle Same.SAME => t $ term lev u)
         | _ => raise Same.SAME);

    fun proof lev (AbsP (a, t, p)) =
          (AbsP (a, Same.map_option (term lev) t, Same.commit (proof lev) p)
           handle Same.SAME => AbsP (a, t, proof lev p))
      | proof lev (Abst (a, T, p)) = Abst (a, T, proof (lev + 1) p)
      | proof lev (p %% q) = (proof lev p %% Same.commit (proof lev) q
          handle Same.SAME => p %% proof lev q)
      | proof lev (p % t) =
          (proof lev p % Option.map (Same.commit (term lev)) t
            handle Same.SAME => p % Same.map_option (term lev) t)
      | proof _ _ = raise Same.SAME;

  in Same.commit (proof 0) end;


(*increments a proof term's non-local bound variables
  required when moving a proof term within abstractions
     inc is  increment for bound variables
     lev is  level at which a bound variable is considered 'loose'*)

fun incr_bv_same incP inct =
  if incP = 0 andalso inct = 0 then fn _ => fn _ => Same.same
  else
    let
      val term = Term.incr_bv_same inct;

      fun proof Plev _ (PBound i) =
            if i >= Plev then PBound (i + incP) else raise Same.SAME
        | proof Plev tlev (AbsP (a, t, p)) =
            (AbsP (a, Same.map_option (term tlev) t, Same.commit (proof (Plev + 1) tlev) p)
              handle Same.SAME => AbsP (a, t, proof (Plev + 1) tlev p))
        | proof Plev tlev (Abst (a, T, body)) =
            Abst (a, T, proof Plev (tlev + 1) body)
        | proof Plev tlev (p %% q) =
            (proof Plev tlev p %% Same.commit (proof Plev tlev) q
              handle Same.SAME => p %% proof Plev tlev q)
        | proof Plev tlev (p % t) =
            (proof Plev tlev p % Option.map (Same.commit (term tlev)) t
              handle Same.SAME => p % Same.map_option (term tlev) t)
        | proof _ _ _ = raise Same.SAME;
    in proof end;

fun incr_bv incP inct Plev tlev = Same.commit (incr_bv_same incP inct Plev tlev);

fun incr_boundvars incP inct = incr_bv incP inct 0 0;


fun prf_loose_bvar1 (prf1 %% prf2) k = prf_loose_bvar1 prf1 k orelse prf_loose_bvar1 prf2 k
  | prf_loose_bvar1 (prf % SOME t) k = prf_loose_bvar1 prf k orelse loose_bvar1 (t, k)
  | prf_loose_bvar1 (_ % NONE) _ = true
  | prf_loose_bvar1 (AbsP (_, SOME t, prf)) k = loose_bvar1 (t, k) orelse prf_loose_bvar1 prf k
  | prf_loose_bvar1 (AbsP (_, NONE, _)) _ = true
  | prf_loose_bvar1 (Abst (_, _, prf)) k = prf_loose_bvar1 prf (k+1)
  | prf_loose_bvar1 _ _ = false;

fun prf_loose_Pbvar1 (PBound i) k = i = k
  | prf_loose_Pbvar1 (prf1 %% prf2) k = prf_loose_Pbvar1 prf1 k orelse prf_loose_Pbvar1 prf2 k
  | prf_loose_Pbvar1 (prf % _) k = prf_loose_Pbvar1 prf k
  | prf_loose_Pbvar1 (AbsP (_, _, prf)) k = prf_loose_Pbvar1 prf (k+1)
  | prf_loose_Pbvar1 (Abst (_, _, prf)) k = prf_loose_Pbvar1 prf k
  | prf_loose_Pbvar1 _ _ = false;

fun prf_add_loose_bnos plev _ (PBound i) (is, js) =
      if i < plev then (is, js) else (insert (op =) (i-plev) is, js)
  | prf_add_loose_bnos plev tlev (prf1 %% prf2) p =
      prf_add_loose_bnos plev tlev prf2
        (prf_add_loose_bnos plev tlev prf1 p)
  | prf_add_loose_bnos plev tlev (prf % opt) (is, js) =
      prf_add_loose_bnos plev tlev prf
        (case opt of
          NONE => (is, insert (op =) ~1 js)
        | SOME t => (is, add_loose_bnos (t, tlev, js)))
  | prf_add_loose_bnos plev tlev (AbsP (_, opt, prf)) (is, js) =
      prf_add_loose_bnos (plev+1) tlev prf
        (case opt of
          NONE => (is, insert (op =) ~1 js)
        | SOME t => (is, add_loose_bnos (t, tlev, js)))
  | prf_add_loose_bnos plev tlev (Abst (_, _, prf)) p =
      prf_add_loose_bnos plev (tlev+1) prf p
  | prf_add_loose_bnos _ _ _ _ = ([], []);


(* substitutions *)

local

fun conflicting_tvarsT envT =
  Term.fold_atyps
    (fn T => fn instT =>
      (case T of
        TVar (v as (_, S)) =>
          if TVars.defined instT v orelse can (Type.lookup envT) v then instT
          else TVars.add (v, Logic.dummy_tfree S) instT
      | _ => instT));

fun conflicting_tvars env =
  Term.fold_aterms
    (fn t => fn inst =>
      (case t of
        Var (v as (_, T)) =>
          if Vars.defined inst v orelse can (Envir.lookup env) v then inst
          else Vars.add (v, Free ("dummy", T)) inst
      | _ => inst));

fun del_conflicting_tvars envT ty =
  Term_Subst.instantiateT (TVars.build (conflicting_tvarsT envT ty)) ty;

fun del_conflicting_vars env tm =
  let
    val instT =
      TVars.build (tm |> Term.fold_types (conflicting_tvarsT (Envir.type_env env)));
    val inst = Vars.build (tm |> conflicting_tvars env);
  in Term_Subst.instantiate (instT, inst) tm end;

in

fun norm_proof envir =
  let
    val tyenv = Envir.type_env envir;
    fun msg s = warning ("type conflict in norm_proof:\n" ^ s);
    fun norm_term_same t = Envir.norm_term_same envir t handle TYPE (s, _, _) =>
      (msg s; Envir.norm_term_same envir (del_conflicting_vars envir t));
    fun norm_type_same T = Envir.norm_type_same tyenv T handle TYPE (s, _, _) =>
      (msg s; Envir.norm_type_same tyenv (del_conflicting_tvars tyenv T));
    fun norm_types_same Ts = Envir.norm_types_same tyenv Ts handle TYPE (s, _, _) =>
      (msg s;  Envir.norm_types_same tyenv (map (del_conflicting_tvars tyenv) Ts));

    fun norm (Abst (a, T, p)) =
          (Abst (a, Same.map_option norm_type_same T, Same.commit norm p)
            handle Same.SAME => Abst (a, T, norm p))
      | norm (AbsP (a, t, p)) =
          (AbsP (a, Same.map_option norm_term_same t, Same.commit norm p)
            handle Same.SAME => AbsP (a, t, norm p))
      | norm (p % t) =
          (norm p % Option.map (Same.commit norm_term_same) t
            handle Same.SAME => p % Same.map_option norm_term_same t)
      | norm (p %% q) =
          (norm p %% Same.commit norm q
            handle Same.SAME => p %% norm q)
      | norm (PAxm (a, prop, Ts)) =
          PAxm (a, prop, Same.map_option norm_types_same Ts)
      | norm (PClass (T, c)) =
          PClass (norm_type_same T, c)
      | norm (Oracle (a, prop, Ts)) =
          Oracle (a, prop, Same.map_option norm_types_same Ts)
      | norm (PThm ({serial = i, pos = p, theory_name, thm_name, prop = t, types = Ts}, thm_body)) =
          PThm (thm_header i p theory_name thm_name t
            (Same.map_option norm_types_same Ts), thm_body)
      | norm _ = raise Same.SAME;
  in Same.commit norm end;

end;


(* remove some types in proof term (to save space) *)

fun remove_types (Abs (s, _, t)) = Abs (s, dummyT, remove_types t)
  | remove_types (t $ u) = remove_types t $ remove_types u
  | remove_types (Const (s, _)) = Const (s, dummyT)
  | remove_types t = t;

fun remove_types_env (Envir.Envir {maxidx, tenv, tyenv}) =
  Envir.Envir {maxidx = maxidx, tenv = Vartab.map (K (apsnd remove_types)) tenv, tyenv = tyenv};

fun norm_proof_remove_types env prf = norm_proof (remove_types_env env) prf;


(* substitution of bound variables *)

fun subst_bounds args prf =
  if null args then prf
  else
    let
      val term = Term.subst_bounds_same args;

      fun proof lev (AbsP (a, t, p)) =
            (AbsP (a, Same.map_option (term lev) t, Same.commit (proof lev) p)
              handle Same.SAME => AbsP (a, t, proof lev p))
        | proof lev (Abst (a, T, p)) = Abst (a, T, proof (lev + 1) p)
        | proof lev (p %% q) =
            (proof lev p %% Same.commit (proof lev) q
              handle Same.SAME => p %% proof lev q)
        | proof lev (p % t) =
            (proof lev p % Option.map (Same.commit (term lev)) t
              handle Same.SAME => p % Same.map_option (term lev) t)
        | proof _ _ = raise Same.SAME;
    in Same.commit (proof 0) prf end;

fun subst_pbounds args prf =
  let
    val n = length args;
    fun proof Plev tlev (PBound i) =
          if i < Plev then raise Same.SAME    (*var is locally bound*)
          else if i - Plev < n then incr_boundvars Plev tlev (nth args (i - Plev))
          else PBound (i - n)  (*loose: change it*)
      | proof Plev tlev (AbsP (a, t, p)) = AbsP (a, t, proof (Plev + 1) tlev p)
      | proof Plev tlev (Abst (a, T, p)) = Abst (a, T, proof Plev (tlev + 1) p)
      | proof Plev tlev (p %% q) =
          (proof Plev tlev p %% Same.commit (proof Plev tlev) q
            handle Same.SAME => p %% proof Plev tlev q)
      | proof Plev tlev (p % t) = proof Plev tlev p % t
      | proof _ _ _ = raise Same.SAME;
  in if null args then prf else Same.commit (proof 0 0) prf end;


(* freezing and thawing of variables in proof terms *)

local

fun frzT names =
  map_type_tvar (fn (ixn, S) => TFree (the (AList.lookup (op =) names ixn), S));

fun thawT names =
  map_type_tfree (fn (a, S) =>
    (case AList.lookup (op =) names a of
      NONE => raise Same.SAME
    | SOME ixn => TVar (ixn, S)));

fun freeze names names' (t $ u) =
      freeze names names' t $ freeze names names' u
  | freeze names names' (Abs (s, T, t)) =
      Abs (s, frzT names' T, freeze names names' t)
  | freeze _ names' (Const (s, T)) = Const (s, frzT names' T)
  | freeze _ names' (Free (s, T)) = Free (s, frzT names' T)
  | freeze names names' (Var (ixn, T)) =
      Free (the (AList.lookup (op =) names ixn), frzT names' T)
  | freeze _ _ t = t;

fun thaw names names' (t $ u) =
      thaw names names' t $ thaw names names' u
  | thaw names names' (Abs (s, T, t)) =
      Abs (s, thawT names' T, thaw names names' t)
  | thaw _ names' (Const (s, T)) = Const (s, thawT names' T)
  | thaw names names' (Free (s, T)) =
      let val T' = thawT names' T in
        (case AList.lookup (op =) names s of
          NONE => Free (s, T')
        | SOME ixn => Var (ixn, T'))
      end
  | thaw _ names' (Var (ixn, T)) = Var (ixn, thawT names' T)
  | thaw _ _ t = t;

in

fun freeze_thaw_prf prf =
  let
    val (fs, Tfs, vs, Tvs) = fold_proof_terms_types
      (fn t => fn (fs, Tfs, vs, Tvs) =>
         (Term.add_free_names t fs, Term.add_tfree_names t Tfs,
          Term.add_var_names t vs, Term.add_tvar_names t Tvs))
      (fn T => fn (fs, Tfs, vs, Tvs) =>
         (fs, Term.add_tfree_namesT T Tfs,
          vs, Term.add_tvar_namesT T Tvs))
      prf ([], [], [], []);
    val names = vs ~~ Name.variant_list fs (map fst vs);
    val names' = Tvs ~~ Name.variant_list Tfs (map fst Tvs);
    val rnames = map swap names;
    val rnames' = map swap names';
  in
    (map_proof_terms (freeze names names') (frzT names') prf,
     map_proof_terms (thaw rnames rnames') (thawT rnames'))
  end;

end;



(** inference rules **)

(* trivial implication *)

val trivial_proof = AbsP ("H", NONE, PBound 0);


(* implication introduction *)

fun gen_implies_intr_proof f h prf =
  let
    fun abshyp i (Hyp t) = if h aconv t then PBound i else raise Same.SAME
      | abshyp i (Abst (s, T, prf)) = Abst (s, T, abshyp i prf)
      | abshyp i (AbsP (s, t, prf)) = AbsP (s, t, abshyp (i + 1) prf)
      | abshyp i (prf % t) = abshyp i prf % t
      | abshyp i (prf1 %% prf2) =
          (abshyp i prf1 %% abshyph i prf2
            handle Same.SAME => prf1 %% abshyp i prf2)
      | abshyp _ _ = raise Same.SAME
    and abshyph i prf = (abshyp i prf handle Same.SAME => prf);
  in
    AbsP ("H", f h, abshyph 0 prf)
  end;

val implies_intr_proof = gen_implies_intr_proof (K NONE);
val implies_intr_proof' = gen_implies_intr_proof SOME;


(* forall introduction *)

fun forall_intr_proof (a, v) opt_T prf = Abst (a, opt_T, abstract_over v prf);

fun forall_intr_proof' v prf =
  let val (a, T) = (case v of Var ((a, _), T) => (a, T) | Free (a, T) => (a, T))
  in forall_intr_proof (a, v) (SOME T) prf end;


(* varify *)

fun varifyT_proof names prf =
  if null names then prf
  else
    let
      val tab = TFrees.make names;
      val typ =
        Term.map_atyps_same
          (fn TFree v =>
              (case TFrees.lookup tab v of
                NONE => raise Same.SAME
              | SOME w => TVar w)
            | _ => raise Same.SAME);
    in Same.commit (map_proof_types_same typ) prf end;


(* freeze *)

fun legacy_freezeT t prf =
  (case Type.legacy_freezeT t of
    NONE => prf
  | SOME f =>
      let val frzT = map_type_tvar (Same.function f)
      in map_proof_terms (map_types frzT) frzT prf end);


(* rotate assumptions *)

fun rotate_proof Bs Bi' params asms m prf =
  let
    val i = length asms;
    val j = length Bs;
  in
    mk_AbsP (Bs @ [Bi']) (proof_combP (prf, map PBound
      (j downto 1) @ [mk_Abst params (mk_AbsP asms
        (proof_combP (proof_combt (PBound i, map Bound ((length params - 1) downto 0)),
          map PBound (((i-m-1) downto 0) @ ((i-1) downto (i-m))))))]))
  end;


(* permute premises *)

fun permute_prems_proof prems' j k prf =
  let val n = length prems' in
    mk_AbsP prems'
      (proof_combP (prf, map PBound ((n-1 downto n-j) @ (k-1 downto 0) @ (n-j-1 downto k))))
  end;


(* generalization *)

fun generalize_proof (tfrees, frees) idx prop prf =
  let
    val gen =
      if Names.is_empty frees then []
      else
        fold_aterms (fn Free (x, T) => Names.defined frees x ? insert (op =) (x, T) | _ => I)
          (Term_Subst.generalize (tfrees, Names.empty) idx prop) [];
  in
    prf
    |> Same.commit (map_proof_terms_same
        (Term_Subst.generalize_same (tfrees, Names.empty) idx)
        (Term_Subst.generalizeT_same tfrees idx))
    |> fold (fn (x, T) => forall_intr_proof (x, Free (x, T)) NONE) gen
    |> fold_rev (fn (x, T) => fn prf' => prf' %> Var (Name.clean_index (x, idx), T)) gen
  end;


(* instantiation *)

fun instantiate (instT, inst) =
  Same.commit (map_proof_terms_same
    (Term_Subst.instantiate_same (instT, Vars.map (K remove_types) inst))
    (Term_Subst.instantiateT_same instT));


(* lifting *)

fun lift_proof gprop inc prems prf =
  let
    val typ = Logic.incr_tvar_same inc;
    val typs = Same.map_option (Same.map typ);

    fun term Ts lev =
      Logic.incr_indexes_operation {fixed = [], Ts = Ts, inc = inc, level = lev};

    fun proof Ts lev (Abst (a, T, p)) =
          (Abst (a, Same.map_option typ T, Same.commit (proof Ts (lev + 1)) p)
            handle Same.SAME => Abst (a, T, proof Ts (lev + 1) p))
      | proof Ts lev (AbsP (a, t, p)) =
          (AbsP (a, Same.map_option (term Ts lev) t, Same.commit (proof Ts lev) p)
            handle Same.SAME => AbsP (a, t, proof Ts lev p))
      | proof Ts lev (p % t) =
          (proof Ts lev p % Option.map (Same.commit (term Ts lev)) t
            handle Same.SAME => p % Same.map_option (term Ts lev) t)
      | proof Ts lev (p %% q) =
          (proof Ts lev p %% Same.commit (proof Ts lev) q
            handle Same.SAME => p %% proof Ts lev q)
      | proof _ _ (PAxm (a, prop, Ts)) = PAxm (a, prop, typs Ts)
      | proof _ _ (PClass (T, c)) = PClass (typ T, c)
      | proof _ _ (Oracle (a, prop, Ts)) = Oracle (a, prop, typs Ts)
      | proof _ _ (PThm ({serial, pos, theory_name, thm_name, prop, types}, thm_body)) =
          PThm (thm_header serial pos theory_name thm_name prop (typs types), thm_body)
      | proof _ _ _ = raise Same.SAME;

    val k = length prems;

    fun mk_app b (i, j, p) =
      if b then (i - 1, j, p %% PBound i) else (i, j - 1, p %> Bound j);

    fun lift Ts bs i j (Const ("Pure.imp", _) $ A $ B) =
          AbsP ("H", NONE (*A*), lift Ts (true::bs) (i + 1) j B)
      | lift Ts bs i j (Const ("Pure.all", _) $ Abs (a, T, t)) =
          Abst (a, NONE (*T*), lift (T::Ts) (false::bs) i (j + 1) t)
      | lift Ts bs i j _ =
          proof_combP (Same.commit (proof (rev Ts) 0) prf,
            map (fn k => (#3 (fold_rev mk_app bs (i - 1, j - 1, PBound k)))) (i + k - 1 downto i));
  in mk_AbsP prems (lift [] [] 0 0 gprop) end;

fun incr_indexes i =
  Same.commit
    (map_proof_terms_same
      (Logic.incr_indexes_operation {fixed = [], Ts = [], inc = i, level = 0})
      (Logic.incr_tvar_same i));


(* proof by assumption *)

fun mk_asm_prf C i m =
  let
    fun imp_prf _ i 0 = PBound i
      | imp_prf (Const ("Pure.imp", _) $ A $ B) i m = AbsP ("H", NONE (*A*), imp_prf B (i+1) (m-1))
      | imp_prf _ i _ = PBound i;
    fun all_prf (Const ("Pure.all", _) $ Abs (a, T, t)) = Abst (a, NONE (*T*), all_prf t)
      | all_prf t = imp_prf t (~i) m
  in all_prf C end;

fun assumption_proof Bs Bi n prf =
  mk_AbsP Bs (proof_combP (prf, map PBound (length Bs - 1 downto 0) @ [mk_asm_prf Bi n ~1]));


(* composition of object rule with proof state *)

fun flatten_params_proof i j n (Const ("Pure.imp", _) $ A $ B, k) =
      AbsP ("H", NONE (*A*), flatten_params_proof (i+1) j n (B, k))
  | flatten_params_proof i j n (Const ("Pure.all", _) $ Abs (a, T, t), k) =
      Abst (a, NONE (*T*), flatten_params_proof i (j+1) n (t, k))
  | flatten_params_proof i j n (_, k) = proof_combP (proof_combt (PBound (k+i),
      map Bound (j-1 downto 0)), map PBound (remove (op =) (i-n) (i-1 downto 0)));

fun bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf =
  let
    val normt = Envir.norm_term env;
    val normp = norm_proof_remove_types env;

    val lb = length Bs;
    val la = length As;

    fun proof p =
      mk_AbsP (map normt (Bs @ As)) (proof_combP (sprf,
        map PBound (lb + la - 1 downto la)) %%
          proof_combP (p, (if n>0 then [mk_asm_prf (the A) n m] else []) @
            map (if flatten then flatten_params_proof 0 0 n else PBound o snd)
              (oldAs ~~ (la - 1 downto 0))));
  in
    if Envir.is_empty env then proof rprf
    else if Envir.above env smax
    then proof (normp rprf)
    else normp (proof rprf)
  end;



(** sort constraints within the logic **)

type sorts_proof = (class * class -> proof) * (string * class list list * class -> proof);

fun of_sort_proof algebra (classrel_proof, arity_proof) hyps =
  Sorts.of_sort_derivation algebra
   {class_relation = fn _ => fn _ => fn (prf, c1) => fn c2 =>
      if c1 = c2 then prf else classrel_proof (c1, c2) %% prf,
    type_constructor = fn (a, _) => fn dom => fn c =>
      let val Ss = map (map snd) dom and prfs = maps (map fst) dom
      in proof_combP (arity_proof (a, Ss, c), prfs) end,
    type_variable = fn typ => map (fn c => (hyps (typ, c), c)) (Type.sort_of_atyp typ)};

fun unconstrainT_proof algebra sorts_proof (ucontext: Logic.unconstrain_context) =
  let
    val typ = #typ_operation ucontext {strip_sorts = true};
    val typ_sort = #typ_operation ucontext {strip_sorts = false};

    fun hyps T =
      (case AList.lookup (op =) (#constraints ucontext) T of
        SOME t => Hyp t
      | NONE => raise Fail "unconstrainT_proof: missing constraint");

    fun class (T, c) =
      let val T' = Same.commit typ_sort T
      in the_single (of_sort_proof algebra sorts_proof hyps (T', [c])) end;
  in
    Same.commit (map_proof_same (Term.map_types_same typ) typ class)
    #> fold_rev (implies_intr_proof o #2) (#constraints ucontext)
  end;



(** axioms and theorems **)

val add_type_variables = (fold_types o fold_atyps) (insert (op =));
fun type_variables_of t = rev (add_type_variables t []);

val add_variables = fold_aterms (fn a => (is_Var a orelse is_Free a) ? insert (op =) a);
fun variables_of t = rev (add_variables t []);

fun test_args _ [] = true
  | test_args is (Bound i :: ts) =
      not (member (op =) is i) andalso test_args (i :: is) ts
  | test_args _ _ = false;

fun is_fun (Type ("fun", _)) = true
  | is_fun (TVar _) = true
  | is_fun _ = false;

fun vars_of t = map Var (build_rev (Term.add_vars t));

fun add_funvars Ts (vs, t) =
  if is_fun (fastype_of1 (Ts, t)) then
    union (op =) vs (map_filter (fn Var (ixn, T) =>
      if is_fun T then SOME ixn else NONE | _ => NONE) (vars_of t))
  else vs;

fun add_npvars q p Ts (vs, Const ("Pure.imp", _) $ t $ u) =
      add_npvars q p Ts (add_npvars q (not p) Ts (vs, t), u)
  | add_npvars q p Ts (vs, Const ("Pure.all", Type (_, [Type (_, [T, _]), _])) $ t) =
      add_npvars q p Ts (vs, if p andalso q then betapply (t, Var (("",0), T)) else t)
  | add_npvars q p Ts (vs, Abs (_, T, t)) = add_npvars q p (T::Ts) (vs, t)
  | add_npvars _ _ Ts (vs, t) = add_npvars' Ts (vs, t)
and add_npvars' Ts (vs, t) =
  (case strip_comb t of
    (Var (ixn, _), ts) => if test_args [] ts then vs
      else Library.foldl (add_npvars' Ts)
        (AList.update (op =) (ixn,
          Library.foldl (add_funvars Ts) ((these ooo AList.lookup) (op =) vs ixn, ts)) vs, ts)
  | (Abs (_, T, u), ts) => Library.foldl (add_npvars' (T::Ts)) (vs, u :: ts)
  | (_, ts) => Library.foldl (add_npvars' Ts) (vs, ts));

fun prop_vars (Const ("Pure.imp", _) $ P $ Q) = union (op =) (prop_vars P) (prop_vars Q)
  | prop_vars (Const ("Pure.all", _) $ Abs (_, _, t)) = prop_vars t
  | prop_vars t = (case strip_comb t of (Var (ixn, _), _) => [ixn] | _ => []);

fun is_proj t =
  let
    fun is_p i t =
      (case strip_comb t of
        (Bound _, []) => false
      | (Bound j, ts) => j >= i orelse exists (is_p i) ts
      | (Abs (_, _, u), _) => is_p (i+1) u
      | (_, ts) => exists (is_p i) ts)
  in
    (case strip_abs_body t of
      Bound _ => true
    | t' => is_p 0 t')
  end;

fun prop_args prop =
  let
    val needed_vars =
      union (op =) (Library.foldl (uncurry (union (op =)))
        ([], map (uncurry (insert (op =))) (add_npvars true true [] ([], prop))))
      (prop_vars prop);
  in
    variables_of prop |> map
      (fn var as Var (ixn, _) => if member (op =) needed_vars ixn then SOME var else NONE
        | free => SOME free)
  end;

fun const_proof mk name prop =
  let
    val args = prop_args prop;
    val ({outer_constraints, ...}, prop1) = Logic.unconstrainT [] prop;
    val head = mk (name, prop1, NONE);
  in proof_combP (proof_combt' (head, args), map PClass outer_constraints) end;

val axiom_proof = const_proof PAxm;
val oracle_proof = const_proof Oracle;

val shrink_proof =
  let
    fun shrink ls lev (prf as Abst (a, T, body)) =
          let val (b, is, ch, body') = shrink ls (lev+1) body
          in (b, is, ch, if ch then Abst (a, T, body') else prf) end
      | shrink ls lev (prf as AbsP (a, t, body)) =
          let val (b, is, ch, body') = shrink (lev::ls) lev body
          in (b orelse member (op =) is 0, map_filter (fn 0 => NONE | i => SOME (i-1)) is,
            ch, if ch then AbsP (a, t, body') else prf)
          end
      | shrink ls lev prf =
          let val (is, ch, _, prf') = shrink' ls lev [] [] prf
          in (false, is, ch, prf') end
    and shrink' ls lev ts prfs (prf as prf1 %% prf2) =
          let
            val p as (_, is', ch', prf') = shrink ls lev prf2;
            val (is, ch, ts', prf'') = shrink' ls lev ts (p::prfs) prf1
          in (union (op =) is is', ch orelse ch', ts',
              if ch orelse ch' then prf'' %% prf' else prf)
          end
      | shrink' ls lev ts prfs (prf as prf1 % t) =
          let val (is, ch, (ch', t')::ts', prf') = shrink' ls lev (t::ts) prfs prf1
          in (is, ch orelse ch', ts',
              if ch orelse ch' then prf' % t' else prf) end
      | shrink' ls lev ts prfs (prf as PBound i) =
          (if exists (fn SOME (Bound j) => lev-j <= nth ls i | _ => true) ts
             orelse has_duplicates (op =)
               (Library.foldl (fn (js, SOME (Bound j)) => j :: js | (js, _) => js) ([], ts))
             orelse exists #1 prfs then [i] else [], false, map (pair false) ts, prf)
      | shrink' _ _ ts _ (Hyp t) = ([], false, map (pair false) ts, Hyp t)
      | shrink' _ _ ts _ (prf as MinProof) = ([], false, map (pair false) ts, prf)
      | shrink' _ _ ts _ (prf as PClass _) = ([], false, map (pair false) ts, prf)
      | shrink' _ _ ts prfs prf =
          let
            val prop =
              (case prf of
                PAxm (_, prop, _) => prop
              | Oracle (_, prop, _) => prop
              | PThm ({prop, ...}, _) => prop
              | _ => raise Fail "shrink: proof not in normal form");
            val vs = vars_of prop;
            val (ts', ts'') = chop (length vs) ts;
            val insts = take (length ts') (map (fst o dest_Var) vs) ~~ ts';
            val nvs = Library.foldl (fn (ixns', (ixn, ixns)) =>
              insert (op =) ixn
                (case AList.lookup (op =) insts ixn of
                  SOME (SOME t) => if is_proj t then union (op =) ixns ixns' else ixns'
                | _ => union (op =) ixns ixns'))
                  (needed prop ts'' prfs, add_npvars false true [] ([], prop));
            val insts' = map
              (fn (ixn, x as SOME _) => if member (op =) nvs ixn then (false, x) else (true, NONE)
                | (_, x) => (false, x)) insts
          in ([], false, insts' @ map (pair false) ts'', prf) end
    and needed (Const ("Pure.imp", _) $ t $ u) ts ((b, _, _, _)::prfs) =
          union (op =) (if b then map (fst o dest_Var) (vars_of t) else []) (needed u ts prfs)
      | needed (Var (ixn, _)) (_::_) _ = [ixn]
      | needed _ _ _ = [];
  in fn prf => #4 (shrink [] 0 prf) end;



(** axioms for equality **)

local val thy = Sign.local_path (Context.the_global_context ()) in

val [reflexive_axm, symmetric_axm, transitive_axm, equal_intr_axm,
  equal_elim_axm, abstract_rule_axm, combination_axm] =
    map (fn (b, t) => PAxm (Sign.full_name thy b, Logic.varify_global t, NONE))
      Theory.equality_axioms;

end;

val reflexive_proof = reflexive_axm % NONE;

val is_reflexive_proof = fn PAxm ("Pure.reflexive", _, _) % _ => true | _ => false;

fun symmetric_proof prf =
  if is_reflexive_proof prf then prf
  else symmetric_axm % NONE % NONE %% prf;

fun transitive_proof U u prf1 prf2 =
  if is_reflexive_proof prf1 then prf2
  else if is_reflexive_proof prf2 then prf1
  else if U = propT then transitive_axm % NONE % SOME (remove_types u) % NONE %% prf1 %% prf2
  else transitive_axm % NONE % NONE % NONE %% prf1 %% prf2;

fun equal_intr_proof A B prf1 prf2 =
  equal_intr_axm %> remove_types A %> remove_types B %% prf1 %% prf2;

fun equal_elim_proof A B prf1 prf2 =
  equal_elim_axm %> remove_types A %> remove_types B %% prf1 %% prf2;

fun abstract_rule_proof (a, x) prf =
  abstract_rule_axm % NONE % NONE %% forall_intr_proof (a, x) NONE prf;

fun check_comb (PAxm ("Pure.combination", _, _) % f % _ % _ % _ %% prf %% _) =
      is_some f orelse check_comb prf
  | check_comb (PAxm ("Pure.transitive", _, _) % _ % _ % _ %% prf1 %% prf2) =
      check_comb prf1 andalso check_comb prf2
  | check_comb (PAxm ("Pure.symmetric", _, _) % _ % _ %% prf) = check_comb prf
  | check_comb _ = false;

fun combination_proof f g t u prf1 prf2 =
  let
    val f' = Envir.beta_norm f;
    val g' = Envir.beta_norm g;
    val ax =
      if check_comb prf1 then combination_axm % NONE % NONE
      else if is_reflexive_proof prf1 then combination_axm %> remove_types f' % NONE
      else combination_axm %> remove_types f' %> remove_types g'
    val t' =
      (case Term.head_of f' of
        Abs _ => SOME (remove_types t)
      | Var _ => SOME (remove_types t)
      | _ => NONE);
    val u' =
      (case Term.head_of g' of
        Abs _ => SOME (remove_types u)
      | Var _ => SOME (remove_types u)
      | _ => NONE);
  in ax % t' % u' %% prf1 %% prf2 end;



(** rewriting on proof terms **)

(* simple first order matching functions for terms and proofs (see pattern.ML) *)

exception PMatch;

fun flt (i: int) = filter (fn n => n < i);

fun fomatch Ts tymatch j instsp p =
  let
    fun mtch (instsp as (tyinsts, insts)) = fn
        (Var (ixn, T), t)  =>
          if j>0 andalso not (null (flt j (loose_bnos t)))
          then raise PMatch
          else (tymatch (tyinsts, fn () => (T, fastype_of1 (Ts, t))),
            (ixn, t) :: insts)
      | (Free (a, T), Free (b, U)) =>
          if a=b then (tymatch (tyinsts, K (T, U)), insts) else raise PMatch
      | (Const (a, T), Const (b, U))  =>
          if a=b then (tymatch (tyinsts, K (T, U)), insts) else raise PMatch
      | (f $ t, g $ u) => mtch (mtch instsp (f, g)) (t, u)
      | (Bound i, Bound j) => if i=j then instsp else raise PMatch
      | _ => raise PMatch
  in mtch instsp (apply2 Envir.beta_eta_contract p) end;

fun match_proof Ts tymatch =
  let
    fun optmatch _ inst (NONE, _) = inst
      | optmatch _ _ (SOME _, NONE) = raise PMatch
      | optmatch mtch inst (SOME x, SOME y) = mtch inst (x, y)

    fun matcht Ts j (pinst, tinst) (t, u) =
      (pinst, fomatch Ts tymatch j tinst (t, Envir.beta_norm u));
    fun matchT (pinst, (tyinsts, insts)) p =
      (pinst, (tymatch (tyinsts, K p), insts));
    fun matchTs inst (Ts, Us) = Library.foldl (uncurry matchT) (inst, Ts ~~ Us);

    fun mtch Ts i j (pinst, tinst) (Hyp (Var (ixn, _)), prf) =
          if i = 0 andalso j = 0 then ((ixn, prf) :: pinst, tinst)
          else
            (case apfst (flt i) (apsnd (flt j) (prf_add_loose_bnos 0 0 prf ([], []))) of
              ([], []) => ((ixn, incr_boundvars (~i) (~j) prf) :: pinst, tinst)
            | ([], _) =>
                if j = 0 then ((ixn, incr_boundvars (~i) (~j) prf) :: pinst, tinst)
                else raise PMatch
            | _ => raise PMatch)
      | mtch Ts i j inst (prf1 % opt1, prf2 % opt2) =
          optmatch (matcht Ts j) (mtch Ts i j inst (prf1, prf2)) (opt1, opt2)
      | mtch Ts i j inst (prf1 %% prf2, prf1' %% prf2') =
          mtch Ts i j (mtch Ts i j inst (prf1, prf1')) (prf2, prf2')
      | mtch Ts i j inst (Abst (_, opT, prf1), Abst (_, opU, prf2)) =
          mtch (the_default dummyT opU :: Ts) i (j+1)
            (optmatch matchT inst (opT, opU)) (prf1, prf2)
      | mtch Ts i j inst (prf1, Abst (_, opU, prf2)) =
          mtch (the_default dummyT opU :: Ts) i (j+1) inst
            (incr_boundvars 0 1 prf1 %> Bound 0, prf2)
      | mtch Ts i j inst (AbsP (_, opt, prf1), AbsP (_, opu, prf2)) =
          mtch Ts (i+1) j (optmatch (matcht Ts j) inst (opt, opu)) (prf1, prf2)
      | mtch Ts i j inst (prf1, AbsP (_, _, prf2)) =
          mtch Ts (i+1) j inst (incr_boundvars 1 0 prf1 %% PBound 0, prf2)
      | mtch Ts i j inst (PAxm (s1, _, opTs), PAxm (s2, _, opUs)) =
          if s1 = s2 then optmatch matchTs inst (opTs, opUs)
          else raise PMatch
      | mtch Ts i j inst (PClass (T1, c1), PClass (T2, c2)) =
          if c1 = c2 then matchT inst (T1, T2)
          else raise PMatch
      | mtch Ts i j inst
            (PThm ({thm_name = name1, prop = prop1, types = types1, ...}, _),
              PThm ({thm_name = name2, prop = prop2, types = types2, ...}, _)) =
          if name1 = name2 andalso prop1 = prop2
          then optmatch matchTs inst (types1, types2)
          else raise PMatch
      | mtch _ _ _ inst (PBound i, PBound j) = if i = j then inst else raise PMatch
      | mtch _ _ _ _ _ = raise PMatch
  in mtch Ts 0 0 end;

fun prf_subst (pinst, (tyinsts, insts)) =
  let
    val substT = Envir.subst_type_same tyinsts;
    val substTs = Same.map substT;

    fun subst' lev (Var (xi, _)) =
        (case AList.lookup (op =) insts xi of
          NONE => raise Same.SAME
        | SOME u => Term.incr_boundvars lev u)
      | subst' _ (Const (s, T)) = Const (s, substT T)
      | subst' _ (Free (s, T)) = Free (s, substT T)
      | subst' lev (Abs (a, T, body)) =
          (Abs (a, substT T, Same.commit (subst' (lev + 1)) body)
            handle Same.SAME => Abs (a, T, subst' (lev + 1) body))
      | subst' lev (f $ t) =
          (subst' lev f $ Same.commit (subst' lev) t
            handle Same.SAME => f $ subst' lev t)
      | subst' _ _ = raise Same.SAME;

    fun subst plev tlev (AbsP (a, t, body)) =
          (AbsP (a, Same.map_option (subst' tlev) t, Same.commit (subst (plev + 1) tlev) body)
            handle Same.SAME => AbsP (a, t, subst (plev + 1) tlev body))
      | subst plev tlev (Abst (a, T, body)) =
          (Abst (a, Same.map_option substT T, Same.commit (subst plev (tlev + 1)) body)
            handle Same.SAME => Abst (a, T, subst plev (tlev + 1) body))
      | subst plev tlev (prf %% prf') =
          (subst plev tlev prf %% Same.commit (subst plev tlev) prf'
            handle Same.SAME => prf %% subst plev tlev prf')
      | subst plev tlev (prf % t) =
          (subst plev tlev prf % Same.commit (Same.map_option (subst' tlev)) t
            handle Same.SAME => prf % Same.map_option (subst' tlev) t)
      | subst plev tlev (Hyp (Var (xi, _))) =
          (case AList.lookup (op =) pinst xi of
            NONE => raise Same.SAME
          | SOME prf' => incr_boundvars plev tlev prf')
      | subst _ _ (PAxm (id, prop, Ts)) = PAxm (id, prop, Same.map_option substTs Ts)
      | subst _ _ (PClass (T, c)) = PClass (substT T, c)
      | subst _ _ (Oracle (id, prop, Ts)) = Oracle (id, prop, Same.map_option substTs Ts)
      | subst _ _ (PThm ({serial = i, pos = p, theory_name, thm_name, prop, types}, thm_body)) =
          PThm (thm_header i p theory_name thm_name prop (Same.map_option substTs types), thm_body)
      | subst _ _ _ = raise Same.SAME;
  in fn t => subst 0 0 t handle Same.SAME => t end;

(*A fast unification filter: true unless the two terms cannot be unified.
  Terms must be NORMAL.  Treats all Vars as distinct. *)
fun could_unify (prf1, prf2) =
  let
    fun matchrands (prf1 %% prf2) (prf1' %% prf2') =
          could_unify (prf2, prf2') andalso matchrands prf1 prf1'
      | matchrands (prf % SOME t) (prf' % SOME t') =
          Term.could_unify (t, t') andalso matchrands prf prf'
      | matchrands (prf % _) (prf' % _) = matchrands prf prf'
      | matchrands _ _ = true
  in case (any_head_of prf1, any_head_of prf2) of
        (_, Hyp (Var _)) => true
      | (Hyp (Var _), _) => true
      | (PAxm (a, _, _), PAxm (b, _, _)) => a = b andalso matchrands prf1 prf2
      | (PClass (_, c), PClass (_, d)) => c = d andalso matchrands prf1 prf2
      | (PThm ({thm_name = a, prop = propa, ...}, _), PThm ({thm_name = b, prop = propb, ...}, _)) =>
          a = b andalso propa = propb andalso matchrands prf1 prf2
      | (PBound i, PBound j) => i = j andalso matchrands prf1 prf2
      | (AbsP _, _) =>  true   (*because of possible eta equality*)
      | (Abst _, _) =>  true
      | (_, AbsP _) =>  true
      | (_, Abst _) =>  true
      | _ => false
  end;


(* rewrite proof *)

val no_skel = PBound 0;
val normal_skel = Hyp (Var ((Name.uu, 0), propT));

fun rewrite_prf tymatch (rules, procs) prf =
  let
    fun rew _ _ (Abst (_, _, body) % SOME t) = SOME (subst_bounds [t] body, no_skel)
      | rew _ _ (AbsP (_, _, body) %% prf) = SOME (subst_pbounds [prf] body, no_skel)
      | rew Ts hs prf =
          (case get_first (fn r => r Ts hs prf) procs of
            NONE => get_first (fn (prf1, prf2) => SOME (prf_subst
              (match_proof Ts tymatch ([], (Vartab.empty, [])) (prf1, prf)) prf2, prf2)
                 handle PMatch => NONE) (filter (fn (prf', _) => could_unify (prf, prf')) rules)
          | some => some);

    fun rew0 Ts hs (prf as AbsP (_, _, prf' %% PBound 0)) =
          if prf_loose_Pbvar1 prf' 0 then rew Ts hs prf
          else
            let val prf'' = incr_boundvars (~1) 0 prf'
            in SOME (the_default (prf'', no_skel) (rew Ts hs prf'')) end
      | rew0 Ts hs (prf as Abst (_, _, prf' % SOME (Bound 0))) =
          if prf_loose_bvar1 prf' 0 then rew Ts hs prf
          else
            let val prf'' = incr_boundvars 0 (~1) prf'
            in SOME (the_default (prf'', no_skel) (rew Ts hs prf'')) end
      | rew0 Ts hs prf = rew Ts hs prf;

    fun rew1 _ _ (Hyp (Var _)) _ = NONE
      | rew1 Ts hs skel prf =
          (case rew2 Ts hs skel prf of
            SOME prf1 =>
              (case rew0 Ts hs prf1 of
                SOME (prf2, skel') => SOME (the_default prf2 (rew1 Ts hs skel' prf2))
              | NONE => SOME prf1)
          | NONE =>
              (case rew0 Ts hs prf of
                SOME (prf1, skel') => SOME (the_default prf1 (rew1 Ts hs skel' prf1))
              | NONE => NONE))

    and rew2 Ts hs skel (prf % SOME t) =
          (case prf of
            Abst (_, _, body) =>
              let val prf' = subst_bounds [t] body
              in SOME (the_default prf' (rew2 Ts hs no_skel prf')) end
          | _ =>
              (case rew1 Ts hs (case skel of skel' % _ => skel' | _ => no_skel) prf of
                SOME prf' => SOME (prf' % SOME t)
              | NONE => NONE))
      | rew2 Ts hs skel (prf % NONE) = Option.map (fn prf' => prf' % NONE)
          (rew1 Ts hs (case skel of skel' % _ => skel' | _ => no_skel) prf)
      | rew2 Ts hs skel (prf1 %% prf2) =
          (case prf1 of
            AbsP (_, _, body) =>
              let val prf' = subst_pbounds [prf2] body
              in SOME (the_default prf' (rew2 Ts hs no_skel prf')) end
          | _ =>
            let
              val (skel1, skel2) =
                (case skel of
                  skel1 %% skel2 => (skel1, skel2)
                | _ => (no_skel, no_skel))
            in
              (case rew1 Ts hs skel1 prf1 of
                SOME prf1' =>
                  (case rew1 Ts hs skel2 prf2 of
                    SOME prf2' => SOME (prf1' %% prf2')
                  | NONE => SOME (prf1' %% prf2))
              | NONE =>
                  (case rew1 Ts hs skel2 prf2 of
                    SOME prf2' => SOME (prf1 %% prf2')
                  | NONE => NONE))
            end)
      | rew2 Ts hs skel (Abst (s, T, prf)) =
          (case rew1 (the_default dummyT T :: Ts) hs
              (case skel of Abst (_, _, skel') => skel' | _ => no_skel) prf of
            SOME prf' => SOME (Abst (s, T, prf'))
          | NONE => NONE)
      | rew2 Ts hs skel (AbsP (s, t, prf)) =
          (case rew1 Ts (t :: hs) (case skel of AbsP (_, _, skel') => skel' | _ => no_skel) prf of
            SOME prf' => SOME (AbsP (s, t, prf'))
          | NONE => NONE)
      | rew2 _ _ _ _ = NONE;

  in the_default prf (rew1 [] [] no_skel prf) end;

fun rewrite_proof thy = rewrite_prf (fn (tyenv, f) =>
  Sign.typ_match thy (f ()) tyenv handle Type.TYPE_MATCH => raise PMatch);

fun rewrite_proof_notypes rews = rewrite_prf fst rews;


(* theory data *)

structure Data = Theory_Data
(
  type T =
    ((stamp * (proof * proof)) list *
     (stamp * (typ list -> term option list -> proof -> (proof * proof) option)) list) *
    (theory -> proof -> proof) option;

  val empty = (([], []), NONE);
  fun merge (((rules1, procs1), preproc1), ((rules2, procs2), preproc2)) : T =
    ((AList.merge (op =) (K true) (rules1, rules2),
      AList.merge (op =) (K true) (procs1, procs2)),
      merge_options (preproc1, preproc2));
);

fun get_rew_data thy =
  let val (rules, procs) = #1 (Data.get thy)
  in (map #2 rules, map #2 procs) end;

fun rew_proof thy = rewrite_prf fst (get_rew_data thy);

fun add_prf_rrule r = (Data.map o apfst o apfst) (cons (stamp (), r));
fun add_prf_rproc p = (Data.map o apfst o apsnd) (cons (stamp (), p));

fun set_preproc f = (Data.map o apsnd) (K (SOME f));
fun apply_preproc thy = (case #2 (Data.get thy) of NONE => I | SOME f => f thy);



(** reconstruction of partial proof terms **)

fun forall_intr_variables_term prop = fold_rev Logic.all (variables_of prop) prop;
fun forall_intr_variables prop prf = fold_rev forall_intr_proof' (variables_of prop) prf;

local

fun app_types shift prop Ts prf =
  let
    val inst = type_variables_of prop ~~ Ts;
    fun subst_same A =
      (case AList.lookup (op =) inst A of SOME T => T | NONE => raise Same.SAME);
    val subst_type_same =
      Term.map_atyps_same
        (fn TVar ((a, i), S) => subst_same (TVar ((a, i - shift), S)) | A => subst_same A);
  in Same.commit (map_proof_types_same subst_type_same) prf end;

fun guess_name (PThm ({thm_name, ...}, _)) = thm_name
  | guess_name (prf %% Hyp _) = guess_name prf
  | guess_name (prf %% PClass _) = guess_name prf
  | guess_name (prf % NONE) = guess_name prf
  | guess_name (prf % SOME (Var _)) = guess_name prf
  | guess_name _ = Thm_Name.empty;


(* generate constraints for proof term *)

fun mk_var env Ts T =
  let val (env', v) = Envir.genvar "a" (env, rev Ts ---> T)
  in (list_comb (v, map Bound (length Ts - 1 downto 0)), env') end;

fun mk_tvar S (Envir.Envir {maxidx, tenv, tyenv}) =
  (TVar (("'t", maxidx + 1), S),
    Envir.Envir {maxidx = maxidx + 1, tenv = tenv, tyenv = tyenv});

val mk_abs = fold (fn T => fn u => Abs ("", T, u));

fun unifyT thy env T U =
  let
    val Envir.Envir {maxidx, tenv, tyenv} = env;
    val (tyenv', maxidx') = Sign.typ_unify thy (T, U) (tyenv, maxidx);
  in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end;

fun chaseT env (T as TVar v) =
      (case Type.lookup (Envir.type_env env) v of
        NONE => T
      | SOME T' => chaseT env T')
  | chaseT _ T = T;

fun infer_type thy (env as Envir.Envir {maxidx, tenv, tyenv}) _ vTs (t as Const (s, T)) =
      if T = dummyT then
        (case Sign.const_type thy s of
          NONE => error ("reconstruct_proof: No such constant: " ^ quote s)
        | SOME T =>
            let val T' = Term.strip_sortsT (Logic.incr_tvar (maxidx + 1) T) in
              (Const (s, T'), T', vTs,
                Envir.Envir {maxidx = maxidx + 1, tenv = tenv, tyenv = tyenv})
            end)
      else (t, T, vTs, env)
  | infer_type _ env _ vTs (t as Free (s, T)) =
      if T = dummyT then
        (case Symtab.lookup vTs s of
          NONE =>
            let val (T, env') = mk_tvar [] env
            in (Free (s, T), T, Symtab.update_new (s, T) vTs, env') end
        | SOME T => (Free (s, T), T, vTs, env))
      else (t, T, vTs, env)
  | infer_type _ _ _ _ (Var _) = error "reconstruct_proof: internal error"
  | infer_type thy env Ts vTs (Abs (s, T, t)) =
      let
        val (T', env') = if T = dummyT then mk_tvar [] env else (T, env);
        val (t', U, vTs', env'') = infer_type thy env' (T' :: Ts) vTs t
      in (Abs (s, T', t'), T' --> U, vTs', env'') end
  | infer_type thy env Ts vTs (t $ u) =
      let
        val (t', T, vTs1, env1) = infer_type thy env Ts vTs t;
        val (u', U, vTs2, env2) = infer_type thy env1 Ts vTs1 u;
      in
        (case chaseT env2 T of
          Type ("fun", [U', V]) => (t' $ u', V, vTs2, unifyT thy env2 U U')
        | _ =>
          let val (V, env3) = mk_tvar [] env2
          in (t' $ u', V, vTs2, unifyT thy env3 T (U --> V)) end)
      end
  | infer_type _ env Ts vTs (t as Bound i) = ((t, nth Ts i, vTs, env)
      handle General.Subscript => error ("infer_type: bad variable index " ^ string_of_int i));

fun cantunify thy (t, u) =
  error ("Non-unifiable terms:\n" ^
    Syntax.string_of_term_global thy t ^ "\n\n" ^ Syntax.string_of_term_global thy u);

fun decompose thy Ts (p as (t, u)) env =
  let
    fun rigrig (a, T) (b, U) uT ts us =
      if a <> b then cantunify thy p
      else apfst flat (fold_map (decompose thy Ts) (ts ~~ us) (uT env T U))
  in
    case apply2 (strip_comb o Envir.head_norm env) p of
      ((Const c, ts), (Const d, us)) => rigrig c d (unifyT thy) ts us
    | ((Free c, ts), (Free d, us)) => rigrig c d (unifyT thy) ts us
    | ((Bound i, ts), (Bound j, us)) =>
        rigrig (i, dummyT) (j, dummyT) (K o K) ts us
    | ((Abs (_, T, t), []), (Abs (_, U, u), [])) =>
        decompose thy (T::Ts) (t, u) (unifyT thy env T U)
    | ((Abs (_, T, t), []), _) =>
        decompose thy (T::Ts) (t, Term.incr_boundvars 1 u $ Bound 0) env
    | (_, (Abs (_, T, u), [])) =>
        decompose thy (T::Ts) (Term.incr_boundvars 1 t $ Bound 0, u) env
    | _ => ([(mk_abs Ts t, mk_abs Ts u)], env)
  end;

fun make_constraints_cprf thy env cprf =
  let
    fun add_cnstrt Ts prop prf cs env vTs (t, u) =
      let
        val t' = mk_abs Ts t;
        val u' = mk_abs Ts u
      in
        (prop, prf, cs, Pattern.unify (Context.Theory thy) (t', u') env, vTs)
          handle Pattern.Pattern =>
            let val (cs', env') = decompose thy [] (t', u') env
            in (prop, prf, cs @ cs', env', vTs) end
          | Pattern.Unif => cantunify thy (Envir.norm_term env t', Envir.norm_term env u')
      end;

    fun mk_cnstrts_atom env vTs prop opTs prf =
          let
            val prop_types = type_variables_of prop;
            val (Ts, env') =
              (case opTs of
                NONE => fold_map (mk_tvar o Type.sort_of_atyp) prop_types env
              | SOME Ts => (Ts, env));
            val prop' = subst_atomic_types (prop_types ~~ Ts)
              (forall_intr_variables_term prop) handle ListPair.UnequalLengths =>
                error ("Wrong number of type arguments for " ^ quote (Thm_Name.print (guess_name prf)))
          in (prop', change_types (SOME Ts) prf, [], env', vTs) end;

    fun head_norm (prop, prf, cnstrts, env, vTs) =
      (Envir.head_norm env prop, prf, cnstrts, env, vTs);

    fun mk_cnstrts env _ Hs vTs (PBound i) = ((nth Hs i, PBound i, [], env, vTs)
          handle General.Subscript => error ("mk_cnstrts: bad variable index " ^ string_of_int i))
      | mk_cnstrts env Ts Hs vTs (Abst (s, opT, cprf)) =
          let
            val (T, env') =
              (case opT of
                NONE => mk_tvar [] env
              | SOME T => (T, env));
            val (t, prf, cnstrts, env'', vTs') =
              mk_cnstrts env' (T::Ts) (map (Term.incr_boundvars 1) Hs) vTs cprf;
          in
            (Const ("Pure.all", (T --> propT) --> propT) $ Abs (s, T, t), Abst (s, SOME T, prf),
              cnstrts, env'', vTs')
          end
      | mk_cnstrts env Ts Hs vTs (AbsP (s, SOME t, cprf)) =
          let
            val (t', _, vTs', env') = infer_type thy env Ts vTs t;
            val (u, prf, cnstrts, env'', vTs'') = mk_cnstrts env' Ts (t'::Hs) vTs' cprf;
          in (Logic.mk_implies (t', u), AbsP (s, SOME t', prf), cnstrts, env'', vTs'')
          end
      | mk_cnstrts env Ts Hs vTs (AbsP (s, NONE, cprf)) =
          let
            val (t, env') = mk_var env Ts propT;
            val (u, prf, cnstrts, env'', vTs') = mk_cnstrts env' Ts (t::Hs) vTs cprf;
          in (Logic.mk_implies (t, u), AbsP (s, SOME t, prf), cnstrts, env'', vTs')
          end
      | mk_cnstrts env Ts Hs vTs (cprf1 %% cprf2) =
          let val (u, prf2, cnstrts, env', vTs') = mk_cnstrts env Ts Hs vTs cprf2
          in (case head_norm (mk_cnstrts env' Ts Hs vTs' cprf1) of
              (Const ("Pure.imp", _) $ u' $ t', prf1, cnstrts', env'', vTs'') =>
                add_cnstrt Ts t' (prf1 %% prf2) (cnstrts' @ cnstrts)
                  env'' vTs'' (u, u')
            | (t, prf1, cnstrts', env'', vTs'') =>
                let val (v, env''') = mk_var env'' Ts propT
                in add_cnstrt Ts v (prf1 %% prf2) (cnstrts' @ cnstrts)
                  env''' vTs'' (t, Logic.mk_implies (u, v))
                end)
          end
      | mk_cnstrts env Ts Hs vTs (cprf % SOME t) =
          let val (t', U, vTs1, env1) = infer_type thy env Ts vTs t
          in (case head_norm (mk_cnstrts env1 Ts Hs vTs1 cprf) of
             (Const ("Pure.all", Type ("fun", [Type ("fun", [T, _]), _])) $ f,
                 prf, cnstrts, env2, vTs2) =>
               let val env3 = unifyT thy env2 T U
               in (betapply (f, t'), prf % SOME t', cnstrts, env3, vTs2)
               end
           | (u, prf, cnstrts, env2, vTs2) =>
               let val (v, env3) = mk_var env2 Ts (U --> propT);
               in
                 add_cnstrt Ts (v $ t') (prf % SOME t') cnstrts env3 vTs2
                   (u, Const ("Pure.all", (U --> propT) --> propT) $ v)
               end)
          end
      | mk_cnstrts env Ts Hs vTs (cprf % NONE) =
          (case head_norm (mk_cnstrts env Ts Hs vTs cprf) of
             (Const ("Pure.all", Type ("fun", [Type ("fun", [T, _]), _])) $ f,
                 prf, cnstrts, env', vTs') =>
               let val (t, env'') = mk_var env' Ts T
               in (betapply (f, t), prf % SOME t, cnstrts, env'', vTs')
               end
           | (u, prf, cnstrts, env', vTs') =>
               let
                 val (T, env1) = mk_tvar [] env';
                 val (v, env2) = mk_var env1 Ts (T --> propT);
                 val (t, env3) = mk_var env2 Ts T
               in
                 add_cnstrt Ts (v $ t) (prf % SOME t) cnstrts env3 vTs'
                   (u, Const ("Pure.all", (T --> propT) --> propT) $ v)
               end)
      | mk_cnstrts env _ _ vTs (prf as PThm ({prop, types = opTs, ...}, _)) =
          mk_cnstrts_atom env vTs prop opTs prf
      | mk_cnstrts env _ _ vTs (prf as PAxm (_, prop, opTs)) =
          mk_cnstrts_atom env vTs prop opTs prf
      | mk_cnstrts env _ _ vTs (prf as PClass C) =
          mk_cnstrts_atom env vTs (Logic.mk_of_class C) NONE prf
      | mk_cnstrts env _ _ vTs (prf as Oracle (_, prop, opTs)) =
          mk_cnstrts_atom env vTs prop opTs prf
      | mk_cnstrts env _ _ vTs (Hyp t) = (t, Hyp t, [], env, vTs)
      | mk_cnstrts _ _ _ _ MinProof = raise MIN_PROOF ()
  in mk_cnstrts env [] [] Symtab.empty cprf end;


(* update list of free variables of constraints *)

fun upd_constrs env cs =
  let
    val tenv = Envir.term_env env;
    val tyenv = Envir.type_env env;
    val dom = []
      |> Vartab.fold (cons o #1) tenv
      |> Vartab.fold (cons o #1) tyenv;
    val vran = []
      |> Vartab.fold (Term.add_var_names o #2 o #2) tenv
      |> Vartab.fold (Term.add_tvar_namesT o #2 o #2) tyenv;
    fun check_cs [] = []
      | check_cs ((u, p, vs) :: ps) =
          let val vs' = subtract (op =) dom vs in
            if vs = vs' then (u, p, vs) :: check_cs ps
            else (true, p, fold (insert op =) vs' vran) :: check_cs ps
          end;
  in check_cs cs end;


(* solution of constraints *)

fun solve _ [] bigenv = bigenv
  | solve thy cs bigenv =
      let
        fun search _ [] =
              error ("Unsolvable constraints:\n" ^
                Pretty.string_of (Pretty.chunks (map (fn (_, p, _) =>
                  Pretty.item (Syntax.pretty_flexpair (Syntax.init_pretty_global thy)
                    (apply2 (Envir.norm_term bigenv) p))) cs)))
          | search env ((u, p as (t1, t2), vs)::ps) =
              if u then
                let
                  val tn1 = Envir.norm_term bigenv t1;
                  val tn2 = Envir.norm_term bigenv t2
                in
                  if Pattern.pattern tn1 andalso Pattern.pattern tn2 then
                    (Pattern.unify (Context.Theory thy) (tn1, tn2) env, ps)
                      handle Pattern.Unif => cantunify thy (tn1, tn2)
                  else
                    let val (cs', env') = decompose thy [] (tn1, tn2) env
                    in if cs' = [(tn1, tn2)] then
                         apsnd (cons (false, (tn1, tn2), vs)) (search env ps)
                       else search env' (map (fn q => (true, q, vs)) cs' @ ps)
                    end
                end
              else apsnd (cons (false, p, vs)) (search env ps);
        val Envir.Envir {maxidx, ...} = bigenv;
        val (env, cs') = search (Envir.empty maxidx) cs;
      in
        solve thy (upd_constrs env cs') (Envir.merge (bigenv, env))
      end;

in


(* reconstruction of proofs *)

fun reconstruct_proof thy prop cprf =
  let
    val (cprf' % SOME prop', thawf) = freeze_thaw_prf (cprf % SOME prop);
    val (t, prf, cs, env, _) = make_constraints_cprf thy
      (Envir.empty (maxidx_proof cprf ~1)) cprf';
    val cs' =
      map (apply2 (Envir.norm_term env)) ((t, prop') :: cs)
      |> map (fn p => (true, p, Term.add_var_names (#1 p) (Term.add_var_names (#2 p) [])));
    val env' = solve thy cs' env;
  in thawf (norm_proof env' prf) end handle MIN_PROOF () => MinProof;

fun prop_of_atom prop Ts =
  subst_atomic_types (type_variables_of prop ~~ Ts) (forall_intr_variables_term prop);

val head_norm = Envir.head_norm Envir.init;

fun prop_of0 Hs (PBound i) = nth Hs i
  | prop_of0 Hs (Abst (s, SOME T, prf)) =
      Logic.all_const T $ (Abs (s, T, prop_of0 Hs prf))
  | prop_of0 Hs (AbsP (_, SOME t, prf)) =
      Logic.mk_implies (t, prop_of0 (t :: Hs) prf)
  | prop_of0 Hs (prf % SOME t) = (case head_norm (prop_of0 Hs prf) of
      Const ("Pure.all", _) $ f => f $ t
    | _ => error "prop_of: all expected")
  | prop_of0 Hs (prf1 %% _) = (case head_norm (prop_of0 Hs prf1) of
      Const ("Pure.imp", _) $ _ $ Q => Q
    | _ => error "prop_of: ==> expected")
  | prop_of0 _ (Hyp t) = t
  | prop_of0 _ (PThm ({prop, types = SOME Ts, ...}, _)) = prop_of_atom prop Ts
  | prop_of0 _ (PAxm (_, prop, SOME Ts)) = prop_of_atom prop Ts
  | prop_of0 _ (PClass C) = Logic.mk_of_class C
  | prop_of0 _ (Oracle (_, prop, SOME Ts)) = prop_of_atom prop Ts
  | prop_of0 _ _ = error "prop_of: partial proof object";

val prop_of' = Envir.beta_eta_contract oo prop_of0;
val prop_of = prop_of' [];


(* expand and reconstruct subproofs *)

fun expand_name_empty (header: thm_header) =
  if Thm_Name.is_empty (#thm_name header) then SOME Thm_Name.empty else NONE;

fun expand_proof thy expand_name prf =
  let
    fun expand seen maxidx (AbsP (s, t, prf)) =
          let val (seen', maxidx', prf') = expand seen maxidx prf
          in (seen', maxidx', AbsP (s, t, prf')) end
      | expand seen maxidx (Abst (s, T, prf)) =
          let val (seen', maxidx', prf') = expand seen maxidx prf
          in (seen', maxidx', Abst (s, T, prf')) end
      | expand seen maxidx (prf1 %% prf2) =
          let
            val (seen', maxidx', prf1') = expand seen maxidx prf1;
            val (seen'', maxidx'', prf2') = expand seen' maxidx' prf2;
          in (seen'', maxidx'', prf1' %% prf2') end
      | expand seen maxidx (prf % t) =
          let val (seen', maxidx', prf') = expand seen maxidx prf
          in (seen', maxidx', prf' % t) end
      | expand seen maxidx (prf as PThm (header, thm_body)) =
          let val {serial, pos, theory_name, thm_name, prop, types} = header in
            (case expand_name header of
              SOME thm_name' =>
                if #1 thm_name' = "" andalso is_some types then
                  let
                    val (seen', maxidx', prf') =
                      (case Inttab.lookup seen serial of
                        NONE =>
                          let
                            val prf1 =
                              thm_body_proof_open thm_body
                              |> reconstruct_proof thy prop
                              |> forall_intr_variables prop;
                            val (seen1, maxidx1, prf2) = expand_init seen prf1
                            val seen2 = seen1 |> Inttab.update (serial, (maxidx1, prf2));
                          in (seen2, maxidx1, prf2) end
                      | SOME (maxidx1, prf1) => (seen, maxidx1, prf1));
                    val prf'' = prf'
                      |> incr_indexes (maxidx + 1) |> app_types (maxidx + 1) prop (the types);
                  in (seen', maxidx' + maxidx + 1, prf'') end
                else if thm_name' <> thm_name then
                  (seen, maxidx,
                    PThm (thm_header serial pos theory_name thm_name' prop types, thm_body))
                else (seen, maxidx, prf)
            | NONE => (seen, maxidx, prf))
          end
      | expand seen maxidx prf = (seen, maxidx, prf)
    and expand_init seen prf = expand seen (maxidx_proof prf ~1) prf;

  in #3 (expand_init Inttab.empty prf) end;

end;



(** promises **)

fun fulfill_norm_proof thy ps body0 =
  let
    val _ = consolidate_bodies (map #2 ps @ [body0]);
    val PBody {oracles = oracles0, thms = thms0, zboxes = zboxes0, zproof, proof = proof0} = body0;
    val oracles =
      unions_oracles
        (fold (fn (_, PBody {oracles, ...}) => not (null oracles) ? cons oracles) ps [oracles0]);
    val thms =
      unions_thms (fold (fn (_, PBody {thms, ...}) => not (null thms) ? cons thms) ps [thms0]);
    val zboxes =
      ZTerm.unions_zboxes
        (fold (fn (_, PBody {zboxes, ...}) => not (null zboxes) ? cons zboxes) ps [zboxes0]);
    val proof = rew_proof thy proof0;
  in
    PBody {oracles = oracles, thms = thms, zboxes = zboxes, zproof = zproof, proof = proof}
  end;

fun fulfill_proof_future thy promises (postproc: proof_body -> proof_body) body =
  let
    fun fulfill () =
      postproc (fulfill_norm_proof thy (map (apsnd Future.join) promises) (Future.join body));
  in
    if null promises then Future.map postproc body
    else if Future.is_finished body andalso length promises = 1 then
      Future.map (fn _ => fulfill ()) (snd (hd promises))
    else
      (singleton o Future.forks)
        {name = "Proofterm.fulfill_proof_future", group = NONE,
          deps = Future.task_of body :: map (Future.task_of o snd) promises, pri = 1,
          interrupts = true}
        fulfill
  end;



(** theorems **)

(* standardization of variables for export: only frees and named bounds *)

local

val declare_names_term = Term.declare_term_frees;
val declare_names_term' = fn SOME t => declare_names_term t | NONE => I;
val declare_names_proof = fold_proof_terms declare_names_term;

fun variant names bs x =
  #1 (Name.variant x (fold Name.declare bs names));

fun variant_term bs (Abs (x, T, t)) =
      let
        val x' = variant (declare_names_term t Name.context) bs x;
        val t' = variant_term (x' :: bs) t;
      in Abs (x', T, t') end
  | variant_term bs (t $ u) = variant_term bs t $ variant_term bs u
  | variant_term _ t = t;

fun variant_proof bs (Abst (x, T, prf)) =
      let
        val x' = variant (declare_names_proof prf Name.context) bs x;
        val prf' = variant_proof (x' :: bs) prf;
      in Abst (x', T, prf') end
  | variant_proof bs (AbsP (x, t, prf)) =
      let
        val x' = variant (declare_names_term' t (declare_names_proof prf Name.context)) bs x;
        val t' = Option.map (variant_term bs) t;
        val prf' = variant_proof (x' :: bs) prf;
      in AbsP (x', t', prf') end
  | variant_proof bs (prf % t) = variant_proof bs prf % Option.map (variant_term bs) t
  | variant_proof bs (prf1 %% prf2) = variant_proof bs prf1 %% variant_proof bs prf2
  | variant_proof bs (Hyp t) = Hyp (variant_term bs t)
  | variant_proof _ prf = prf;

val used_frees_type = fold_atyps (fn TFree (a, _) => Name.declare a | _ => I);
fun used_frees_term t = fold_types used_frees_type t #> Term.declare_term_frees t;
val used_frees_proof = fold_proof_terms_types used_frees_term used_frees_type;

val unvarifyT = Term.map_atyps (fn TVar ((a, _), S) => TFree (a, S) | T => T);
val unvarify = Term.map_aterms (fn Var ((x, _), T) => Free (x, T) | t => t) #> map_types unvarifyT;
val unvarify_proof = map_proof_terms unvarify unvarifyT;

fun hidden_types prop proof =
  let
    val visible = (fold_types o fold_atyps) (insert (op =)) prop [];
    val add_hiddenT = fold_atyps (fn T => not (member (op =) visible T) ? insert (op =) T);
  in rev (fold_proof_terms_types (fold_types add_hiddenT) add_hiddenT proof []) end;

fun standard_hidden_types term proof =
  let
    val hidden = hidden_types term proof;
    val idx = Term.maxidx_term term (maxidx_proof proof ~1) + 1;
    fun smash T =
      if member (op =) hidden T then
        (case Type.sort_of_atyp T of
          [] => dummyT
        | S => TVar (("'", idx), S))
      else T;
    val smashT = map_atyps smash;
  in map_proof_terms (map_types smashT) smashT proof end;

fun standard_hidden_terms term proof =
  let
    fun add_unless excluded x =
      ((is_Free x orelse is_Var x) andalso not (member (op =) excluded x)) ? insert (op =) x;
    val visible = fold_aterms (add_unless []) term [];
    val hidden = fold_proof_terms (fold_aterms (add_unless visible)) proof [];
    val dummy_term = Term.map_aterms (fn x =>
      if member (op =) hidden x then Term.dummy_pattern (Term.fastype_of x) else x);
  in proof |> not (null hidden) ? map_proof_terms dummy_term I end;

in

fun standard_vars used (term, opt_proof) =
  let
    val proofs = opt_proof
      |> Option.map (standard_hidden_types term #> standard_hidden_terms term) |> the_list;
    val proof_terms = rev (fold (fold_proof_terms_types cons (cons o Logic.mk_type)) proofs []);
    val used_frees = used
      |> used_frees_term term
      |> fold used_frees_proof proofs;
    val inst = Term_Subst.zero_var_indexes_inst used_frees (term :: proof_terms);
    val term' = term |> Term_Subst.instantiate inst |> unvarify |> variant_term [];
    val proofs' = proofs |> map (instantiate inst #> unvarify_proof #> variant_proof []);
  in (term', try hd proofs') end;

fun standard_vars_term used t = #1 (standard_vars used (t, NONE));

val add_standard_vars_term = fold_aterms
  (fn Free (x, T) =>
    (fn env =>
      (case AList.lookup (op =) env x of
        NONE => (x, T) :: env
      | SOME T' =>
          if T = T' then env
          else raise TYPE ("standard_vars_env: type conflict for variable " ^ quote x, [T, T'], [])))
    | _ => I);

val add_standard_vars = fold_proof_terms add_standard_vars_term;

end;


(* PThm nodes *)

fun prune_body body =
  if Options.default_bool "prune_proofs"
  then Future.map no_proof body
  else body;

fun export_enabled () = Options.default_bool "export_proofs";
fun export_standard_enabled () = Options.default_bool "export_standard_proofs";

fun export_proof_boxes_required thy =
  Context.theory_long_name thy = Context.PureN orelse
    (export_enabled () andalso not (export_standard_enabled ()));

fun export_proof_boxes bodies =
  let
    fun export_thm (i, thm_node) boxes =
      if Inttab.defined boxes i then boxes
      else
        boxes
        |> Inttab.update (i, thm_node_export thm_node)
        |> fold export_thm (thm_node_thms thm_node);

    fun export_body (PBody {thms, ...}) = fold export_thm thms;

    val exports = Inttab.build (fold export_body bodies) |> Inttab.dest;
  in List.app (Lazy.force o #2) exports end;

local

fun export_proof thy i prop prf =
  let
    val (prop', SOME prf') = (prop, SOME prf) |> standard_vars Name.context;
    val args = [] |> add_standard_vars_term prop' |> add_standard_vars prf' |> rev;
    val typargs = [] |> Term.add_tfrees prop' |> fold_proof_terms Term.add_tfrees prf' |> rev;

    val consts = Sign.consts_of thy;
    val xml = (typargs, (args, (prop', no_thm_names prf'))) |>
      let
        open XML.Encode Term_XML.Encode;
        val encode_vars = list (pair string typ);
        val encode_term = encode_standard_term consts;
        val encode_proof = encode_standard_proof consts;
      in pair (list (pair string sort)) (pair encode_vars (pair encode_term encode_proof)) end;
  in
    Export.export_params (Context.Theory thy)
     {theory_name = Context.theory_long_name thy,
      binding = Path.binding0 (Path.make ["proofs", string_of_int i]),
      executable = false,
      compress = true,
      strict = false} xml
  end;

fun prepare_thm_proof unconstrain thy sorts_proof
    (name, pos) shyps hyps concl promises
    (PBody {oracles = oracles0, thms = thms0, zboxes = zboxes0, zproof = zproof0, proof = proof0}) =
  let
    val named = not (Thm_Name.is_empty name);

    val prop = Logic.list_implies (hyps, concl);
    val args = prop_args prop;

    val (ucontext as {typ_operation, ...}, prop1) = Logic.unconstrainT shyps prop;

    val proofs = get_proofs_level ();
    val (zproof1, zboxes1) =
      if zproof_enabled proofs then
        ZTerm.add_box_proof {unconstrain = unconstrain} thy hyps concl zproof0 zboxes0
      else (ZNop, []);
    val proof1 =
      if proof_enabled proofs then fold_rev implies_intr_proof hyps proof0
      else MinProof;

    fun new_prf () =
      let
        val i = serial ();
        val unconstrainT = unconstrainT_proof (Sign.classes_of thy) sorts_proof ucontext;
        val postproc = map_proof_of (unconstrainT #> named ? rew_proof thy);
        val body1 =
          {oracles = oracles0, thms = thms0, zboxes = [], zproof = ZNop, proof = proof1};
      in (i, fulfill_proof_future thy promises postproc (Future.value (PBody body1))) end;

    val (i, body') =
      (*somewhat non-deterministic proof boxes!*)
      if export_enabled () then new_prf ()
      else
        (case strip_combt (proof_head_of proof0) of
          (PThm ({serial = ser, thm_name = a, prop = prop', types = NONE, ...}, thm_body'), args') =>
            if (#1 a = "" orelse a = name) andalso prop' = prop1 andalso args' = args then
              let
                val Thm_Body {body = body', ...} = thm_body';
                val i = if #1 a = "" andalso named then serial () else ser;
              in (i, body' |> ser <> i ? Future.map (map_proof_of (rew_proof thy))) end
            else new_prf ()
        | _ => new_prf ());

    val exp_proof = Future.map proof_of body';
    val open_proof = not named ? rew_proof thy;
    fun export_body () =
      Future.join exp_proof
      |> open_proof
      |> reconstruct_proof thy prop1
      |> apply_preproc thy
      |> export_proof thy i prop1;

    val export =
      if export_enabled () then
        Lazy.lazy (fn () =>
          (case Exn.capture_body export_body of
            Exn.Res res => res
          | Exn.Exn exn =>
              if Exn.is_interrupt_breakdown exn then
                raise Fail ("Resource problems while exporting proof " ^ string_of_int i)
              else Exn.reraise exn))
      else no_export;

    val thm_body = prune_body body';
    val theory_name = Context.theory_long_name thy;
    val thm = (i, make_thm_node theory_name name prop1 thm_body export);

    val header = thm_header i ([pos, Position.thread_data ()]) theory_name name prop1 NONE;
    val head = PThm (header, Thm_Body {open_proof = open_proof, body = thm_body});
    val argst =
      if unconstrain then
        (Same.commit o Same.map o Same.map_option o Term.map_types_same)
          (typ_operation {strip_sorts = true}) args
      else args;
    val argsP =
      if unconstrain then []
      else map PClass (#outer_constraints ucontext) @ map Hyp hyps;
    val proof2 = proof_combP (proof_combt' (head, argst), argsP);

    val body2 = {oracles = [], thms = [thm], zboxes = zboxes1, zproof = zproof1, proof = proof2};
  in (prop1, PBody body2) end;

in

fun thm_proof thy sorts_proof name shyps hyps concl promises =
  prepare_thm_proof false thy sorts_proof name shyps hyps concl promises #> #2;

fun unconstrain_thm_proof thy sorts_proof shyps concl promises body =
  prepare_thm_proof true thy sorts_proof Thm_Name.none
    shyps [] concl promises body;

end;


(* PThm identity *)

fun get_identity shyps hyps prop prf =
  let val (_, prop) = Logic.unconstrainT shyps (Logic.list_implies (hyps, prop)) in
    (case term_head_of (proof_head_of prf) of
      PThm ({serial, theory_name, thm_name, prop = prop', ...}, _) =>
        if prop = prop'
        then SOME {serial = serial, theory_name = theory_name, thm_name = thm_name} else NONE
    | _ => NONE)
  end;

fun get_approximative_name shyps hyps prop prf =
  Option.map #thm_name (get_identity shyps hyps prop prf) |> the_default Thm_Name.empty;


(* thm_id *)

type thm_id = {serial: serial, theory_name: string};

fun make_thm_id (serial, theory_name) : thm_id =
  {serial = serial, theory_name = theory_name};

fun thm_header_id ({serial, theory_name, ...}: thm_header) =
  make_thm_id (serial, theory_name);

fun thm_id (serial, thm_node) : thm_id =
  make_thm_id (serial, thm_node_theory_name thm_node);

fun get_id shyps hyps prop prf : thm_id option =
  (case get_identity shyps hyps prop prf of
    NONE => NONE
  | SOME {serial, theory_name, thm_name, ...} =>
      if Thm_Name.is_empty thm_name then NONE else SOME (make_thm_id (serial, theory_name)));

fun this_id NONE _ = false
  | this_id (SOME (thm_id: thm_id)) (thm_id': thm_id) = #serial thm_id = #serial thm_id';


(* proof boxes: intermediate PThm nodes *)

fun proof_boxes {included, excluded} proofs =
  let
    fun boxes_of (Abst (_, _, prf)) = boxes_of prf
      | boxes_of (AbsP (_, _, prf)) = boxes_of prf
      | boxes_of (prf % _) = boxes_of prf
      | boxes_of (prf1 %% prf2) = boxes_of prf1 #> boxes_of prf2
      | boxes_of (PThm (header as {serial = i, ...}, thm_body)) =
          (fn boxes =>
            let val thm_id = thm_header_id header in
              if Inttab.defined boxes i orelse (excluded thm_id andalso not (included thm_id))
              then boxes
              else
                let
                  val prf' = thm_body_proof_open thm_body;
                  val boxes' = Inttab.update (i, (header, prf')) boxes;
                in boxes_of prf' boxes' end
            end)
      | boxes_of MinProof = raise MIN_PROOF ()
      | boxes_of _ = I;
  in Inttab.fold_rev (cons o #2) (Inttab.build (fold boxes_of proofs)) [] end;

end;

structure Basic_Proofterm =
struct
  datatype proof = datatype Proofterm.proof
  datatype proof_body = datatype Proofterm.proof_body
  val op %> = Proofterm.%>
end;

open Basic_Proofterm;
