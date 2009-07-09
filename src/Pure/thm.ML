(*  Title:      Pure/thm.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

The very core of Isabelle's Meta Logic: certified types and terms,
derivations, theorems, framework rules (including lifting and
resolution), oracles.
*)

signature BASIC_THM =
  sig
  (*certified types*)
  type ctyp
  val rep_ctyp: ctyp ->
   {thy_ref: theory_ref,
    T: typ,
    maxidx: int,
    sorts: sort OrdList.T}
  val theory_of_ctyp: ctyp -> theory
  val typ_of: ctyp -> typ
  val ctyp_of: theory -> typ -> ctyp

  (*certified terms*)
  type cterm
  exception CTERM of string * cterm list
  val rep_cterm: cterm ->
   {thy_ref: theory_ref,
    t: term,
    T: typ,
    maxidx: int,
    sorts: sort OrdList.T}
  val crep_cterm: cterm ->
    {thy_ref: theory_ref, t: term, T: ctyp, maxidx: int, sorts: sort OrdList.T}
  val theory_of_cterm: cterm -> theory
  val term_of: cterm -> term
  val cterm_of: theory -> term -> cterm
  val ctyp_of_term: cterm -> ctyp

  (*theorems*)
  type thm
  type conv = cterm -> thm
  type attribute = Context.generic * thm -> Context.generic * thm
  val rep_thm: thm ->
   {thy_ref: theory_ref,
    tags: Properties.T,
    maxidx: int,
    shyps: sort OrdList.T,
    hyps: term OrdList.T,
    tpairs: (term * term) list,
    prop: term}
  val crep_thm: thm ->
   {thy_ref: theory_ref,
    tags: Properties.T,
    maxidx: int,
    shyps: sort OrdList.T,
    hyps: cterm OrdList.T,
    tpairs: (cterm * cterm) list,
    prop: cterm}
  exception THM of string * int * thm list
  val theory_of_thm: thm -> theory
  val prop_of: thm -> term
  val tpairs_of: thm -> (term * term) list
  val concl_of: thm -> term
  val prems_of: thm -> term list
  val nprems_of: thm -> int
  val cprop_of: thm -> cterm
  val cprem_of: thm -> int -> cterm
  val transfer: theory -> thm -> thm
  val weaken: cterm -> thm -> thm
  val weaken_sorts: sort list -> cterm -> cterm
  val extra_shyps: thm -> sort list
  val strip_shyps: thm -> thm

  (*meta rules*)
  val assume: cterm -> thm
  val implies_intr: cterm -> thm -> thm
  val implies_elim: thm -> thm -> thm
  val forall_intr: cterm -> thm -> thm
  val forall_elim: cterm -> thm -> thm
  val reflexive: cterm -> thm
  val symmetric: thm -> thm
  val transitive: thm -> thm -> thm
  val beta_conversion: bool -> conv
  val eta_conversion: conv
  val eta_long_conversion: conv
  val abstract_rule: string -> cterm -> thm -> thm
  val combination: thm -> thm -> thm
  val equal_intr: thm -> thm -> thm
  val equal_elim: thm -> thm -> thm
  val flexflex_rule: thm -> thm Seq.seq
  val generalize: string list * string list -> int -> thm -> thm
  val instantiate: (ctyp * ctyp) list * (cterm * cterm) list -> thm -> thm
  val instantiate_cterm: (ctyp * ctyp) list * (cterm * cterm) list -> cterm -> cterm
  val trivial: cterm -> thm
  val of_class: ctyp * class -> thm
  val unconstrainT: ctyp -> thm -> thm
  val dest_state: thm * int -> (term * term) list * term list * term * term
  val lift_rule: cterm -> thm -> thm
  val incr_indexes: int -> thm -> thm
end;

signature THM =
sig
  include BASIC_THM
  val dest_ctyp: ctyp -> ctyp list
  val dest_comb: cterm -> cterm * cterm
  val dest_fun: cterm -> cterm
  val dest_arg: cterm -> cterm
  val dest_fun2: cterm -> cterm
  val dest_arg1: cterm -> cterm
  val dest_abs: string option -> cterm -> cterm * cterm
  val capply: cterm -> cterm -> cterm
  val cabs: cterm -> cterm -> cterm
  val adjust_maxidx_cterm: int -> cterm -> cterm
  val incr_indexes_cterm: int -> cterm -> cterm
  val match: cterm * cterm -> (ctyp * ctyp) list * (cterm * cterm) list
  val first_order_match: cterm * cterm -> (ctyp * ctyp) list * (cterm * cterm) list
  val fold_terms: (term -> 'a -> 'a) -> thm -> 'a -> 'a
  val terms_of_tpairs: (term * term) list -> term list
  val full_prop_of: thm -> term
  val maxidx_of: thm -> int
  val maxidx_thm: thm -> int -> int
  val hyps_of: thm -> term list
  val no_prems: thm -> bool
  val major_prem_of: thm -> term
  val axiom: theory -> string -> thm
  val axioms_of: theory -> (string * thm) list
  val get_tags: thm -> Properties.T
  val map_tags: (Properties.T -> Properties.T) -> thm -> thm
  val norm_proof: thm -> thm
  val adjust_maxidx_thm: int -> thm -> thm
  val varifyT: thm -> thm
  val varifyT': (string * sort) list -> thm -> ((string * sort) * indexname) list * thm
  val freezeT: thm -> thm
  val assumption: int -> thm -> thm Seq.seq
  val eq_assumption: int -> thm -> thm
  val rotate_rule: int -> int -> thm -> thm
  val permute_prems: int -> int -> thm -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val compose_no_flatten: bool -> thm * int -> int -> thm -> thm Seq.seq
  val bicompose: bool -> bool * thm * int -> int -> thm -> thm Seq.seq
  val biresolution: bool -> (bool * thm) list -> int -> thm -> thm Seq.seq
  val rename_boundvars: term -> term -> thm -> thm
  val future: thm future -> cterm -> thm
  val pending_groups: thm -> Task_Queue.group list -> Task_Queue.group list
  val status_of: thm -> {oracle: bool, unfinished: bool, failed: bool}
  val proof_body_of: thm -> proof_body
  val proof_of: thm -> proof
  val join_proof: thm -> unit
  val get_name: thm -> string
  val put_name: string -> thm -> thm
  val extern_oracles: theory -> xstring list
  val add_oracle: binding * ('a -> cterm) -> theory -> (string * ('a -> thm)) * theory
end;

structure Thm:> THM =
struct

structure Pt = Proofterm;


(*** Certified terms and types ***)

(** certified types **)

datatype ctyp = Ctyp of
 {thy_ref: theory_ref,
  T: typ,
  maxidx: int,
  sorts: sort OrdList.T};

fun rep_ctyp (Ctyp args) = args;
fun theory_of_ctyp (Ctyp {thy_ref, ...}) = Theory.deref thy_ref;
fun typ_of (Ctyp {T, ...}) = T;

fun ctyp_of thy raw_T =
  let
    val T = Sign.certify_typ thy raw_T;
    val maxidx = Term.maxidx_of_typ T;
    val sorts = Sorts.insert_typ T [];
  in Ctyp {thy_ref = Theory.check_thy thy, T = T, maxidx = maxidx, sorts = sorts} end;

fun dest_ctyp (Ctyp {thy_ref, T = Type (s, Ts), maxidx, sorts}) =
      map (fn T => Ctyp {thy_ref = thy_ref, T = T, maxidx = maxidx, sorts = sorts}) Ts
  | dest_ctyp cT = raise TYPE ("dest_ctyp", [typ_of cT], []);



(** certified terms **)

(*certified terms with checked typ, maxidx, and sorts*)
datatype cterm = Cterm of
 {thy_ref: theory_ref,
  t: term,
  T: typ,
  maxidx: int,
  sorts: sort OrdList.T};

exception CTERM of string * cterm list;

fun rep_cterm (Cterm args) = args;

fun crep_cterm (Cterm {thy_ref, t, T, maxidx, sorts}) =
  {thy_ref = thy_ref, t = t, maxidx = maxidx, sorts = sorts,
    T = Ctyp {thy_ref = thy_ref, T = T, maxidx = maxidx, sorts = sorts}};

fun theory_of_cterm (Cterm {thy_ref, ...}) = Theory.deref thy_ref;
fun term_of (Cterm {t, ...}) = t;

fun ctyp_of_term (Cterm {thy_ref, T, maxidx, sorts, ...}) =
  Ctyp {thy_ref = thy_ref, T = T, maxidx = maxidx, sorts = sorts};

fun cterm_of thy tm =
  let
    val (t, T, maxidx) = Sign.certify_term thy tm;
    val sorts = Sorts.insert_term t [];
  in Cterm {thy_ref = Theory.check_thy thy, t = t, T = T, maxidx = maxidx, sorts = sorts} end;

fun merge_thys0 (Cterm {thy_ref = r1, t = t1, ...}) (Cterm {thy_ref = r2, t = t2, ...}) =
  Theory.merge_refs (r1, r2);


(* destructors *)

fun dest_comb (ct as Cterm {t = c $ a, T, thy_ref, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0 in
        (Cterm {t = c, T = A --> T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts},
         Cterm {t = a, T = A, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts})
      end
  | dest_comb ct = raise CTERM ("dest_comb", [ct]);

fun dest_fun (ct as Cterm {t = c $ _, T, thy_ref, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0
      in Cterm {t = c, T = A --> T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts} end
  | dest_fun ct = raise CTERM ("dest_fun", [ct]);

fun dest_arg (ct as Cterm {t = c $ a, T = _, thy_ref, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0
      in Cterm {t = a, T = A, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts} end
  | dest_arg ct = raise CTERM ("dest_arg", [ct]);


fun dest_fun2 (Cterm {t = c $ a $ b, T, thy_ref, maxidx, sorts}) =
      let
        val A = Term.argument_type_of c 0;
        val B = Term.argument_type_of c 1;
      in Cterm {t = c, T = A --> B --> T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts} end
  | dest_fun2 ct = raise CTERM ("dest_fun2", [ct]);

fun dest_arg1 (Cterm {t = c $ a $ _, T = _, thy_ref, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0
      in Cterm {t = a, T = A, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts} end
  | dest_arg1 ct = raise CTERM ("dest_arg1", [ct]);

fun dest_abs a (ct as
        Cterm {t = Abs (x, T, t), T = Type ("fun", [_, U]), thy_ref, maxidx, sorts}) =
      let val (y', t') = Term.dest_abs (the_default x a, T, t) in
        (Cterm {t = Free (y', T), T = T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts},
          Cterm {t = t', T = U, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts})
      end
  | dest_abs _ ct = raise CTERM ("dest_abs", [ct]);


(* constructors *)

fun capply
  (cf as Cterm {t = f, T = Type ("fun", [dty, rty]), maxidx = maxidx1, sorts = sorts1, ...})
  (cx as Cterm {t = x, T, maxidx = maxidx2, sorts = sorts2, ...}) =
    if T = dty then
      Cterm {thy_ref = merge_thys0 cf cx,
        t = f $ x,
        T = rty,
        maxidx = Int.max (maxidx1, maxidx2),
        sorts = Sorts.union sorts1 sorts2}
      else raise CTERM ("capply: types don't agree", [cf, cx])
  | capply cf cx = raise CTERM ("capply: first arg is not a function", [cf, cx]);

fun cabs
  (ct1 as Cterm {t = t1, T = T1, maxidx = maxidx1, sorts = sorts1, ...})
  (ct2 as Cterm {t = t2, T = T2, maxidx = maxidx2, sorts = sorts2, ...}) =
    let val t = Term.lambda t1 t2 in
      Cterm {thy_ref = merge_thys0 ct1 ct2,
        t = t, T = T1 --> T2,
        maxidx = Int.max (maxidx1, maxidx2),
        sorts = Sorts.union sorts1 sorts2}
    end;


(* indexes *)

fun adjust_maxidx_cterm i (ct as Cterm {thy_ref, t, T, maxidx, sorts}) =
  if maxidx = i then ct
  else if maxidx < i then
    Cterm {maxidx = i, thy_ref = thy_ref, t = t, T = T, sorts = sorts}
  else
    Cterm {maxidx = Int.max (maxidx_of_term t, i), thy_ref = thy_ref, t = t, T = T, sorts = sorts};

fun incr_indexes_cterm i (ct as Cterm {thy_ref, t, T, maxidx, sorts}) =
  if i < 0 then raise CTERM ("negative increment", [ct])
  else if i = 0 then ct
  else Cterm {thy_ref = thy_ref, t = Logic.incr_indexes ([], i) t,
    T = Logic.incr_tvar i T, maxidx = maxidx + i, sorts = sorts};


(* matching *)

local

fun gen_match match
    (ct1 as Cterm {t = t1, sorts = sorts1, ...},
     ct2 as Cterm {t = t2, sorts = sorts2, maxidx = maxidx2, ...}) =
  let
    val thy = Theory.deref (merge_thys0 ct1 ct2);
    val (Tinsts, tinsts) = match thy (t1, t2) (Vartab.empty, Vartab.empty);
    val sorts = Sorts.union sorts1 sorts2;
    fun mk_cTinst ((a, i), (S, T)) =
      (Ctyp {T = TVar ((a, i), S), thy_ref = Theory.check_thy thy, maxidx = i, sorts = sorts},
       Ctyp {T = T, thy_ref = Theory.check_thy thy, maxidx = maxidx2, sorts = sorts});
    fun mk_ctinst ((x, i), (T, t)) =
      let val T = Envir.typ_subst_TVars Tinsts T in
        (Cterm {t = Var ((x, i), T), T = T, thy_ref = Theory.check_thy thy,
          maxidx = i, sorts = sorts},
         Cterm {t = t, T = T, thy_ref = Theory.check_thy thy, maxidx = maxidx2, sorts = sorts})
      end;
  in (Vartab.fold (cons o mk_cTinst) Tinsts [], Vartab.fold (cons o mk_ctinst) tinsts []) end;

in

val match = gen_match Pattern.match;
val first_order_match = gen_match Pattern.first_order_match;

end;



(*** Derivations and Theorems ***)

datatype thm = Thm of
 deriv *                                        (*derivation*)
 {thy_ref: theory_ref,                          (*dynamic reference to theory*)
  tags: Properties.T,                           (*additional annotations/comments*)
  maxidx: int,                                  (*maximum index of any Var or TVar*)
  shyps: sort OrdList.T,                        (*sort hypotheses*)
  hyps: term OrdList.T,                         (*hypotheses*)
  tpairs: (term * term) list,                   (*flex-flex pairs*)
  prop: term}                                   (*conclusion*)
and deriv = Deriv of
 {max_promise: serial,
  open_promises: (serial * thm future) OrdList.T,
  promises: (serial * thm future) OrdList.T,
  body: Pt.proof_body};

type conv = cterm -> thm;

(*attributes subsume any kind of rules or context modifiers*)
type attribute = Context.generic * thm -> Context.generic * thm;

(*errors involving theorems*)
exception THM of string * int * thm list;

fun rep_thm (Thm (_, args)) = args;

fun crep_thm (Thm (_, {thy_ref, tags, maxidx, shyps, hyps, tpairs, prop})) =
  let fun cterm max t = Cterm {thy_ref = thy_ref, t = t, T = propT, maxidx = max, sorts = shyps} in
   {thy_ref = thy_ref, tags = tags, maxidx = maxidx, shyps = shyps,
    hyps = map (cterm ~1) hyps,
    tpairs = map (pairself (cterm maxidx)) tpairs,
    prop = cterm maxidx prop}
  end;

fun fold_terms f (Thm (_, {tpairs, prop, hyps, ...})) =
  fold (fn (t, u) => f t #> f u) tpairs #> f prop #> fold f hyps;

fun terms_of_tpairs tpairs = fold_rev (fn (t, u) => cons t o cons u) tpairs [];

fun eq_tpairs ((t, u), (t', u')) = t aconv t' andalso u aconv u';
fun union_tpairs ts us = Library.merge eq_tpairs (ts, us);
val maxidx_tpairs = fold (fn (t, u) => Term.maxidx_term t #> Term.maxidx_term u);

fun attach_tpairs tpairs prop =
  Logic.list_implies (map Logic.mk_equals tpairs, prop);

fun full_prop_of (Thm (_, {tpairs, prop, ...})) = attach_tpairs tpairs prop;

val union_hyps = OrdList.union TermOrd.fast_term_ord;
val insert_hyps = OrdList.insert TermOrd.fast_term_ord;
val remove_hyps = OrdList.remove TermOrd.fast_term_ord;


(* merge theories of cterms/thms -- trivial absorption only *)

fun merge_thys1 (Cterm {thy_ref = r1, ...}) (th as Thm (_, {thy_ref = r2, ...})) =
  Theory.merge_refs (r1, r2);

fun merge_thys2 (th1 as Thm (_, {thy_ref = r1, ...})) (th2 as Thm (_, {thy_ref = r2, ...})) =
  Theory.merge_refs (r1, r2);


(* basic components *)

val theory_of_thm = Theory.deref o #thy_ref o rep_thm;
val maxidx_of = #maxidx o rep_thm;
fun maxidx_thm th i = Int.max (maxidx_of th, i);
val hyps_of = #hyps o rep_thm;
val prop_of = #prop o rep_thm;
val tpairs_of = #tpairs o rep_thm;

val concl_of = Logic.strip_imp_concl o prop_of;
val prems_of = Logic.strip_imp_prems o prop_of;
val nprems_of = Logic.count_prems o prop_of;
fun no_prems th = nprems_of th = 0;

fun major_prem_of th =
  (case prems_of th of
    prem :: _ => Logic.strip_assums_concl prem
  | [] => raise THM ("major_prem_of: rule with no premises", 0, [th]));

(*the statement of any thm is a cterm*)
fun cprop_of (Thm (_, {thy_ref, maxidx, shyps, prop, ...})) =
  Cterm {thy_ref = thy_ref, maxidx = maxidx, T = propT, t = prop, sorts = shyps};

fun cprem_of (th as Thm (_, {thy_ref, maxidx, shyps, prop, ...})) i =
  Cterm {thy_ref = thy_ref, maxidx = maxidx, T = propT, sorts = shyps,
    t = Logic.nth_prem (i, prop) handle TERM _ => raise THM ("cprem_of", i, [th])};

(*explicit transfer to a super theory*)
fun transfer thy' thm =
  let
    val Thm (der, {thy_ref, tags, maxidx, shyps, hyps, tpairs, prop}) = thm;
    val thy = Theory.deref thy_ref;
    val _ = Theory.subthy (thy, thy') orelse raise THM ("transfer: not a super theory", 0, [thm]);
    val is_eq = Theory.eq_thy (thy, thy');
    val _ = Theory.check_thy thy;
  in
    if is_eq then thm
    else
      Thm (der,
       {thy_ref = Theory.check_thy thy',
        tags = tags,
        maxidx = maxidx,
        shyps = shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = prop})
  end;

(*explicit weakening: maps |- B to A |- B*)
fun weaken raw_ct th =
  let
    val ct as Cterm {t = A, T, sorts, maxidx = maxidxA, ...} = adjust_maxidx_cterm ~1 raw_ct;
    val Thm (der, {tags, maxidx, shyps, hyps, tpairs, prop, ...}) = th;
  in
    if T <> propT then
      raise THM ("weaken: assumptions must have type prop", 0, [])
    else if maxidxA <> ~1 then
      raise THM ("weaken: assumptions may not contain schematic variables", maxidxA, [])
    else
      Thm (der,
       {thy_ref = merge_thys1 ct th,
        tags = tags,
        maxidx = maxidx,
        shyps = Sorts.union sorts shyps,
        hyps = insert_hyps A hyps,
        tpairs = tpairs,
        prop = prop})
  end;

fun weaken_sorts raw_sorts ct =
  let
    val Cterm {thy_ref, t, T, maxidx, sorts} = ct;
    val thy = Theory.deref thy_ref;
    val more_sorts = Sorts.make (map (Sign.certify_sort thy) raw_sorts);
    val sorts' = Sorts.union sorts more_sorts;
  in Cterm {thy_ref = Theory.check_thy thy, t = t, T = T, maxidx = maxidx, sorts = sorts'} end;



(** sort contexts of theorems **)

(*remove extra sorts that are witnessed by type signature information*)
fun strip_shyps (thm as Thm (_, {shyps = [], ...})) = thm
  | strip_shyps (thm as Thm (der, {thy_ref, tags, maxidx, shyps, hyps, tpairs, prop})) =
      let
        val thy = Theory.deref thy_ref;
        val present =
          (fold_terms o fold_types o fold_atyps)
            (fn T as TFree (_, S) => insert (eq_snd op =) (T, S)
              | T as TVar (_, S) => insert (eq_snd op =) (T, S)) thm [];
        val extra = fold (Sorts.remove_sort o #2) present shyps;
        val witnessed = Sign.witness_sorts thy present extra;
        val extra' = fold (Sorts.remove_sort o #2) witnessed extra
          |> Sorts.minimal_sorts (Sign.classes_of thy);
        val shyps' = fold (Sorts.insert_sort o #2) present extra';
      in
        Thm (der, {thy_ref = Theory.check_thy thy, tags = tags, maxidx = maxidx,
          shyps = shyps', hyps = hyps, tpairs = tpairs, prop = prop})
      end;

(*dangling sort constraints of a thm*)
fun extra_shyps (th as Thm (_, {shyps, ...})) =
  Sorts.subtract (fold_terms Sorts.insert_term th []) shyps;



(** derivations **)

fun make_deriv max_promise open_promises promises oracles thms proof =
  Deriv {max_promise = max_promise, open_promises = open_promises, promises = promises,
    body = PBody {oracles = oracles, thms = thms, proof = proof}};

val empty_deriv = make_deriv ~1 [] [] [] [] Pt.MinProof;


(* inference rules *)

fun promise_ord ((i, _), (j, _)) = int_ord (j, i);

fun deriv_rule2 f
    (Deriv {max_promise = max1, open_promises = open_ps1, promises = ps1,
      body = PBody {oracles = oras1, thms = thms1, proof = prf1}})
    (Deriv {max_promise = max2, open_promises = open_ps2, promises = ps2,
      body = PBody {oracles = oras2, thms = thms2, proof = prf2}}) =
  let
    val max = Int.max (max1, max2);
    val open_ps = OrdList.union promise_ord open_ps1 open_ps2;
    val ps = OrdList.union promise_ord ps1 ps2;
    val oras = Pt.merge_oracles oras1 oras2;
    val thms = Pt.merge_thms thms1 thms2;
    val prf =
      (case ! Pt.proofs of
        2 => f prf1 prf2
      | 1 => MinProof
      | 0 => MinProof
      | i => error ("Illegal level of detail for proof objects: " ^ string_of_int i));
  in make_deriv max open_ps ps oras thms prf end;

fun deriv_rule1 f = deriv_rule2 (K f) empty_deriv;
fun deriv_rule0 prf = deriv_rule1 I (make_deriv ~1 [] [] [] [] prf);



(** Axioms **)

fun axiom theory name =
  let
    fun get_ax thy =
      Symtab.lookup (Theory.axiom_table thy) name
      |> Option.map (fn prop =>
           let
             val der = deriv_rule0 (Pt.axm_proof name prop);
             val maxidx = maxidx_of_term prop;
             val shyps = Sorts.insert_term prop [];
           in
             Thm (der, {thy_ref = Theory.check_thy thy, tags = [],
               maxidx = maxidx, shyps = shyps, hyps = [], tpairs = [], prop = prop})
           end);
  in
    (case get_first get_ax (theory :: Theory.ancestors_of theory) of
      SOME thm => thm
    | NONE => raise THEORY ("No axiom " ^ quote name, [theory]))
  end;

(*return additional axioms of this theory node*)
fun axioms_of thy =
  map (fn s => (s, axiom thy s)) (Symtab.keys (Theory.axiom_table thy));


(* tags *)

val get_tags = #tags o rep_thm;

fun map_tags f (Thm (der, {thy_ref, tags, maxidx, shyps, hyps, tpairs, prop})) =
  Thm (der, {thy_ref = thy_ref, tags = f tags, maxidx = maxidx,
    shyps = shyps, hyps = hyps, tpairs = tpairs, prop = prop});


fun norm_proof (Thm (der, args as {thy_ref, ...})) =
  let
    val thy = Theory.deref thy_ref;
    val der' = deriv_rule1 (Pt.rew_proof thy) der;
    val _ = Theory.check_thy thy;
  in Thm (der', args) end;

fun adjust_maxidx_thm i (th as Thm (der, {thy_ref, tags, maxidx, shyps, hyps, tpairs, prop})) =
  if maxidx = i then th
  else if maxidx < i then
    Thm (der, {maxidx = i, thy_ref = thy_ref, tags = tags, shyps = shyps,
      hyps = hyps, tpairs = tpairs, prop = prop})
  else
    Thm (der, {maxidx = Int.max (maxidx_tpairs tpairs (maxidx_of_term prop), i), thy_ref = thy_ref,
      tags = tags, shyps = shyps, hyps = hyps, tpairs = tpairs, prop = prop});



(*** Meta rules ***)

(** primitive rules **)

(*The assumption rule A |- A*)
fun assume raw_ct =
  let val Cterm {thy_ref, t = prop, T, maxidx, sorts} = adjust_maxidx_cterm ~1 raw_ct in
    if T <> propT then
      raise THM ("assume: prop", 0, [])
    else if maxidx <> ~1 then
      raise THM ("assume: variables", maxidx, [])
    else Thm (deriv_rule0 (Pt.Hyp prop),
     {thy_ref = thy_ref,
      tags = [],
      maxidx = ~1,
      shyps = sorts,
      hyps = [prop],
      tpairs = [],
      prop = prop})
  end;

(*Implication introduction
    [A]
     :
     B
  -------
  A ==> B
*)
fun implies_intr
    (ct as Cterm {t = A, T, maxidx = maxidxA, sorts, ...})
    (th as Thm (der, {maxidx, hyps, shyps, tpairs, prop, ...})) =
  if T <> propT then
    raise THM ("implies_intr: assumptions must have type prop", 0, [th])
  else
    Thm (deriv_rule1 (Pt.implies_intr_proof A) der,
     {thy_ref = merge_thys1 ct th,
      tags = [],
      maxidx = Int.max (maxidxA, maxidx),
      shyps = Sorts.union sorts shyps,
      hyps = remove_hyps A hyps,
      tpairs = tpairs,
      prop = Logic.mk_implies (A, prop)});


(*Implication elimination
  A ==> B    A
  ------------
        B
*)
fun implies_elim thAB thA =
  let
    val Thm (derA, {maxidx = maxA, hyps = hypsA, shyps = shypsA, tpairs = tpairsA,
      prop = propA, ...}) = thA
    and Thm (der, {maxidx, hyps, shyps, tpairs, prop, ...}) = thAB;
    fun err () = raise THM ("implies_elim: major premise", 0, [thAB, thA]);
  in
    case prop of
      Const ("==>", _) $ A $ B =>
        if A aconv propA then
          Thm (deriv_rule2 (curry Pt.%%) der derA,
           {thy_ref = merge_thys2 thAB thA,
            tags = [],
            maxidx = Int.max (maxA, maxidx),
            shyps = Sorts.union shypsA shyps,
            hyps = union_hyps hypsA hyps,
            tpairs = union_tpairs tpairsA tpairs,
            prop = B})
        else err ()
    | _ => err ()
  end;

(*Forall introduction.  The Free or Var x must not be free in the hypotheses.
    [x]
     :
     A
  ------
  !!x. A
*)
fun forall_intr
    (ct as Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {maxidx, shyps, hyps, tpairs, prop, ...})) =
  let
    fun result a =
      Thm (deriv_rule1 (Pt.forall_intr_proof x a) der,
       {thy_ref = merge_thys1 ct th,
        tags = [],
        maxidx = maxidx,
        shyps = Sorts.union sorts shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = Term.all T $ Abs (a, T, abstract_over (x, prop))});
    fun check_occs a x ts =
      if exists (fn t => Logic.occs (x, t)) ts then
        raise THM ("forall_intr: variable " ^ quote a ^ " free in assumptions", 0, [th])
      else ();
  in
    case x of
      Free (a, _) => (check_occs a x hyps; check_occs a x (terms_of_tpairs tpairs); result a)
    | Var ((a, _), _) => (check_occs a x (terms_of_tpairs tpairs); result a)
    | _ => raise THM ("forall_intr: not a variable", 0, [th])
  end;

(*Forall elimination
  !!x. A
  ------
  A[t/x]
*)
fun forall_elim
    (ct as Cterm {t, T, maxidx = maxt, sorts, ...})
    (th as Thm (der, {maxidx, shyps, hyps, tpairs, prop, ...})) =
  (case prop of
    Const ("all", Type ("fun", [Type ("fun", [qary, _]), _])) $ A =>
      if T <> qary then
        raise THM ("forall_elim: type mismatch", 0, [th])
      else
        Thm (deriv_rule1 (Pt.% o rpair (SOME t)) der,
         {thy_ref = merge_thys1 ct th,
          tags = [],
          maxidx = Int.max (maxidx, maxt),
          shyps = Sorts.union sorts shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = Term.betapply (A, t)})
  | _ => raise THM ("forall_elim: not quantified", 0, [th]));


(* Equality *)

(*Reflexivity
  t == t
*)
fun reflexive (ct as Cterm {thy_ref, t, T, maxidx, sorts}) =
  Thm (deriv_rule0 Pt.reflexive,
   {thy_ref = thy_ref,
    tags = [],
    maxidx = maxidx,
    shyps = sorts,
    hyps = [],
    tpairs = [],
    prop = Logic.mk_equals (t, t)});

(*Symmetry
  t == u
  ------
  u == t
*)
fun symmetric (th as Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...})) =
  (case prop of
    (eq as Const ("==", Type (_, [T, _]))) $ t $ u =>
      Thm (deriv_rule1 Pt.symmetric der,
       {thy_ref = thy_ref,
        tags = [],
        maxidx = maxidx,
        shyps = shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = eq $ u $ t})
    | _ => raise THM ("symmetric", 0, [th]));

(*Transitivity
  t1 == u    u == t2
  ------------------
       t1 == t2
*)
fun transitive th1 th2 =
  let
    val Thm (der1, {maxidx = max1, hyps = hyps1, shyps = shyps1, tpairs = tpairs1,
      prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = max2, hyps = hyps2, shyps = shyps2, tpairs = tpairs2,
      prop = prop2, ...}) = th2;
    fun err msg = raise THM ("transitive: " ^ msg, 0, [th1, th2]);
  in
    case (prop1, prop2) of
      ((eq as Const ("==", Type (_, [T, _]))) $ t1 $ u, Const ("==", _) $ u' $ t2) =>
        if not (u aconv u') then err "middle term"
        else
          Thm (deriv_rule2 (Pt.transitive u T) der1 der2,
           {thy_ref = merge_thys2 th1 th2,
            tags = [],
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = eq $ t1 $ t2})
     | _ =>  err "premises"
  end;

(*Beta-conversion
  (%x. t)(u) == t[u/x]
  fully beta-reduces the term if full = true
*)
fun beta_conversion full (Cterm {thy_ref, t, T, maxidx, sorts}) =
  let val t' =
    if full then Envir.beta_norm t
    else
      (case t of Abs (_, _, bodt) $ u => subst_bound (u, bodt)
      | _ => raise THM ("beta_conversion: not a redex", 0, []));
  in
    Thm (deriv_rule0 Pt.reflexive,
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx,
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_equals (t, t')})
  end;

fun eta_conversion (Cterm {thy_ref, t, T, maxidx, sorts}) =
  Thm (deriv_rule0 Pt.reflexive,
   {thy_ref = thy_ref,
    tags = [],
    maxidx = maxidx,
    shyps = sorts,
    hyps = [],
    tpairs = [],
    prop = Logic.mk_equals (t, Envir.eta_contract t)});

fun eta_long_conversion (Cterm {thy_ref, t, T, maxidx, sorts}) =
  Thm (deriv_rule0 Pt.reflexive,
   {thy_ref = thy_ref,
    tags = [],
    maxidx = maxidx,
    shyps = sorts,
    hyps = [],
    tpairs = [],
    prop = Logic.mk_equals (t, Pattern.eta_long [] t)});

(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.
  The bound variable will be named "a" (since x will be something like x320)
      t == u
  --------------
  %x. t == %x. u
*)
fun abstract_rule a
    (Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {thy_ref, maxidx, hyps, shyps, tpairs, prop, ...})) =
  let
    val (t, u) = Logic.dest_equals prop
      handle TERM _ => raise THM ("abstract_rule: premise not an equality", 0, [th]);
    val result =
      Thm (deriv_rule1 (Pt.abstract_rule x a) der,
       {thy_ref = thy_ref,
        tags = [],
        maxidx = maxidx,
        shyps = Sorts.union sorts shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = Logic.mk_equals
          (Abs (a, T, abstract_over (x, t)), Abs (a, T, abstract_over (x, u)))});
    fun check_occs a x ts =
      if exists (fn t => Logic.occs (x, t)) ts then
        raise THM ("abstract_rule: variable " ^ quote a ^ " free in assumptions", 0, [th])
      else ();
  in
    case x of
      Free (a, _) => (check_occs a x hyps; check_occs a x (terms_of_tpairs tpairs); result)
    | Var ((a, _), _) => (check_occs a x (terms_of_tpairs tpairs); result)
    | _ => raise THM ("abstract_rule: not a variable", 0, [th])
  end;

(*The combination rule
  f == g  t == u
  --------------
    f t == g u
*)
fun combination th1 th2 =
  let
    val Thm (der1, {maxidx = max1, shyps = shyps1, hyps = hyps1, tpairs = tpairs1,
      prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = max2, shyps = shyps2, hyps = hyps2, tpairs = tpairs2,
      prop = prop2, ...}) = th2;
    fun chktypes fT tT =
      (case fT of
        Type ("fun", [T1, T2]) =>
          if T1 <> tT then
            raise THM ("combination: types", 0, [th1, th2])
          else ()
      | _ => raise THM ("combination: not function type", 0, [th1, th2]));
  in
    case (prop1, prop2) of
      (Const ("==", Type ("fun", [fT, _])) $ f $ g,
       Const ("==", Type ("fun", [tT, _])) $ t $ u) =>
        (chktypes fT tT;
          Thm (deriv_rule2 (Pt.combination f g t u fT) der1 der2,
           {thy_ref = merge_thys2 th1 th2,
            tags = [],
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = Logic.mk_equals (f $ t, g $ u)}))
     | _ => raise THM ("combination: premises", 0, [th1, th2])
  end;

(*Equality introduction
  A ==> B  B ==> A
  ----------------
       A == B
*)
fun equal_intr th1 th2 =
  let
    val Thm (der1, {maxidx = max1, shyps = shyps1, hyps = hyps1, tpairs = tpairs1,
      prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = max2, shyps = shyps2, hyps = hyps2, tpairs = tpairs2,
      prop = prop2, ...}) = th2;
    fun err msg = raise THM ("equal_intr: " ^ msg, 0, [th1, th2]);
  in
    case (prop1, prop2) of
      (Const("==>", _) $ A $ B, Const("==>", _) $ B' $ A') =>
        if A aconv A' andalso B aconv B' then
          Thm (deriv_rule2 (Pt.equal_intr A B) der1 der2,
           {thy_ref = merge_thys2 th1 th2,
            tags = [],
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = Logic.mk_equals (A, B)})
        else err "not equal"
    | _ =>  err "premises"
  end;

(*The equal propositions rule
  A == B  A
  ---------
      B
*)
fun equal_elim th1 th2 =
  let
    val Thm (der1, {maxidx = max1, shyps = shyps1, hyps = hyps1,
      tpairs = tpairs1, prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = max2, shyps = shyps2, hyps = hyps2,
      tpairs = tpairs2, prop = prop2, ...}) = th2;
    fun err msg = raise THM ("equal_elim: " ^ msg, 0, [th1, th2]);
  in
    case prop1 of
      Const ("==", _) $ A $ B =>
        if prop2 aconv A then
          Thm (deriv_rule2 (Pt.equal_elim A B) der1 der2,
           {thy_ref = merge_thys2 th1 th2,
            tags = [],
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = B})
        else err "not equal"
     | _ =>  err"major premise"
  end;



(**** Derived rules ****)

(*Smash unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.  Resulting
  sequence may contain multiple elements if the tpairs are not all
  flex-flex.*)
fun flexflex_rule (th as Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...})) =
  let val thy = Theory.deref thy_ref in
    Unify.smash_unifiers thy tpairs (Envir.empty maxidx)
    |> Seq.map (fn env =>
        if Envir.is_empty env then th
        else
          let
            val tpairs' = tpairs |> map (pairself (Envir.norm_term env))
              (*remove trivial tpairs, of the form t==t*)
              |> filter_out (op aconv);
            val der' = deriv_rule1 (Pt.norm_proof' env) der;
            val prop' = Envir.norm_term env prop;
            val maxidx = maxidx_tpairs tpairs' (maxidx_of_term prop');
            val shyps = Envir.insert_sorts env shyps;
          in
            Thm (der', {thy_ref = Theory.check_thy thy, tags = [], maxidx = maxidx,
              shyps = shyps, hyps = hyps, tpairs = tpairs', prop = prop'})
          end)
  end;


(*Generalization of fixed variables
           A
  --------------------
  A[?'a/'a, ?x/x, ...]
*)

fun generalize ([], []) _ th = th
  | generalize (tfrees, frees) idx th =
      let
        val Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...}) = th;
        val _ = idx <= maxidx andalso raise THM ("generalize: bad index", idx, [th]);

        val bad_type = if null tfrees then K false else
          Term.exists_subtype (fn TFree (a, _) => member (op =) tfrees a | _ => false);
        fun bad_term (Free (x, T)) = bad_type T orelse member (op =) frees x
          | bad_term (Var (_, T)) = bad_type T
          | bad_term (Const (_, T)) = bad_type T
          | bad_term (Abs (_, T, t)) = bad_type T orelse bad_term t
          | bad_term (t $ u) = bad_term t orelse bad_term u
          | bad_term (Bound _) = false;
        val _ = exists bad_term hyps andalso
          raise THM ("generalize: variable free in assumptions", 0, [th]);

        val gen = Term_Subst.generalize (tfrees, frees) idx;
        val prop' = gen prop;
        val tpairs' = map (pairself gen) tpairs;
        val maxidx' = maxidx_tpairs tpairs' (maxidx_of_term prop');
      in
        Thm (deriv_rule1 (Pt.generalize (tfrees, frees) idx) der,
         {thy_ref = thy_ref,
          tags = [],
          maxidx = maxidx',
          shyps = shyps,
          hyps = hyps,
          tpairs = tpairs',
          prop = prop'})
      end;


(*Instantiation of schematic variables
           A
  --------------------
  A[t1/v1, ..., tn/vn]
*)

local

fun pretty_typing thy t T = Pretty.block
  [Syntax.pretty_term_global thy t, Pretty.str " ::", Pretty.brk 1, Syntax.pretty_typ_global thy T];

fun add_inst (ct, cu) (thy_ref, sorts) =
  let
    val Cterm {t = t, T = T, ...} = ct;
    val Cterm {t = u, T = U, sorts = sorts_u, maxidx = maxidx_u, ...} = cu;
    val thy_ref' = Theory.merge_refs (thy_ref, merge_thys0 ct cu);
    val sorts' = Sorts.union sorts_u sorts;
  in
    (case t of Var v =>
      if T = U then ((v, (u, maxidx_u)), (thy_ref', sorts'))
      else raise TYPE (Pretty.string_of (Pretty.block
       [Pretty.str "instantiate: type conflict",
        Pretty.fbrk, pretty_typing (Theory.deref thy_ref') t T,
        Pretty.fbrk, pretty_typing (Theory.deref thy_ref') u U]), [T, U], [t, u])
    | _ => raise TYPE (Pretty.string_of (Pretty.block
       [Pretty.str "instantiate: not a variable",
        Pretty.fbrk, Syntax.pretty_term_global (Theory.deref thy_ref') t]), [], [t]))
  end;

fun add_instT (cT, cU) (thy_ref, sorts) =
  let
    val Ctyp {T, thy_ref = thy_ref1, ...} = cT
    and Ctyp {T = U, thy_ref = thy_ref2, sorts = sorts_U, maxidx = maxidx_U, ...} = cU;
    val thy' = Theory.deref (Theory.merge_refs (thy_ref, Theory.merge_refs (thy_ref1, thy_ref2)));
    val sorts' = Sorts.union sorts_U sorts;
  in
    (case T of TVar (v as (_, S)) =>
      if Sign.of_sort thy' (U, S) then ((v, (U, maxidx_U)), (Theory.check_thy thy', sorts'))
      else raise TYPE ("Type not of sort " ^ Syntax.string_of_sort_global thy' S, [U], [])
    | _ => raise TYPE (Pretty.string_of (Pretty.block
        [Pretty.str "instantiate: not a type variable",
         Pretty.fbrk, Syntax.pretty_typ_global thy' T]), [T], []))
  end;

in

(*Left-to-right replacements: ctpairs = [..., (vi, ti), ...].
  Instantiates distinct Vars by terms of same type.
  Does NOT normalize the resulting theorem!*)
fun instantiate ([], []) th = th
  | instantiate (instT, inst) th =
      let
        val Thm (der, {thy_ref, hyps, shyps, tpairs, prop, ...}) = th;
        val (inst', (instT', (thy_ref', shyps'))) =
          (thy_ref, shyps) |> fold_map add_inst inst ||> fold_map add_instT instT;
        val subst = Term_Subst.instantiate_maxidx (instT', inst');
        val (prop', maxidx1) = subst prop ~1;
        val (tpairs', maxidx') =
          fold_map (fn (t, u) => fn i => subst t i ||>> subst u) tpairs maxidx1;
      in
        Thm (deriv_rule1 (fn d => Pt.instantiate (map (apsnd #1) instT', map (apsnd #1) inst') d) der,
         {thy_ref = thy_ref',
          tags = [],
          maxidx = maxidx',
          shyps = shyps',
          hyps = hyps,
          tpairs = tpairs',
          prop = prop'})
      end
      handle TYPE (msg, _, _) => raise THM (msg, 0, [th]);

fun instantiate_cterm ([], []) ct = ct
  | instantiate_cterm (instT, inst) ct =
      let
        val Cterm {thy_ref, t, T, sorts, ...} = ct;
        val (inst', (instT', (thy_ref', sorts'))) =
          (thy_ref, sorts) |> fold_map add_inst inst ||> fold_map add_instT instT;
        val subst = Term_Subst.instantiate_maxidx (instT', inst');
        val substT = Term_Subst.instantiateT_maxidx instT';
        val (t', maxidx1) = subst t ~1;
        val (T', maxidx') = substT T maxidx1;
      in Cterm {thy_ref = thy_ref', t = t', T = T', sorts = sorts', maxidx = maxidx'} end
      handle TYPE (msg, _, _) => raise CTERM (msg, [ct]);

end;


(*The trivial implication A ==> A, justified by assume and forall rules.
  A can contain Vars, not so for assume!*)
fun trivial (Cterm {thy_ref, t =A, T, maxidx, sorts}) =
  if T <> propT then
    raise THM ("trivial: the term must have type prop", 0, [])
  else
    Thm (deriv_rule0 (Pt.AbsP ("H", NONE, Pt.PBound 0)),
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx,
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_implies (A, A)});

(*Axiom-scheme reflecting signature contents
        T :: c
  -------------------
  OFCLASS(T, c_class)
*)
fun of_class (cT, raw_c) =
  let
    val Ctyp {thy_ref, T, ...} = cT;
    val thy = Theory.deref thy_ref;
    val c = Sign.certify_class thy raw_c;
    val Cterm {t = prop, maxidx, sorts, ...} = cterm_of thy (Logic.mk_of_class (T, c));
  in
    if Sign.of_sort thy (T, [c]) then
      Thm (deriv_rule0 (Pt.OfClass (T, c)),
       {thy_ref = Theory.check_thy thy,
        tags = [],
        maxidx = maxidx,
        shyps = sorts,
        hyps = [],
        tpairs = [],
        prop = prop})
    else raise THM ("of_class: type not of class " ^ Syntax.string_of_sort_global thy [c], 0, [])
  end;

(*Internalize sort constraints of type variable*)
fun unconstrainT
    (Ctyp {thy_ref = thy_ref1, T, ...})
    (th as Thm (_, {thy_ref = thy_ref2, maxidx, shyps, hyps, tpairs, prop, ...})) =
  let
    val ((x, i), S) = Term.dest_TVar T handle TYPE _ =>
      raise THM ("unconstrainT: not a type variable", 0, [th]);
    val T' = TVar ((x, i), []);
    val unconstrain = Term.map_types (Term.map_atyps (fn U => if U = T then T' else U));
    val constraints = map (curry Logic.mk_of_class T') S;
  in
    Thm (deriv_rule0 (Pt.PAxm ("Pure.unconstrainT", prop, SOME [])),
     {thy_ref = Theory.merge_refs (thy_ref1, thy_ref2),
      tags = [],
      maxidx = Int.max (maxidx, i),
      shyps = Sorts.remove_sort S shyps,
      hyps = hyps,
      tpairs = map (pairself unconstrain) tpairs,
      prop = Logic.list_implies (constraints, unconstrain prop)})
  end;

(* Replace all TFrees not fixed or in the hyps by new TVars *)
fun varifyT' fixed (Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...})) =
  let
    val tfrees = fold Term.add_tfrees hyps fixed;
    val prop1 = attach_tpairs tpairs prop;
    val (al, prop2) = Type.varify tfrees prop1;
    val (ts, prop3) = Logic.strip_prems (length tpairs, [], prop2);
  in
    (al, Thm (deriv_rule1 (Pt.varify_proof prop tfrees) der,
     {thy_ref = thy_ref,
      tags = [],
      maxidx = Int.max (0, maxidx),
      shyps = shyps,
      hyps = hyps,
      tpairs = rev (map Logic.dest_equals ts),
      prop = prop3}))
  end;

val varifyT = #2 o varifyT' [];

(* Replace all TVars by new TFrees *)
fun freezeT (Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...})) =
  let
    val prop1 = attach_tpairs tpairs prop;
    val prop2 = Type.freeze prop1;
    val (ts, prop3) = Logic.strip_prems (length tpairs, [], prop2);
  in
    Thm (deriv_rule1 (Pt.freezeT prop1) der,
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx_of_term prop2,
      shyps = shyps,
      hyps = hyps,
      tpairs = rev (map Logic.dest_equals ts),
      prop = prop3})
  end;


(*** Inference rules for tactics ***)

(*Destruct proof state into constraints, other goals, goal(i), rest *)
fun dest_state (state as Thm (_, {prop,tpairs,...}), i) =
  (case  Logic.strip_prems(i, [], prop) of
      (B::rBs, C) => (tpairs, rev rBs, B, C)
    | _ => raise THM("dest_state", i, [state]))
  handle TERM _ => raise THM("dest_state", i, [state]);

(*Increment variables and parameters of orule as required for
  resolution with a goal.*)
fun lift_rule goal orule =
  let
    val Cterm {t = gprop, T, maxidx = gmax, sorts, ...} = goal;
    val inc = gmax + 1;
    val lift_abs = Logic.lift_abs inc gprop;
    val lift_all = Logic.lift_all inc gprop;
    val Thm (der, {maxidx, shyps, hyps, tpairs, prop, ...}) = orule;
    val (As, B) = Logic.strip_horn prop;
  in
    if T <> propT then raise THM ("lift_rule: the term must have type prop", 0, [])
    else
      Thm (deriv_rule1 (Pt.lift_proof gprop inc prop) der,
       {thy_ref = merge_thys1 goal orule,
        tags = [],
        maxidx = maxidx + inc,
        shyps = Sorts.union shyps sorts,  (*sic!*)
        hyps = hyps,
        tpairs = map (pairself lift_abs) tpairs,
        prop = Logic.list_implies (map lift_all As, lift_all B)})
  end;

fun incr_indexes i (thm as Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...})) =
  if i < 0 then raise THM ("negative increment", 0, [thm])
  else if i = 0 then thm
  else
    Thm (deriv_rule1 (Pt.map_proof_terms (Logic.incr_indexes ([], i)) (Logic.incr_tvar i)) der,
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx + i,
      shyps = shyps,
      hyps = hyps,
      tpairs = map (pairself (Logic.incr_indexes ([], i))) tpairs,
      prop = Logic.incr_indexes ([], i) prop});

(*Solve subgoal Bi of proof state B1...Bn/C by assumption. *)
fun assumption i state =
  let
    val Thm (der, {thy_ref, maxidx, shyps, hyps, prop, ...}) = state;
    val thy = Theory.deref thy_ref;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    fun newth n (env as Envir.Envir {maxidx, ...}, tpairs) =
      Thm (deriv_rule1
          ((if Envir.is_empty env then I else (Pt.norm_proof' env)) o
            Pt.assumption_proof Bs Bi n) der,
       {tags = [],
        maxidx = maxidx,
        shyps = Envir.insert_sorts env shyps,
        hyps = hyps,
        tpairs =
          if Envir.is_empty env then tpairs
          else map (pairself (Envir.norm_term env)) tpairs,
        prop =
          if Envir.is_empty env then (*avoid wasted normalizations*)
            Logic.list_implies (Bs, C)
          else (*normalize the new rule fully*)
            Envir.norm_term env (Logic.list_implies (Bs, C)),
        thy_ref = Theory.check_thy thy});

    val (close, asms, concl) = Logic.assum_problems (~1, Bi);
    val concl' = close concl;
    fun addprfs [] _ = Seq.empty
      | addprfs (asm :: rest) n = Seq.make (fn () => Seq.pull
          (Seq.mapp (newth n)
            (if Term.could_unify (asm, concl) then
              (Unify.unifiers (thy, Envir.empty maxidx, (close asm, concl') :: tpairs))
             else Seq.empty)
            (addprfs rest (n + 1))))
  in addprfs asms 1 end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha-convertible to one of its assumptions*)
fun eq_assumption i state =
  let
    val Thm (der, {thy_ref, maxidx, shyps, hyps, prop, ...}) = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    val (_, asms, concl) = Logic.assum_problems (~1, Bi);
  in
    (case find_index (fn asm => Pattern.aeconv (asm, concl)) asms of
      ~1 => raise THM ("eq_assumption", 0, [state])
    | n =>
        Thm (deriv_rule1 (Pt.assumption_proof Bs Bi (n + 1)) der,
         {thy_ref = thy_ref,
          tags = [],
          maxidx = maxidx,
          shyps = shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = Logic.list_implies (Bs, C)}))
  end;


(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let
    val Thm (der, {thy_ref, maxidx, shyps, hyps, prop, ...}) = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    val params = Term.strip_all_vars Bi
    and rest   = Term.strip_all_body Bi;
    val asms   = Logic.strip_imp_prems rest
    and concl  = Logic.strip_imp_concl rest;
    val n = length asms;
    val m = if k < 0 then n + k else k;
    val Bi' =
      if 0 = m orelse m = n then Bi
      else if 0 < m andalso m < n then
        let val (ps, qs) = chop m asms
        in list_all (params, Logic.list_implies (qs @ ps, concl)) end
      else raise THM ("rotate_rule", k, [state]);
  in
    Thm (deriv_rule1 (Pt.rotate_proof Bs Bi m) der,
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx,
      shyps = shyps,
      hyps = hyps,
      tpairs = tpairs,
      prop = Logic.list_implies (Bs @ [Bi'], C)})
  end;


(*Rotates a rule's premises to the left by k, leaving the first j premises
  unchanged.  Does nothing if k=0 or if k equals n-j, where n is the
  number of premises.  Useful with etac and underlies defer_tac*)
fun permute_prems j k rl =
  let
    val Thm (der, {thy_ref, maxidx, shyps, hyps, tpairs, prop, ...}) = rl;
    val prems = Logic.strip_imp_prems prop
    and concl = Logic.strip_imp_concl prop;
    val moved_prems = List.drop (prems, j)
    and fixed_prems = List.take (prems, j)
      handle Subscript => raise THM ("permute_prems: j", j, [rl]);
    val n_j = length moved_prems;
    val m = if k < 0 then n_j + k else k;
    val prop' =
      if 0 = m orelse m = n_j then prop
      else if 0 < m andalso m < n_j then
        let val (ps, qs) = chop m moved_prems
        in Logic.list_implies (fixed_prems @ qs @ ps, concl) end
      else raise THM ("permute_prems: k", k, [rl]);
  in
    Thm (deriv_rule1 (Pt.permute_prems_prf prems j m) der,
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx,
      shyps = shyps,
      hyps = hyps,
      tpairs = tpairs,
      prop = prop'})
  end;


(** User renaming of parameters in a subgoal **)

(*Calls error rather than raising an exception because it is intended
  for top-level use -- exception handling would not make sense here.
  The names in cs, if distinct, are used for the innermost parameters;
  preceding parameters may be renamed to make all params distinct.*)
fun rename_params_rule (cs, i) state =
  let
    val Thm (der, {thy_ref, tags, maxidx, shyps, hyps, ...}) = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    val iparams = map #1 (Logic.strip_params Bi);
    val short = length iparams - length cs;
    val newnames =
      if short < 0 then error "More names than abstractions!"
      else Name.variant_list cs (Library.take (short, iparams)) @ cs;
    val freenames = Term.fold_aterms (fn Free (x, _) => insert (op =) x | _ => I) Bi [];
    val newBi = Logic.list_rename_params (newnames, Bi);
  in
    (case duplicates (op =) cs of
      a :: _ => (warning ("Can't rename.  Bound variables not distinct: " ^ a); state)
    | [] =>
      (case cs inter_string freenames of
        a :: _ => (warning ("Can't rename.  Bound/Free variable clash: " ^ a); state)
      | [] =>
        Thm (der,
         {thy_ref = thy_ref,
          tags = tags,
          maxidx = maxidx,
          shyps = shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = Logic.list_implies (Bs @ [newBi], C)})))
  end;


(*** Preservation of bound variable names ***)

fun rename_boundvars pat obj (thm as Thm (der, {thy_ref, tags, maxidx, shyps, hyps, tpairs, prop})) =
  (case Term.rename_abs pat obj prop of
    NONE => thm
  | SOME prop' => Thm (der,
      {thy_ref = thy_ref,
       tags = tags,
       maxidx = maxidx,
       hyps = hyps,
       shyps = shyps,
       tpairs = tpairs,
       prop = prop'}));


(* strip_apply f (A, B) strips off all assumptions/parameters from A
   introduced by lifting over B, and applies f to remaining part of A*)
fun strip_apply f =
  let fun strip(Const("==>",_)$ A1 $ B1,
                Const("==>",_)$ _  $ B2) = Logic.mk_implies (A1, strip(B1,B2))
        | strip((c as Const("all",_)) $ Abs(a,T,t1),
                      Const("all",_)  $ Abs(_,_,t2)) = c$Abs(a,T,strip(t1,t2))
        | strip(A,_) = f A
  in strip end;

(*Use the alist to rename all bound variables and some unknowns in a term
  dpairs = current disagreement pairs;  tpairs = permanent ones (flexflex);
  Preserves unknowns in tpairs and on lhs of dpairs. *)
fun rename_bvs([],_,_,_) = I
  | rename_bvs(al,dpairs,tpairs,B) =
      let
        val add_var = fold_aterms (fn Var ((x, _), _) => insert (op =) x | _ => I);
        val vids = []
          |> fold (add_var o fst) dpairs
          |> fold (add_var o fst) tpairs
          |> fold (add_var o snd) tpairs;
        (*unknowns appearing elsewhere be preserved!*)
        fun rename(t as Var((x,i),T)) =
              (case AList.lookup (op =) al x of
                SOME y =>
                  if member (op =) vids x orelse member (op =) vids y then t
                  else Var((y,i),T)
              | NONE=> t)
          | rename(Abs(x,T,t)) =
              Abs (the_default x (AList.lookup (op =) al x), T, rename t)
          | rename(f$t) = rename f $ rename t
          | rename(t) = t;
        fun strip_ren Ai = strip_apply rename (Ai,B)
      in strip_ren end;

(*Function to rename bounds/unknowns in the argument, lifted over B*)
fun rename_bvars(dpairs, tpairs, B) =
        rename_bvs(List.foldr Term.match_bvars [] dpairs, dpairs, tpairs, B);


(*** RESOLUTION ***)

(** Lifting optimizations **)

(*strip off pairs of assumptions/parameters in parallel -- they are
  identical because of lifting*)
fun strip_assums2 (Const("==>", _) $ _ $ B1,
                   Const("==>", _) $ _ $ B2) = strip_assums2 (B1,B2)
  | strip_assums2 (Const("all",_)$Abs(a,T,t1),
                   Const("all",_)$Abs(_,_,t2)) =
      let val (B1,B2) = strip_assums2 (t1,t2)
      in  (Abs(a,T,B1), Abs(a,T,B2))  end
  | strip_assums2 BB = BB;


(*Faster normalization: skip assumptions that were lifted over*)
fun norm_term_skip env 0 t = Envir.norm_term env t
  | norm_term_skip env n (Const("all",_)$Abs(a,T,t)) =
        let val Envir.Envir{iTs, ...} = env
            val T' = Envir.typ_subst_TVars iTs T
            (*Must instantiate types of parameters because they are flattened;
              this could be a NEW parameter*)
        in Term.all T' $ Abs(a, T', norm_term_skip env n t)  end
  | norm_term_skip env n (Const("==>", _) $ A $ B) =
        Logic.mk_implies (A, norm_term_skip env (n-1) B)
  | norm_term_skip env n t = error"norm_term_skip: too few assumptions??";


(*Composition of object rule r=(A1...Am/B) with proof state s=(B1...Bn/C)
  Unifies B with Bi, replacing subgoal i    (1 <= i <= n)
  If match then forbid instantiations in proof state
  If lifted then shorten the dpair using strip_assums2.
  If eres_flg then simultaneously proves A1 by assumption.
  nsubgoal is the number of new subgoals (written m above).
  Curried so that resolution calls dest_state only once.
*)
local exception COMPOSE
in
fun bicompose_aux flatten match (state, (stpairs, Bs, Bi, C), lifted)
                        (eres_flg, orule, nsubgoal) =
 let val Thm (sder, {maxidx=smax, shyps=sshyps, hyps=shyps, ...}) = state
     and Thm (rder, {maxidx=rmax, shyps=rshyps, hyps=rhyps,
             tpairs=rtpairs, prop=rprop,...}) = orule
         (*How many hyps to skip over during normalization*)
     and nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0)
     val thy = Theory.deref (merge_thys2 state orule);
     (** Add new theorem with prop = '[| Bs; As |] ==> C' to thq **)
     fun addth A (As, oldAs, rder', n) ((env as Envir.Envir {maxidx, ...}, tpairs), thq) =
       let val normt = Envir.norm_term env;
           (*perform minimal copying here by examining env*)
           val (ntpairs, normp) =
             if Envir.is_empty env then (tpairs, (Bs @ As, C))
             else
             let val ntps = map (pairself normt) tpairs
             in if Envir.above env smax then
                  (*no assignments in state; normalize the rule only*)
                  if lifted
                  then (ntps, (Bs @ map (norm_term_skip env nlift) As, C))
                  else (ntps, (Bs @ map normt As, C))
                else if match then raise COMPOSE
                else (*normalize the new rule fully*)
                  (ntps, (map normt (Bs @ As), normt C))
             end
           val th =
             Thm (deriv_rule2
                   ((if Envir.is_empty env then I
                     else if Envir.above env smax then
                       (fn f => fn der => f (Pt.norm_proof' env der))
                     else
                       curry op oo (Pt.norm_proof' env))
                    (Pt.bicompose_proof flatten Bs oldAs As A n (nlift+1))) rder' sder,
                {tags = [],
                 maxidx = maxidx,
                 shyps = Envir.insert_sorts env (Sorts.union rshyps sshyps),
                 hyps = union_hyps rhyps shyps,
                 tpairs = ntpairs,
                 prop = Logic.list_implies normp,
                 thy_ref = Theory.check_thy thy})
        in  Seq.cons th thq  end  handle COMPOSE => thq;
     val (rAs,B) = Logic.strip_prems(nsubgoal, [], rprop)
       handle TERM _ => raise THM("bicompose: rule", 0, [orule,state]);
     (*Modify assumptions, deleting n-th if n>0 for e-resolution*)
     fun newAs(As0, n, dpairs, tpairs) =
       let val (As1, rder') =
         if not lifted then (As0, rder)
         else (map (rename_bvars(dpairs,tpairs,B)) As0,
           deriv_rule1 (Pt.map_proof_terms
             (rename_bvars (dpairs, tpairs, Bound 0)) I) rder);
       in (map (if flatten then (Logic.flatten_params n) else I) As1, As1, rder', n)
          handle TERM _ =>
          raise THM("bicompose: 1st premise", 0, [orule])
       end;
     val env = Envir.empty(Int.max(rmax,smax));
     val BBi = if lifted then strip_assums2(B,Bi) else (B,Bi);
     val dpairs = BBi :: (rtpairs@stpairs);

     (*elim-resolution: try each assumption in turn*)
     fun eres [] = raise THM ("bicompose: no premises", 0, [orule, state])
       | eres (A1 :: As) =
           let
             val A = SOME A1;
             val (close, asms, concl) = Logic.assum_problems (nlift + 1, A1);
             val concl' = close concl;
             fun tryasms [] _ = Seq.empty
               | tryasms (asm :: rest) n =
                   if Term.could_unify (asm, concl) then
                     let val asm' = close asm in
                       (case Seq.pull (Unify.unifiers (thy, env, (asm', concl') :: dpairs)) of
                         NONE => tryasms rest (n + 1)
                       | cell as SOME ((_, tpairs), _) =>
                           Seq.it_right (addth A (newAs (As, n, [BBi, (concl', asm')], tpairs)))
                             (Seq.make (fn () => cell),
                              Seq.make (fn () => Seq.pull (tryasms rest (n + 1)))))
                     end
                   else tryasms rest (n + 1);
           in tryasms asms 1 end;

     (*ordinary resolution*)
     fun res () =
       (case Seq.pull (Unify.unifiers (thy, env, dpairs)) of
         NONE => Seq.empty
       | cell as SOME ((_, tpairs), _) =>
           Seq.it_right (addth NONE (newAs (rev rAs, 0, [BBi], tpairs)))
             (Seq.make (fn () => cell), Seq.empty));
 in
   if eres_flg then eres (rev rAs) else res ()
 end;
end;

fun compose_no_flatten match (orule, nsubgoal) i state =
  bicompose_aux false match (state, dest_state (state, i), false) (false, orule, nsubgoal);

fun bicompose match arg i state =
  bicompose_aux true match (state, dest_state (state,i), false) arg;

(*Quick test whether rule is resolvable with the subgoal with hyps Hs
  and conclusion B.  If eres_flg then checks 1st premise of rule also*)
fun could_bires (Hs, B, eres_flg, rule) =
    let fun could_reshyp (A1::_) = exists (fn H => Term.could_unify (A1, H)) Hs
          | could_reshyp [] = false;  (*no premise -- illegal*)
    in  Term.could_unify(concl_of rule, B) andalso
        (not eres_flg  orelse  could_reshyp (prems_of rule))
    end;

(*Bi-resolution of a state with a list of (flag,rule) pairs.
  Puts the rule above:  rule/state.  Renames vars in the rules. *)
fun biresolution match brules i state =
    let val (stpairs, Bs, Bi, C) = dest_state(state,i);
        val lift = lift_rule (cprem_of state i);
        val B = Logic.strip_assums_concl Bi;
        val Hs = Logic.strip_assums_hyp Bi;
        val compose = bicompose_aux true match (state, (stpairs, Bs, Bi, C), true);
        fun res [] = Seq.empty
          | res ((eres_flg, rule)::brules) =
              if !Pattern.trace_unify_fail orelse
                 could_bires (Hs, B, eres_flg, rule)
              then Seq.make (*delay processing remainder till needed*)
                  (fn()=> SOME(compose (eres_flg, lift rule, nprems_of rule),
                               res brules))
              else res brules
    in  Seq.flat (res brules)  end;



(*** Future theorems -- proofs with promises ***)

(* future rule *)

fun future_result i orig_thy orig_shyps orig_prop raw_thm =
  let
    val _ = Theory.check_thy orig_thy;
    val thm = strip_shyps (transfer orig_thy raw_thm);
    val _ = Theory.check_thy orig_thy;
    fun err msg = raise THM ("future_result: " ^ msg, 0, [thm]);

    val Thm (Deriv {max_promise, ...}, {shyps, hyps, tpairs, prop, ...}) = thm;
    val _ = prop aconv orig_prop orelse err "bad prop";
    val _ = null tpairs orelse err "bad tpairs";
    val _ = null hyps orelse err "bad hyps";
    val _ = Sorts.subset (shyps, orig_shyps) orelse err "bad shyps";
    val _ = max_promise < i orelse err "bad dependencies";
  in thm end;

fun future future_thm ct =
  let
    val Cterm {thy_ref = thy_ref, t = prop, T, maxidx, sorts} = ct;
    val thy = Context.reject_draft (Theory.deref thy_ref);
    val _ = T <> propT andalso raise CTERM ("future: prop expected", [ct]);

    val i = serial ();
    val future = future_thm |> Future.map (future_result i thy sorts prop);
    val promise = (i, future);
  in
    Thm (make_deriv i [promise] [promise] [] [] (Pt.promise_proof thy i prop),
     {thy_ref = thy_ref,
      tags = [],
      maxidx = maxidx,
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = prop})
  end;


(* derivation status *)

fun raw_proof_body_of (Thm (Deriv {body, ...}, _)) = body;
val raw_proof_of = Proofterm.proof_of o raw_proof_body_of;

fun pending_groups (Thm (Deriv {open_promises, ...}, _)) =
  fold (insert Task_Queue.eq_group o Future.group_of o #2) open_promises;

fun status_of (Thm (Deriv {promises, body, ...}, _)) =
  let
    val ps = map (Future.peek o snd) promises;
    val bodies = body ::
      map_filter (fn SOME (Exn.Result th) => SOME (raw_proof_body_of th) | _ => NONE) ps;
    val {oracle, unfinished, failed} = Pt.status_of bodies;
  in
   {oracle = oracle,
    unfinished = unfinished orelse exists is_none ps,
    failed = failed orelse exists (fn SOME (Exn.Exn _) => true | _ => false) ps}
  end;


(* fulfilled proofs *)

fun proof_body_of (Thm (Deriv {open_promises, promises, body, ...}, {thy_ref, ...})) =
  let
    val _ = Exn.release_all (map (Future.join_result o #2) (rev open_promises));
    val ps = map (apsnd (raw_proof_body_of o Future.join)) promises;
  in Pt.fulfill_proof (Theory.deref thy_ref) ps body end;

val proof_of = Proofterm.proof_of o proof_body_of;
val join_proof = ignore o proof_body_of;


(* closed derivations with official name *)

fun get_name thm =
  Pt.get_name (hyps_of thm) (prop_of thm) (raw_proof_of thm);

fun put_name name (thm as Thm (der, args)) =
  let
    val Deriv {max_promise, open_promises, promises, body, ...} = der;
    val {thy_ref, hyps, prop, tpairs, ...} = args;
    val _ = null tpairs orelse raise THM ("put_name: unsolved flex-flex constraints", 0, [thm]);

    val ps = map (apsnd (Future.map proof_body_of)) promises;
    val thy = Theory.deref thy_ref;
    val (pthm, proof) = Pt.thm_proof thy name hyps prop ps body;

    val open_promises' = open_promises |> filter (fn (_, p) =>
      (case Future.peek p of SOME (Exn.Result _) => false | _ => true));
    val der' = make_deriv max_promise open_promises' [] [] [pthm] proof;
    val _ = Theory.check_thy thy;
  in Thm (der', args) end;



(*** Oracles ***)

(* oracle rule *)

fun invoke_oracle thy_ref1 name oracle arg =
  let val Cterm {thy_ref = thy_ref2, t = prop, T, maxidx, sorts} = oracle arg in
    if T <> propT then
      raise THM ("Oracle's result must have type prop: " ^ name, 0, [])
    else
      let val (ora, prf) = Pt.oracle_proof name prop in
        Thm (make_deriv ~1 [] [] [ora] [] prf,
         {thy_ref = Theory.merge_refs (thy_ref1, thy_ref2),
          tags = [],
          maxidx = maxidx,
          shyps = sorts,
          hyps = [],
          tpairs = [],
          prop = prop})
      end
  end;


(* authentic derivation names *)

fun err_dup_ora dup = error ("Duplicate oracle: " ^ quote dup);

structure Oracles = TheoryDataFun
(
  type T = serial NameSpace.table;
  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ oracles : T = NameSpace.merge_tables (op =) oracles
    handle Symtab.DUP dup => err_dup_ora dup;
);

val extern_oracles = map #1 o NameSpace.extern_table o Oracles.get;

fun add_oracle (b, oracle) thy =
  let
    val naming = Sign.naming_of thy;
    val (name, tab') = NameSpace.define naming (b, serial ()) (Oracles.get thy)
      handle Symtab.DUP _ => err_dup_ora (Binding.str_of b);
    val thy' = Oracles.put tab' thy;
  in ((name, invoke_oracle (Theory.check_thy thy') name oracle), thy') end;

end;

structure BasicThm: BASIC_THM = Thm;
open BasicThm;
