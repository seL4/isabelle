(*  Title:      Pure/thm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The very core of Isabelle's Meta Logic: certified types and terms,
meta theorems, meta rules (including lifting and resolution).
*)

signature BASIC_THM =
  sig
  (*certified types*)
  type ctyp
  val rep_ctyp: ctyp ->
   {thy: theory,
    sign: theory,       (*obsolete*)
    T: typ,
    sorts: sort list}
  val theory_of_ctyp: ctyp -> theory
  val typ_of: ctyp -> typ
  val ctyp_of: theory -> typ -> ctyp
  val read_ctyp: theory -> string -> ctyp

  (*certified terms*)
  type cterm
  exception CTERM of string
  val rep_cterm: cterm ->
   {thy: theory,
    sign: theory,       (*obsolete*)
    t: term,
    T: typ,
    maxidx: int,
    sorts: sort list}
  val crep_cterm: cterm ->
    {thy: theory, sign: theory, t: term, T: ctyp, maxidx: int, sorts: sort list}
  val theory_of_cterm: cterm -> theory
  val sign_of_cterm: cterm -> theory    (*obsolete*)
  val term_of: cterm -> term
  val cterm_of: theory -> term -> cterm
  val ctyp_of_term: cterm -> ctyp
  val read_cterm: theory -> string * typ -> cterm
  val adjust_maxidx: cterm -> cterm
  val read_def_cterm:
    theory * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> string * typ -> cterm * (indexname * typ) list
  val read_def_cterms:
    theory * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ)list
    -> cterm list * (indexname * typ)list

  type tag              (* = string * string list *)

  (*meta theorems*)
  type thm
  val rep_thm: thm ->
   {thy: theory,
    sign: theory,       (*obsolete*)
    der: bool * Proofterm.proof,
    maxidx: int,
    shyps: sort list,
    hyps: term list,
    tpairs: (term * term) list,
    prop: term}
  val crep_thm: thm ->
   {thy: theory,
    sign: theory,       (*obsolete*)
    der: bool * Proofterm.proof,
    maxidx: int,
    shyps: sort list,
    hyps: cterm list,
    tpairs: (cterm * cterm) list,
    prop: cterm}
  exception THM of string * int * thm list
  type 'a attribute     (* = 'a * thm -> 'a * thm *)
  val eq_thm: thm * thm -> bool
  val eq_thms: thm list * thm list -> bool
  val theory_of_thm: thm -> theory
  val sign_of_thm: thm -> theory    (*obsolete*)
  val prop_of: thm -> term
  val proof_of: thm -> Proofterm.proof
  val tpairs_of: thm -> (term * term) list
  val concl_of: thm -> term
  val prems_of: thm -> term list
  val nprems_of: thm -> int
  val cprop_of: thm -> cterm
  val transfer: theory -> thm -> thm
  val weaken: cterm -> thm -> thm
  val extra_shyps: thm -> sort list
  val strip_shyps: thm -> thm
  val get_axiom_i: theory -> string -> thm
  val get_axiom: theory -> xstring -> thm
  val def_name: string -> string
  val get_def: theory -> xstring -> thm
  val axioms_of: theory -> (string * thm) list

  (*meta rules*)
  val assume: cterm -> thm
  val implies_intr: cterm -> thm -> thm
  val implies_elim: thm -> thm -> thm
  val forall_intr: cterm -> thm -> thm
  val forall_elim: cterm -> thm -> thm
  val reflexive: cterm -> thm
  val symmetric: thm -> thm
  val transitive: thm -> thm -> thm
  val beta_conversion: bool -> cterm -> thm
  val eta_conversion: cterm -> thm
  val abstract_rule: string -> cterm -> thm -> thm
  val combination: thm -> thm -> thm
  val equal_intr: thm -> thm -> thm
  val equal_elim: thm -> thm -> thm
  val flexflex_rule: thm -> thm Seq.seq
  val instantiate: (ctyp * ctyp) list * (cterm * cterm) list -> thm -> thm
  val trivial: cterm -> thm
  val class_triv: theory -> class -> thm
  val varifyT: thm -> thm
  val varifyT': (string * sort) list -> thm -> thm * ((string * sort) * indexname) list
  val freezeT: thm -> thm
  val dest_state: thm * int -> (term * term) list * term list * term * term
  val lift_rule: (thm * int) -> thm -> thm
  val incr_indexes: int -> thm -> thm
  val assumption: int -> thm -> thm Seq.seq
  val eq_assumption: int -> thm -> thm
  val rotate_rule: int -> int -> thm -> thm
  val permute_prems: int -> int -> thm -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val bicompose: bool -> bool * thm * int -> int -> thm -> thm Seq.seq
  val biresolution: bool -> (bool * thm) list -> int -> thm -> thm Seq.seq
  val invoke_oracle: theory -> xstring -> theory * Object.T -> thm
  val invoke_oracle_i: theory -> string -> theory * Object.T -> thm
end;

signature THM =
sig
  include BASIC_THM
  val dest_ctyp: ctyp -> ctyp list
  val dest_comb: cterm -> cterm * cterm
  val dest_abs: string option -> cterm -> cterm * cterm
  val capply: cterm -> cterm -> cterm
  val cabs: cterm -> cterm -> cterm
  val major_prem_of: thm -> term
  val no_prems: thm -> bool
  val no_attributes: 'a -> 'a * 'b attribute list
  val apply_attributes: ('a * thm) * 'a attribute list -> 'a * thm
  val applys_attributes: ('a * thm list) * 'a attribute list -> 'a * thm list
  val terms_of_tpairs: (term * term) list -> term list
  val full_prop_of: thm -> term
  val get_name_tags: thm -> string * tag list
  val put_name_tags: string * tag list -> thm -> thm
  val name_of_thm: thm -> string
  val tags_of_thm: thm -> tag list
  val name_thm: string * thm -> thm
  val compress: thm -> thm
  val adjust_maxidx_thm: thm -> thm
  val rename_boundvars: term -> term -> thm -> thm
  val cterm_match: cterm * cterm -> (ctyp * ctyp) list * (cterm * cterm) list
  val cterm_first_order_match: cterm * cterm -> (ctyp * ctyp) list * (cterm * cterm) list
  val cterm_incr_indexes: int -> cterm -> cterm
end;

structure Thm: THM =
struct


(*** Certified terms and types ***)

(** collect occurrences of sorts -- unless all sorts non-empty **)

fun may_insert_typ_sorts thy T = if Sign.all_sorts_nonempty thy then I else Sorts.insert_typ T;
fun may_insert_term_sorts thy t = if Sign.all_sorts_nonempty thy then I else Sorts.insert_term t;

(*NB: type unification may invent new sorts*)
fun may_insert_env_sorts thy (env as Envir.Envir {iTs, ...}) =
  if Sign.all_sorts_nonempty thy then I
  else Vartab.fold (fn (_, (_, T)) => Sorts.insert_typ T) iTs;



(** certified types **)

datatype ctyp = Ctyp of {thy_ref: theory_ref, T: typ, sorts: sort list};

fun rep_ctyp (Ctyp {thy_ref, T, sorts}) =
  let val thy = Theory.deref thy_ref
  in {thy = thy, sign = thy, T = T, sorts = sorts} end;

fun theory_of_ctyp (Ctyp {thy_ref, ...}) = Theory.deref thy_ref;

fun typ_of (Ctyp {T, ...}) = T;

fun ctyp_of thy raw_T =
  let val T = Sign.certify_typ thy raw_T
  in Ctyp {thy_ref = Theory.self_ref thy, T = T, sorts = may_insert_typ_sorts thy T []} end;

fun read_ctyp thy s =
  let val T = Sign.read_typ (thy, K NONE) s
  in Ctyp {thy_ref = Theory.self_ref thy, T = T, sorts = may_insert_typ_sorts thy T []} end;

fun dest_ctyp (Ctyp {thy_ref, T = Type (s, Ts), sorts}) =
      map (fn T => Ctyp {thy_ref = thy_ref, T = T, sorts = sorts}) Ts
  | dest_ctyp cT = raise TYPE ("dest_ctyp", [typ_of cT], []);



(** certified terms **)

(*certified terms with checked typ, maxidx, and sorts*)
datatype cterm = Cterm of
 {thy_ref: theory_ref,
  t: term,
  T: typ,
  maxidx: int,
  sorts: sort list};

exception CTERM of string;

fun rep_cterm (Cterm {thy_ref, t, T, maxidx, sorts}) =
  let val thy =  Theory.deref thy_ref
  in {thy = thy, sign = thy, t = t, T = T, maxidx = maxidx, sorts = sorts} end;

fun crep_cterm (Cterm {thy_ref, t, T, maxidx, sorts}) =
  let val thy = Theory.deref thy_ref in
   {thy = thy, sign = thy, t = t, T = Ctyp {thy_ref = thy_ref, T = T, sorts = sorts},
    maxidx = maxidx, sorts = sorts}
  end;

fun theory_of_cterm (Cterm {thy_ref, ...}) = Theory.deref thy_ref;
val sign_of_cterm = theory_of_cterm;

fun term_of (Cterm {t, ...}) = t;

fun ctyp_of_term (Cterm {thy_ref, T, sorts, ...}) =
  Ctyp {thy_ref = thy_ref, T = T, sorts = sorts};

fun cterm_of thy tm =
  let
    val (t, T, maxidx) = Sign.certify_term (Sign.pp thy) thy tm;
    val sorts = may_insert_term_sorts thy t [];
  in Cterm {thy_ref = Theory.self_ref thy, t = t, T = T, maxidx = maxidx, sorts = sorts} end;

fun merge_thys0 (Cterm {thy_ref = r1, ...}) (Cterm {thy_ref = r2, ...}) =
  Theory.merge_refs (r1, r2);

(*Destruct application in cterms*)
fun dest_comb (Cterm {t = t $ u, T, thy_ref, maxidx, sorts}) =
      let val A = Term.argument_type_of t in
        (Cterm {t = t, T = A --> T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts},
         Cterm {t = u, T = A, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts})
      end
  | dest_comb _ = raise CTERM "dest_comb";

(*Destruct abstraction in cterms*)
fun dest_abs a (Cterm {t = Abs (x, T, t), T = Type ("fun", [_, U]), thy_ref, maxidx, sorts}) =
      let val (y', t') = Term.dest_abs (if_none a x, T, t) in
        (Cterm {t = Free (y', T), T = T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts},
          Cterm {t = t', T = U, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts})
      end
  | dest_abs _ _ = raise CTERM "dest_abs";

(*Makes maxidx precise: it is often too big*)
fun adjust_maxidx (ct as Cterm {thy_ref, t, T, maxidx, sorts}) =
  if maxidx = ~1 then ct
  else Cterm {thy_ref = thy_ref, t = t, T = T, maxidx = maxidx_of_term t, sorts = sorts};

(*Form cterm out of a function and an argument*)
fun capply
  (cf as Cterm {t = f, T = Type ("fun", [dty, rty]), maxidx = maxidx1, sorts = sorts1, ...})
  (cx as Cterm {t = x, T, maxidx = maxidx2, sorts = sorts2, ...}) =
    if T = dty then
      Cterm {thy_ref = merge_thys0 cf cx,
        t = f $ x,
        T = rty,
        maxidx = Int.max (maxidx1, maxidx2),
        sorts = Sorts.union sorts1 sorts2}
      else raise CTERM "capply: types don't agree"
  | capply _ _ = raise CTERM "capply: first arg is not a function"

fun cabs
  (ct1 as Cterm {t = t1, T = T1, maxidx = maxidx1, sorts = sorts1, ...})
  (ct2 as Cterm {t = t2, T = T2, maxidx = maxidx2, sorts = sorts2, ...}) =
    let val t = lambda t1 t2 handle TERM _ => raise CTERM "cabs: first arg is not a variable" in
      Cterm {thy_ref = merge_thys0 ct1 ct2,
        t = t, T = T1 --> T2,
        maxidx = Int.max (maxidx1, maxidx2),
        sorts = Sorts.union sorts1 sorts2}
    end;

(*Matching of cterms*)
fun gen_cterm_match match
    (ct1 as Cterm {t = t1, maxidx = maxidx1, sorts = sorts1, ...},
     ct2 as Cterm {t = t2, maxidx = maxidx2, sorts = sorts2, ...}) =
  let
    val thy_ref = merge_thys0 ct1 ct2;
    val (Tinsts, tinsts) = match (Sign.tsig_of (Theory.deref thy_ref)) (t1, t2);
    val maxidx = Int.max (maxidx1, maxidx2);
    val sorts = Sorts.union sorts1 sorts2;
    fun mk_cTinst (ixn, (S, T)) =
      (Ctyp {T = TVar (ixn, S), thy_ref = thy_ref, sorts = sorts},
       Ctyp {T = T, thy_ref = thy_ref, sorts = sorts});
    fun mk_ctinst (ixn, (T, t)) =
      let val T = Envir.typ_subst_TVars Tinsts T in
        (Cterm {t = Var (ixn, T), T = T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts},
         Cterm {t = t, T = T, thy_ref = thy_ref, maxidx = maxidx, sorts = sorts})
      end;
  in (Vartab.fold (cons o mk_cTinst) Tinsts [], Vartab.fold (cons o mk_ctinst) tinsts []) end;

val cterm_match = gen_cterm_match Pattern.match;
val cterm_first_order_match = gen_cterm_match Pattern.first_order_match;

(*Incrementing indexes*)
fun cterm_incr_indexes i (ct as Cterm {thy_ref, t, T, maxidx, sorts}) =
  if i < 0 then raise CTERM "negative increment"
  else if i = 0 then ct
  else Cterm {thy_ref = thy_ref, t = Logic.incr_indexes ([], i) t,
    T = Logic.incr_tvar i T, maxidx = maxidx + i, sorts = sorts};



(** read cterms **)   (*exception ERROR*)

(*read terms, infer types, certify terms*)
fun read_def_cterms (thy, types, sorts) used freeze sTs =
  let
    val (ts', tye) = Sign.read_def_terms (thy, types, sorts) used freeze sTs;
    val cts = map (cterm_of thy) ts'
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in (cts, tye) end;

(*read term, infer types, certify term*)
fun read_def_cterm args used freeze aT =
  let val ([ct],tye) = read_def_cterms args used freeze [aT]
  in (ct,tye) end;

fun read_cterm thy = #1 o read_def_cterm (thy, K NONE, K NONE) [] true;


(*tags provide additional comment, apart from the axiom/theorem name*)
type tag = string * string list;


(*** Meta theorems ***)

structure Pt = Proofterm;

datatype thm = Thm of
 {thy_ref: theory_ref,         (*dynamic reference to theory*)
  der: bool * Pt.proof,        (*derivation*)
  maxidx: int,                 (*maximum index of any Var or TVar*)
  shyps: sort list,            (*sort hypotheses as ordered list*)
  hyps: term list,             (*hypotheses as ordered list*)
  tpairs: (term * term) list,  (*flex-flex pairs*)
  prop: term};                 (*conclusion*)

(*errors involving theorems*)
exception THM of string * int * thm list;

fun rep_thm (Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  let val thy = Theory.deref thy_ref in
   {thy = thy, sign = thy, der = der, maxidx = maxidx,
    shyps = shyps, hyps = hyps, tpairs = tpairs, prop = prop}
  end;

(*version of rep_thm returning cterms instead of terms*)
fun crep_thm (Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  let
    val thy = Theory.deref thy_ref;
    fun cterm max t = Cterm {thy_ref = thy_ref, t = t, T = propT, maxidx = max, sorts = shyps};
  in
   {thy = thy, sign = thy, der = der, maxidx = maxidx, shyps = shyps,
    hyps = map (cterm ~1) hyps,
    tpairs = map (pairself (cterm maxidx)) tpairs,
    prop = cterm maxidx prop}
  end;

fun terms_of_tpairs tpairs = fold_rev (fn (t, u) => cons t o cons u) tpairs [];

fun eq_tpairs ((t, u), (t', u')) = t aconv t' andalso u aconv u';
val union_tpairs = gen_merge_lists eq_tpairs;
val maxidx_tpairs = fold (fn (t, u) => Term.maxidx_term t #> Term.maxidx_term u);

fun attach_tpairs tpairs prop =
  Logic.list_implies (map Logic.mk_equals tpairs, prop);

fun full_prop_of (Thm {tpairs, prop, ...}) = attach_tpairs tpairs prop;


(* merge theories of cterms/thms; raise exception if incompatible *)

fun merge_thys1 (Cterm {thy_ref = r1, ...}) (th as Thm {thy_ref = r2, ...}) =
  Theory.merge_refs (r1, r2) handle TERM (msg, _) => raise THM (msg, 0, [th]);

fun merge_thys2 (th1 as Thm {thy_ref = r1, ...}) (th2 as Thm {thy_ref = r2, ...}) =
  Theory.merge_refs (r1, r2) handle TERM (msg, _) => raise THM (msg, 0, [th1, th2]);


(*attributes subsume any kind of rules or context modifiers*)
type 'a attribute = 'a * thm -> 'a * thm;
  
fun no_attributes x = (x, []);
fun apply_attributes (x_th, atts) = Library.apply atts x_th;
fun applys_attributes (x_ths, atts) = foldl_map (Library.apply atts) x_ths;


(* hyps *)

val insert_hyps = OrdList.insert Term.fast_term_ord;
val remove_hyps = OrdList.remove Term.fast_term_ord;
val union_hyps = OrdList.union Term.fast_term_ord;
val eq_set_hyps = OrdList.eq_set Term.fast_term_ord;


(* eq_thm(s) *)

fun eq_thm (th1, th2) =
  let
    val {thy = thy1, shyps = shyps1, hyps = hyps1, tpairs = tpairs1, prop = prop1, ...} =
      rep_thm th1;
    val {thy = thy2, shyps = shyps2, hyps = hyps2, tpairs = tpairs2, prop = prop2, ...} =
      rep_thm th2;
  in
    Context.joinable (thy1, thy2) andalso
    Sorts.eq_set (shyps1, shyps2) andalso
    eq_set_hyps (hyps1, hyps2) andalso
    equal_lists eq_tpairs (tpairs1, tpairs2) andalso
    prop1 aconv prop2
  end;

val eq_thms = Library.equal_lists eq_thm;

fun theory_of_thm (Thm {thy_ref, ...}) = Theory.deref thy_ref;
val sign_of_thm = theory_of_thm;

fun prop_of (Thm {prop, ...}) = prop;
fun proof_of (Thm {der = (_, proof), ...}) = proof;
fun tpairs_of (Thm {tpairs, ...}) = tpairs;

val concl_of = Logic.strip_imp_concl o prop_of;
val prems_of = Logic.strip_imp_prems o prop_of;
fun nprems_of th = Logic.count_prems (prop_of th, 0);
val no_prems = equal 0 o nprems_of;

fun major_prem_of th =
  (case prems_of th of
    prem :: _ => Logic.strip_assums_concl prem
  | [] => raise THM ("major_prem_of: rule with no premises", 0, [th]));

(*the statement of any thm is a cterm*)
fun cprop_of (Thm {thy_ref, maxidx, shyps, prop, ...}) =
  Cterm {thy_ref = thy_ref, maxidx = maxidx, T = propT, t = prop, sorts = shyps};

(*explicit transfer to a super theory*)
fun transfer thy' thm =
  let
    val Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop} = thm;
    val thy = Theory.deref thy_ref;
  in
    if not (subthy (thy, thy')) then
      raise THM ("transfer: not a super theory", 0, [thm])
    else if eq_thy (thy, thy') then thm
    else
      Thm {thy_ref = Theory.self_ref thy',
        der = der,
        maxidx = maxidx,
        shyps = shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = prop}
  end;

(*explicit weakening: maps |- B to A |- B*)
fun weaken raw_ct th =
  let
    val ct as Cterm {t = A, T, sorts, maxidx = maxidxA, ...} = adjust_maxidx raw_ct;
    val Thm {der, maxidx, shyps, hyps, tpairs, prop, ...} = th;
  in
    if T <> propT then
      raise THM ("weaken: assumptions must have type prop", 0, [])
    else if maxidxA <> ~1 then
      raise THM ("weaken: assumptions may not contain schematic variables", maxidxA, [])
    else
      Thm {thy_ref = merge_thys1 ct th,
        der = der,
        maxidx = maxidx,
        shyps = Sorts.union sorts shyps,
        hyps = insert_hyps A hyps,
        tpairs = tpairs,
        prop = prop}
  end;



(** sort contexts of theorems **)

fun present_sorts (Thm {hyps, tpairs, prop, ...}) =
  fold (fn (t, u) => Sorts.insert_term t o Sorts.insert_term u) tpairs
    (Sorts.insert_terms hyps (Sorts.insert_term prop []));

(*remove extra sorts that are non-empty by virtue of type signature information*)
fun strip_shyps (thm as Thm {shyps = [], ...}) = thm
  | strip_shyps (thm as Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
      let
        val thy = Theory.deref thy_ref;
        val shyps' =
          if Sign.all_sorts_nonempty thy then []
          else
            let
              val present = present_sorts thm;
              val extra = Sorts.subtract present shyps;
              val witnessed = map #2 (Sign.witness_sorts thy present extra);
            in Sorts.subtract witnessed shyps end;
      in
        Thm {thy_ref = thy_ref, der = der, maxidx = maxidx,
          shyps = shyps', hyps = hyps, tpairs = tpairs, prop = prop}
      end;

(*dangling sort constraints of a thm*)
fun extra_shyps (th as Thm {shyps, ...}) = Sorts.subtract (present_sorts th) shyps;



(** Axioms **)

(*look up the named axiom in the theory or its ancestors*)
fun get_axiom_i theory name =
  let
    fun get_ax thy =
      Symtab.lookup (#2 (#axioms (Theory.rep_theory thy)), name)
      |> Option.map (fn prop =>
          Thm {thy_ref = Theory.self_ref thy,
            der = Pt.infer_derivs' I (false, Pt.axm_proof name prop),
            maxidx = maxidx_of_term prop,
            shyps = may_insert_term_sorts thy prop [],
            hyps = [],
            tpairs = [],
            prop = prop});
  in
    (case get_first get_ax (theory :: Theory.ancestors_of theory) of
      SOME thm => thm
    | NONE => raise THEORY ("No axiom " ^ quote name, [theory]))
  end;

fun get_axiom thy =
  get_axiom_i thy o NameSpace.intern (Theory.axiom_space thy);

fun def_name name = name ^ "_def";
fun get_def thy = get_axiom thy o def_name;


(*return additional axioms of this theory node*)
fun axioms_of thy =
  map (fn (s, _) => (s, get_axiom thy s))
    (Symtab.dest (#2 (#axioms (Theory.rep_theory thy))));


(* name and tags -- make proof objects more readable *)

fun get_name_tags (Thm {hyps, prop, der = (_, prf), ...}) =
  Pt.get_name_tags hyps prop prf;

fun put_name_tags x (Thm {thy_ref, der = (ora, prf), maxidx,
      shyps, hyps, tpairs = [], prop}) = Thm {thy_ref = thy_ref,
        der = (ora, Pt.thm_proof (Theory.deref thy_ref) x hyps prop prf),
        maxidx = maxidx, shyps = shyps, hyps = hyps, tpairs = [], prop = prop}
  | put_name_tags _ thm =
      raise THM ("put_name_tags: unsolved flex-flex constraints", 0, [thm]);

val name_of_thm = #1 o get_name_tags;
val tags_of_thm = #2 o get_name_tags;

fun name_thm (name, thm) = put_name_tags (name, tags_of_thm thm) thm;


(*Compression of theorems -- a separate rule, not integrated with the others,
  as it could be slow.*)
fun compress (Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  Thm {thy_ref = thy_ref,
    der = der,
    maxidx = maxidx,
    shyps = shyps,
    hyps = map Term.compress_term hyps,
    tpairs = map (pairself Term.compress_term) tpairs,
    prop = Term.compress_term prop};

fun adjust_maxidx_thm (Thm {thy_ref, der, shyps, hyps, tpairs, prop, ...}) =
  Thm {thy_ref = thy_ref,
    der = der,
    maxidx = maxidx_tpairs tpairs (maxidx_of_term prop),
    shyps = shyps,
    hyps = hyps,
    tpairs = tpairs,
    prop = prop};



(*** Meta rules ***)

(** primitive rules **)

(*The assumption rule A |- A*)
fun assume raw_ct =
  let val Cterm {thy_ref, t = prop, T, maxidx, sorts} = adjust_maxidx raw_ct in
    if T <> propT then
      raise THM ("assume: assumptions must have type prop", 0, [])
    else if maxidx <> ~1 then
      raise THM ("assume: assumptions may not contain schematic variables", maxidx, [])
    else Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' I (false, Pt.Hyp prop),
      maxidx = ~1,
      shyps = sorts,
      hyps = [prop],
      tpairs = [],
      prop = prop}
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
    (th as Thm {der, maxidx, hyps, shyps, tpairs, prop, ...}) =
  if T <> propT then
    raise THM ("implies_intr: assumptions must have type prop", 0, [th])
  else
    Thm {thy_ref = merge_thys1 ct th,
      der = Pt.infer_derivs' (Pt.implies_intr_proof A) der,
      maxidx = Int.max (maxidxA, maxidx),
      shyps = Sorts.union sorts shyps,
      hyps = remove_hyps A hyps,
      tpairs = tpairs,
      prop = implies $ A $ prop};


(*Implication elimination
  A ==> B    A
  ------------
        B
*)
fun implies_elim thAB thA =
  let
    val Thm {maxidx = maxA, der = derA, hyps = hypsA, shyps = shypsA, tpairs = tpairsA,
      prop = propA, ...} = thA
    and Thm {der, maxidx, hyps, shyps, tpairs, prop, ...} = thAB;
    fun err () = raise THM ("implies_elim: major premise", 0, [thAB, thA]);
  in
    case prop of
      imp $ A $ B =>
        if imp = Term.implies andalso A aconv propA then
          Thm {thy_ref = merge_thys2 thAB thA,
            der = Pt.infer_derivs (curry Pt.%%) der derA,
            maxidx = Int.max (maxA, maxidx),
            shyps = Sorts.union shypsA shyps,
            hyps = union_hyps hypsA hyps,
            tpairs = union_tpairs tpairsA tpairs,
            prop = B}
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
    (th as Thm {der, maxidx, shyps, hyps, tpairs, prop, ...}) =
  let
    fun result a =
      Thm {thy_ref = merge_thys1 ct th,
        der = Pt.infer_derivs' (Pt.forall_intr_proof x a) der,
        maxidx = maxidx,
        shyps = Sorts.union sorts shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = all T $ Abs (a, T, abstract_over (x, prop))};
    fun check_occs x ts =
      if exists (fn t => Logic.occs (x, t)) ts then
        raise THM("forall_intr: variable free in assumptions", 0, [th])
      else ();
  in
    case x of
      Free (a, _) => (check_occs x hyps; check_occs x (terms_of_tpairs tpairs); result a)
    | Var ((a, _), _) => (check_occs x (terms_of_tpairs tpairs); result a)
    | _ => raise THM ("forall_intr: not a variable", 0, [th])
  end;

(*Forall elimination
  !!x. A
  ------
  A[t/x]
*)
fun forall_elim
    (ct as Cterm {t, T, maxidx = maxt, sorts, ...})
    (th as Thm {der, maxidx, shyps, hyps, tpairs, prop, ...}) =
  (case prop of
    Const ("all", Type ("fun", [Type ("fun", [qary, _]), _])) $ A =>
      if T <> qary then
        raise THM ("forall_elim: type mismatch", 0, [th])
      else
        Thm {thy_ref = merge_thys1 ct th,
          der = Pt.infer_derivs' (Pt.% o rpair (SOME t)) der,
          maxidx = Int.max (maxidx, maxt),
          shyps = Sorts.union sorts shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = Term.betapply (A, t)}
  | _ => raise THM ("forall_elim: not quantified", 0, [th]));


(* Equality *)

(*Reflexivity
  t == t
*)
fun reflexive (ct as Cterm {thy_ref, t, T, maxidx, sorts}) =
  Thm {thy_ref = thy_ref,
    der = Pt.infer_derivs' I (false, Pt.reflexive),
    maxidx = maxidx,
    shyps = sorts,
    hyps = [],
    tpairs = [],
    prop = Logic.mk_equals (t, t)};

(*Symmetry
  t == u
  ------
  u == t
*)
fun symmetric (th as Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  (case prop of
    (eq as Const ("==", Type (_, [T, _]))) $ t $ u =>
      Thm {thy_ref = thy_ref,
        der = Pt.infer_derivs' Pt.symmetric der,
        maxidx = maxidx,
        shyps = shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = eq $ u $ t}
    | _ => raise THM ("symmetric", 0, [th]));

(*Transitivity
  t1 == u    u == t2
  ------------------
       t1 == t2
*)
fun transitive th1 th2 =
  let
    val Thm {der = der1, maxidx = max1, hyps = hyps1, shyps = shyps1, tpairs = tpairs1,
      prop = prop1, ...} = th1
    and Thm {der = der2, maxidx = max2, hyps = hyps2, shyps = shyps2, tpairs = tpairs2,
      prop = prop2, ...} = th2;
    fun err msg = raise THM ("transitive: " ^ msg, 0, [th1, th2]);
  in
    case (prop1, prop2) of
      ((eq as Const ("==", Type (_, [T, _]))) $ t1 $ u, Const ("==", _) $ u' $ t2) =>
        if not (u aconv u') then err "middle term"
        else
          Thm {thy_ref = merge_thys2 th1 th2,
            der = Pt.infer_derivs (Pt.transitive u T) der1 der2,
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = eq $ t1 $ t2}
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
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' I (false, Pt.reflexive),
      maxidx = maxidx,
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_equals (t, t')}
  end;

fun eta_conversion (Cterm {thy_ref, t, T, maxidx, sorts}) =
  Thm {thy_ref = thy_ref,
    der = Pt.infer_derivs' I (false, Pt.reflexive),
    maxidx = maxidx,
    shyps = sorts,
    hyps = [],
    tpairs = [],
    prop = Logic.mk_equals (t, Pattern.eta_contract t)};

(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.
  The bound variable will be named "a" (since x will be something like x320)
      t == u
  --------------
  %x. t == %x. u
*)
fun abstract_rule a
    (Cterm {t = x, T, sorts, ...})
    (th as Thm {thy_ref, der, maxidx, hyps, shyps, tpairs, prop}) =
  let
    val (t, u) = Logic.dest_equals prop
      handle TERM _ => raise THM ("abstract_rule: premise not an equality", 0, [th]);
    val result =
      Thm {thy_ref = thy_ref,
        der = Pt.infer_derivs' (Pt.abstract_rule x a) der,
        maxidx = maxidx,
        shyps = Sorts.union sorts shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = Logic.mk_equals
          (Abs (a, T, abstract_over (x, t)), Abs (a, T, abstract_over (x, u)))};
    fun check_occs x ts =
      if exists (fn t => Logic.occs (x, t)) ts then
        raise THM ("abstract_rule: variable free in assumptions", 0, [th])
      else ();
  in
    case x of
      Free _ => (check_occs x hyps; check_occs x (terms_of_tpairs tpairs); result)
    | Var _ => (check_occs x (terms_of_tpairs tpairs); result)
    | _ => raise THM ("abstract_rule: not a variable", 0, [th])
  end;

(*The combination rule
  f == g  t == u
  --------------
    f t == g u
*)
fun combination th1 th2 =
  let
    val Thm {der = der1, maxidx = max1, shyps = shyps1, hyps = hyps1, tpairs = tpairs1,
      prop = prop1, ...} = th1
    and Thm {der = der2, maxidx = max2, shyps = shyps2, hyps = hyps2, tpairs = tpairs2,
      prop = prop2, ...} = th2;
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
          Thm {thy_ref = merge_thys2 th1 th2,
            der = Pt.infer_derivs (Pt.combination f g t u fT) der1 der2,
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = Logic.mk_equals (f $ t, g $ u)})
     | _ => raise THM ("combination: premises", 0, [th1, th2])
  end;

(*Equality introduction
  A ==> B  B ==> A
  ----------------
       A == B
*)
fun equal_intr th1 th2 =
  let
    val Thm {der = der1, maxidx = max1, shyps = shyps1, hyps = hyps1, tpairs = tpairs1,
      prop = prop1, ...} = th1
    and Thm {der = der2, maxidx = max2, shyps = shyps2, hyps = hyps2, tpairs = tpairs2,
      prop = prop2, ...} = th2;
    fun err msg = raise THM ("equal_intr: " ^ msg, 0, [th1, th2]);
  in
    case (prop1, prop2) of
      (Const("==>", _) $ A $ B, Const("==>", _) $ B' $ A') =>
        if A aconv A' andalso B aconv B' then
          Thm {thy_ref = merge_thys2 th1 th2,
            der = Pt.infer_derivs (Pt.equal_intr A B) der1 der2,
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = Logic.mk_equals (A, B)}
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
    val Thm {der = der1, maxidx = max1, shyps = shyps1, hyps = hyps1,
      tpairs = tpairs1, prop = prop1, ...} = th1
    and Thm {der = der2, maxidx = max2, shyps = shyps2, hyps = hyps2,
      tpairs = tpairs2, prop = prop2, ...} = th2;
    fun err msg = raise THM ("equal_elim: " ^ msg, 0, [th1, th2]);
  in
    case prop1 of
      Const ("==", _) $ A $ B =>
        if prop2 aconv A then
          Thm {thy_ref = merge_thys2 th1 th2,
            der = Pt.infer_derivs (Pt.equal_elim A B) der1 der2,
            maxidx = Int.max (max1, max2),
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = B}
        else err "not equal"
     | _ =>  err"major premise"
  end;



(**** Derived rules ****)

(*Smash unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.
  Resulting sequence may contain multiple elements if the tpairs are
    not all flex-flex. *)
fun flexflex_rule (th as Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  Unify.smash_unifiers (Theory.deref thy_ref, Envir.empty maxidx, tpairs)
  |> Seq.map (fn env =>
      if Envir.is_empty env then th
      else
        let
          val tpairs' = tpairs |> map (pairself (Envir.norm_term env))
            (*remove trivial tpairs, of the form t==t*)
            |> filter_out (op aconv);
          val prop' = Envir.norm_term env prop;
        in
          Thm {thy_ref = thy_ref,
            der = Pt.infer_derivs' (Pt.norm_proof' env) der,
            maxidx = maxidx_tpairs tpairs' (maxidx_of_term prop'),
            shyps = may_insert_env_sorts (Theory.deref thy_ref) env shyps,
            hyps = hyps,
            tpairs = tpairs',
            prop = prop'}
        end);


(*Instantiation of Vars
           A
  --------------------
  A[t1/v1, ..., tn/vn]
*)

local

fun pretty_typing thy t T =
  Pretty.block [Sign.pretty_term thy t, Pretty.str " ::", Pretty.brk 1, Sign.pretty_typ thy T];

fun add_inst (ct, cu) (thy_ref, sorts) =
  let
    val Cterm {t = t, T = T, ...} = ct
    and Cterm {t = u, T = U, sorts = sorts_u, ...} = cu;
    val thy_ref' = Theory.merge_refs (thy_ref, merge_thys0 ct cu);
    val sorts' = Sorts.union sorts_u sorts;
  in
    (case t of Var v =>
      if T = U then ((v, u), (thy_ref', sorts'))
      else raise TYPE (Pretty.string_of (Pretty.block
       [Pretty.str "instantiate: type conflict",
        Pretty.fbrk, pretty_typing (Theory.deref thy_ref') t T,
        Pretty.fbrk, pretty_typing (Theory.deref thy_ref') u U]), [T, U], [t, u])
    | _ => raise TYPE (Pretty.string_of (Pretty.block
       [Pretty.str "instantiate: not a variable",
        Pretty.fbrk, Sign.pretty_term (Theory.deref thy_ref') t]), [], [t]))
  end;

fun add_instT (cT, cU) (thy_ref, sorts) =
  let
    val Ctyp {T, thy_ref = thy_ref1, ...} = cT
    and Ctyp {T = U, thy_ref = thy_ref2, sorts = sorts_U, ...} = cU;
    val thy_ref' = Theory.merge_refs (thy_ref, Theory.merge_refs (thy_ref1, thy_ref2));
    val thy' = Theory.deref thy_ref';
    val sorts' = Sorts.union sorts_U sorts;
  in
    (case T of TVar (v as (_, S)) =>
      if Type.of_sort (Sign.tsig_of thy') (U, S) then ((v, U), (thy_ref', sorts'))
      else raise TYPE ("Type not of sort " ^ Sign.string_of_sort thy' S, [U], [])
    | _ => raise TYPE (Pretty.string_of (Pretty.block
        [Pretty.str "instantiate: not a type variable",
         Pretty.fbrk, Sign.pretty_typ thy' T]), [T], []))
  end;

in

(*Left-to-right replacements: ctpairs = [..., (vi, ti), ...].
  Instantiates distinct Vars by terms of same type.
  Does NOT normalize the resulting theorem!*)
fun instantiate ([], []) th = th
  | instantiate (instT, inst) th =
      let
        val Thm {thy_ref, der, hyps, shyps, tpairs, prop, ...} = th;
        val (inst', (instT', (thy_ref', shyps'))) =
          (thy_ref, shyps) |> fold_map add_inst inst ||> fold_map add_instT instT;
        val subst = Term.instantiate (instT', inst');
        val prop' = subst prop;
        val tpairs' = map (pairself subst) tpairs;
      in
        if has_duplicates (fn ((v, _), (v', _)) => Term.eq_var (v, v')) inst' then
          raise THM ("instantiate: variables not distinct", 0, [th])
        else if has_duplicates (fn ((v, _), (v', _)) => Term.eq_tvar (v, v')) instT' then
          raise THM ("instantiate: type variables not distinct", 0, [th])
        else
          Thm {thy_ref = thy_ref',
            der = Pt.infer_derivs' (Pt.instantiate (instT', inst')) der,
            maxidx = maxidx_tpairs tpairs' (maxidx_of_term prop'),
            shyps = shyps',
            hyps = hyps,
            tpairs = tpairs',
            prop = prop'}
      end
      handle TYPE (msg, _, _) => raise THM (msg, 0, [th]);

end;


(*The trivial implication A ==> A, justified by assume and forall rules.
  A can contain Vars, not so for assume!*)
fun trivial (Cterm {thy_ref, t =A, T, maxidx, sorts}) =
  if T <> propT then
    raise THM ("trivial: the term must have type prop", 0, [])
  else
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' I (false, Pt.AbsP ("H", NONE, Pt.PBound 0)),
      maxidx = maxidx,
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = implies $ A $ A};

(*Axiom-scheme reflecting signature contents: "OFCLASS(?'a::c, c_class)" *)
fun class_triv thy c =
  let val Cterm {thy_ref, t, maxidx, sorts, ...} =
    cterm_of thy (Logic.mk_inclass (TVar (("'a", 0), [c]), c))
      handle TERM (msg, _) => raise THM ("class_triv: " ^ msg, 0, []);
  in
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' I (false, Pt.PAxm ("ProtoPure.class_triv:" ^ c, t, SOME [])),
      maxidx = maxidx,
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = t}
  end;


(* Replace all TFrees not fixed or in the hyps by new TVars *)
fun varifyT' fixed (Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  let
    val tfrees = foldr add_term_tfrees fixed hyps;
    val prop1 = attach_tpairs tpairs prop;
    val (prop2, al) = Type.varify (prop1, tfrees);
    val (ts, prop3) = Logic.strip_prems (length tpairs, [], prop2);
  in
    (Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' (Pt.varify_proof prop tfrees) der,
      maxidx = Int.max (0, maxidx),
      shyps = shyps,
      hyps = hyps,
      tpairs = rev (map Logic.dest_equals ts),
      prop = prop3}, al)
  end;

val varifyT = #1 o varifyT' [];

(* Replace all TVars by new TFrees *)
fun freezeT (Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  let
    val prop1 = attach_tpairs tpairs prop;
    val prop2 = Type.freeze prop1;
    val (ts, prop3) = Logic.strip_prems (length tpairs, [], prop2);
  in
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' (Pt.freezeT prop1) der,
      maxidx = maxidx_of_term prop2,
      shyps = shyps,
      hyps = hyps,
      tpairs = rev (map Logic.dest_equals ts),
      prop = prop3}
  end;


(*** Inference rules for tactics ***)

(*Destruct proof state into constraints, other goals, goal(i), rest *)
fun dest_state (state as Thm{prop,tpairs,...}, i) =
  (case  Logic.strip_prems(i, [], prop) of
      (B::rBs, C) => (tpairs, rev rBs, B, C)
    | _ => raise THM("dest_state", i, [state]))
  handle TERM _ => raise THM("dest_state", i, [state]);

(*Increment variables and parameters of orule as required for
  resolution with goal i of state. *)
fun lift_rule (state, i) orule =
  let
    val Thm {shyps = sshyps, prop = sprop, maxidx = smax, ...} = state;
    val (Bi :: _, _) = Logic.strip_prems (i, [], sprop)
      handle TERM _ => raise THM ("lift_rule", i, [orule, state]);
    val (lift_abs, lift_all) = Logic.lift_fns (Bi, smax + 1);
    val (Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) = orule;
    val (As, B) = Logic.strip_horn prop;
  in
    Thm {thy_ref = merge_thys2 state orule,
      der = Pt.infer_derivs' (Pt.lift_proof Bi (smax + 1) prop) der,
      maxidx = maxidx + smax + 1,
      shyps = Sorts.union sshyps shyps,
      hyps = hyps,
      tpairs = map (pairself lift_abs) tpairs,
      prop = Logic.list_implies (map lift_all As, lift_all B)}
  end;

fun incr_indexes i (thm as Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  if i < 0 then raise THM ("negative increment", 0, [thm])
  else if i = 0 then thm
  else
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs'
        (Pt.map_proof_terms (Logic.incr_indexes ([], i)) (Logic.incr_tvar i)) der,
      maxidx = maxidx + i,
      shyps = shyps,
      hyps = hyps,
      tpairs = map (pairself (Logic.incr_indexes ([], i))) tpairs,
      prop = Logic.incr_indexes ([], i) prop};

(*Solve subgoal Bi of proof state B1...Bn/C by assumption. *)
fun assumption i state =
  let
    val Thm {thy_ref, der, maxidx, shyps, hyps, prop, ...} = state;
    val thy = Theory.deref thy_ref;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    fun newth n (env as Envir.Envir {maxidx, ...}, tpairs) =
      Thm {thy_ref = thy_ref,
        der = Pt.infer_derivs'
          ((if Envir.is_empty env then I else (Pt.norm_proof' env)) o
            Pt.assumption_proof Bs Bi n) der,
        maxidx = maxidx,
        shyps = may_insert_env_sorts thy env shyps,
        hyps = hyps,
        tpairs =
          if Envir.is_empty env then tpairs
          else map (pairself (Envir.norm_term env)) tpairs,
        prop =
          if Envir.is_empty env then (*avoid wasted normalizations*)
            Logic.list_implies (Bs, C)
          else (*normalize the new rule fully*)
            Envir.norm_term env (Logic.list_implies (Bs, C))};
    fun addprfs [] _ = Seq.empty
      | addprfs ((t, u) :: apairs) n = Seq.make (fn () => Seq.pull
          (Seq.mapp (newth n)
            (Unify.unifiers (thy, Envir.empty maxidx, (t, u) :: tpairs))
            (addprfs apairs (n + 1))))
  in addprfs (Logic.assum_pairs (~1, Bi)) 1 end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha-convertible to one of its assumptions*)
fun eq_assumption i state =
  let
    val Thm {thy_ref, der, maxidx, shyps, hyps, prop, ...} = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
  in
    (case find_index (op aconv) (Logic.assum_pairs (~1, Bi)) of
      ~1 => raise THM ("eq_assumption", 0, [state])
    | n =>
        Thm {thy_ref = thy_ref,
          der = Pt.infer_derivs' (Pt.assumption_proof Bs Bi (n + 1)) der,
          maxidx = maxidx,
          shyps = shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = Logic.list_implies (Bs, C)})
  end;


(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let
    val Thm {thy_ref, der, maxidx, shyps, hyps, prop, ...} = state;
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
        let val (ps, qs) = splitAt (m, asms)
        in list_all (params, Logic.list_implies (qs @ ps, concl)) end
      else raise THM ("rotate_rule", k, [state]);
  in
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' (Pt.rotate_proof Bs Bi m) der,
      maxidx = maxidx,
      shyps = shyps,
      hyps = hyps,
      tpairs = tpairs,
      prop = Logic.list_implies (Bs @ [Bi'], C)}
  end;


(*Rotates a rule's premises to the left by k, leaving the first j premises
  unchanged.  Does nothing if k=0 or if k equals n-j, where n is the
  number of premises.  Useful with etac and underlies defer_tac*)
fun permute_prems j k rl =
  let
    val Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop} = rl;
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
        let val (ps, qs) = splitAt (m, moved_prems)
        in Logic.list_implies (fixed_prems @ qs @ ps, concl) end
      else raise THM ("permute_prems: k", k, [rl]);
  in
    Thm {thy_ref = thy_ref,
      der = Pt.infer_derivs' (Pt.permute_prems_prf prems j m) der,
      maxidx = maxidx,
      shyps = shyps,
      hyps = hyps,
      tpairs = tpairs,
      prop = prop'}
  end;


(** User renaming of parameters in a subgoal **)

(*Calls error rather than raising an exception because it is intended
  for top-level use -- exception handling would not make sense here.
  The names in cs, if distinct, are used for the innermost parameters;
   preceding parameters may be renamed to make all params distinct.*)
fun rename_params_rule (cs, i) state =
  let
    val Thm {thy_ref, der, maxidx, shyps, hyps, ...} = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    val iparams = map #1 (Logic.strip_params Bi);
    val short = length iparams - length cs;
    val newnames =
      if short < 0 then error "More names than abstractions!"
      else variantlist (Library.take (short, iparams), cs) @ cs;
    val freenames = map (#1 o dest_Free) (term_frees Bi);
    val newBi = Logic.list_rename_params (newnames, Bi);
  in
    case findrep cs of
      c :: _ => (warning ("Can't rename.  Bound variables not distinct: " ^ c); state)
    | [] =>
      (case cs inter_string freenames of
        a :: _ => (warning ("Can't rename.  Bound/Free variable clash: " ^ a); state)
      | [] =>
        Thm {thy_ref = thy_ref,
          der = der,
          maxidx = maxidx,
          shyps = shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = Logic.list_implies (Bs @ [newBi], C)})
  end;


(*** Preservation of bound variable names ***)

fun rename_boundvars pat obj (thm as Thm {thy_ref, der, maxidx, shyps, hyps, tpairs, prop}) =
  (case Term.rename_abs pat obj prop of
    NONE => thm
  | SOME prop' => Thm
      {thy_ref = thy_ref,
       der = der,
       maxidx = maxidx,
       hyps = hyps,
       shyps = shyps,
       tpairs = tpairs,
       prop = prop'});


(* strip_apply f (A, B) strips off all assumptions/parameters from A
   introduced by lifting over B, and applies f to remaining part of A*)
fun strip_apply f =
  let fun strip(Const("==>",_)$ A1 $ B1,
                Const("==>",_)$ _  $ B2) = implies $ A1 $ strip(B1,B2)
        | strip((c as Const("all",_)) $ Abs(a,T,t1),
                      Const("all",_)  $ Abs(_,_,t2)) = c$Abs(a,T,strip(t1,t2))
        | strip(A,_) = f A
  in strip end;

(*Use the alist to rename all bound variables and some unknowns in a term
  dpairs = current disagreement pairs;  tpairs = permanent ones (flexflex);
  Preserves unknowns in tpairs and on lhs of dpairs. *)
fun rename_bvs([],_,_,_) = I
  | rename_bvs(al,dpairs,tpairs,B) =
    let val vars = foldr add_term_vars []
                        (map fst dpairs @ map fst tpairs @ map snd tpairs)
        (*unknowns appearing elsewhere be preserved!*)
        val vids = map (#1 o #1 o dest_Var) vars;
        fun rename(t as Var((x,i),T)) =
                (case assoc(al,x) of
                   SOME(y) => if x mem_string vids orelse y mem_string vids then t
                              else Var((y,i),T)
                 | NONE=> t)
          | rename(Abs(x,T,t)) =
              Abs (if_none (assoc_string (al, x)) x, T, rename t)
          | rename(f$t) = rename f $ rename t
          | rename(t) = t;
        fun strip_ren Ai = strip_apply rename (Ai,B)
    in strip_ren end;

(*Function to rename bounds/unknowns in the argument, lifted over B*)
fun rename_bvars(dpairs, tpairs, B) =
        rename_bvs(foldr Term.match_bvars [] dpairs, dpairs, tpairs, B);


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
        in  all T' $ Abs(a, T', norm_term_skip env n t)  end
  | norm_term_skip env n (Const("==>", _) $ A $ B) =
        implies $ A $ norm_term_skip env (n-1) B
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
fun bicompose_aux match (state, (stpairs, Bs, Bi, C), lifted)
                        (eres_flg, orule, nsubgoal) =
 let val Thm{der=sder, maxidx=smax, shyps=sshyps, hyps=shyps, ...} = state
     and Thm{der=rder, maxidx=rmax, shyps=rshyps, hyps=rhyps,
             tpairs=rtpairs, prop=rprop,...} = orule
         (*How many hyps to skip over during normalization*)
     and nlift = Logic.count_prems(strip_all_body Bi,
                                   if eres_flg then ~1 else 0)
     val thy_ref = merge_thys2 state orule;
     val thy = Theory.deref thy_ref;
     (** Add new theorem with prop = '[| Bs; As |] ==> C' to thq **)
     fun addth A (As, oldAs, rder', n) ((env as Envir.Envir {maxidx, ...}, tpairs), thq) =
       let val normt = Envir.norm_term env;
           (*perform minimal copying here by examining env*)
           val (ntpairs, normp) =
             if Envir.is_empty env then (tpairs, (Bs @ As, C))
             else
             let val ntps = map (pairself normt) tpairs
             in if Envir.above (smax, env) then
                  (*no assignments in state; normalize the rule only*)
                  if lifted
                  then (ntps, (Bs @ map (norm_term_skip env nlift) As, C))
                  else (ntps, (Bs @ map normt As, C))
                else if match then raise COMPOSE
                else (*normalize the new rule fully*)
                  (ntps, (map normt (Bs @ As), normt C))
             end
           val th =
             Thm{thy_ref = thy_ref,
                 der = Pt.infer_derivs
                   ((if Envir.is_empty env then I
                     else if Envir.above (smax, env) then
                       (fn f => fn der => f (Pt.norm_proof' env der))
                     else
                       curry op oo (Pt.norm_proof' env))
                    (Pt.bicompose_proof Bs oldAs As A n)) rder' sder,
                 maxidx = maxidx,
                 shyps = may_insert_env_sorts thy env (Sorts.union rshyps sshyps),
                 hyps = union_hyps rhyps shyps,
                 tpairs = ntpairs,
                 prop = Logic.list_implies normp}
        in  Seq.cons(th, thq)  end  handle COMPOSE => thq;
     val (rAs,B) = Logic.strip_prems(nsubgoal, [], rprop)
       handle TERM _ => raise THM("bicompose: rule", 0, [orule,state]);
     (*Modify assumptions, deleting n-th if n>0 for e-resolution*)
     fun newAs(As0, n, dpairs, tpairs) =
       let val (As1, rder') =
         if !Logic.auto_rename orelse not lifted then (As0, rder)
         else (map (rename_bvars(dpairs,tpairs,B)) As0,
           Pt.infer_derivs' (Pt.map_proof_terms
             (rename_bvars (dpairs, tpairs, Bound 0)) I) rder);
       in (map (Logic.flatten_params n) As1, As1, rder', n)
          handle TERM _ =>
          raise THM("bicompose: 1st premise", 0, [orule])
       end;
     val env = Envir.empty(Int.max(rmax,smax));
     val BBi = if lifted then strip_assums2(B,Bi) else (B,Bi);
     val dpairs = BBi :: (rtpairs@stpairs);
     (*elim-resolution: try each assumption in turn.  Initially n=1*)
     fun tryasms (_, _, _, []) = Seq.empty
       | tryasms (A, As, n, (t,u)::apairs) =
          (case Seq.pull(Unify.unifiers(thy, env, (t,u)::dpairs))  of
              NONE                   => tryasms (A, As, n+1, apairs)
            | cell as SOME((_,tpairs),_) =>
                Seq.it_right (addth A (newAs(As, n, [BBi,(u,t)], tpairs)))
                    (Seq.make(fn()=> cell),
                     Seq.make(fn()=> Seq.pull (tryasms(A, As, n+1, apairs)))))
     fun eres [] = raise THM("bicompose: no premises", 0, [orule,state])
       | eres (A1::As) = tryasms(SOME A1, As, 1, Logic.assum_pairs(nlift+1,A1))
     (*ordinary resolution*)
     fun res(NONE) = Seq.empty
       | res(cell as SOME((_,tpairs),_)) =
             Seq.it_right (addth NONE (newAs(rev rAs, 0, [BBi], tpairs)))
                       (Seq.make (fn()=> cell), Seq.empty)
 in  if eres_flg then eres(rev rAs)
     else res(Seq.pull(Unify.unifiers(thy, env, dpairs)))
 end;
end;


fun bicompose match arg i state =
    bicompose_aux match (state, dest_state(state,i), false) arg;

(*Quick test whether rule is resolvable with the subgoal with hyps Hs
  and conclusion B.  If eres_flg then checks 1st premise of rule also*)
fun could_bires (Hs, B, eres_flg, rule) =
    let fun could_reshyp (A1::_) = exists (fn H => could_unify (A1, H)) Hs
          | could_reshyp [] = false;  (*no premise -- illegal*)
    in  could_unify(concl_of rule, B) andalso
        (not eres_flg  orelse  could_reshyp (prems_of rule))
    end;

(*Bi-resolution of a state with a list of (flag,rule) pairs.
  Puts the rule above:  rule/state.  Renames vars in the rules. *)
fun biresolution match brules i state =
    let val lift = lift_rule(state, i);
        val (stpairs, Bs, Bi, C) = dest_state(state,i)
        val B = Logic.strip_assums_concl Bi;
        val Hs = Logic.strip_assums_hyp Bi;
        val comp = bicompose_aux match (state, (stpairs, Bs, Bi, C), true);
        fun res [] = Seq.empty
          | res ((eres_flg, rule)::brules) =
              if !Pattern.trace_unify_fail orelse
                 could_bires (Hs, B, eres_flg, rule)
              then Seq.make (*delay processing remainder till needed*)
                  (fn()=> SOME(comp (eres_flg, lift rule, nprems_of rule),
                               res brules))
              else res brules
    in  Seq.flat (res brules)  end;


(*** Oracles ***)

fun invoke_oracle_i thy1 name =
  let
    val oracle =
      (case Symtab.lookup (#2 (#oracles (Theory.rep_theory thy1)), name) of
        NONE => raise THM ("Unknown oracle: " ^ name, 0, [])
      | SOME (f, _) => f);
    val thy_ref1 = Theory.self_ref thy1;
  in
    fn (thy2, data) =>
      let
        val thy' = Theory.merge (Theory.deref thy_ref1, thy2);
        val (prop, T, maxidx) =
          Sign.certify_term (Sign.pp thy') thy' (oracle (thy', data));
      in
        if T <> propT then
          raise THM ("Oracle's result must have type prop: " ^ name, 0, [])
        else
          Thm {thy_ref = Theory.self_ref thy',
            der = (true, Pt.oracle_proof name prop),
            maxidx = maxidx,
            shyps = may_insert_term_sorts thy' prop [],
            hyps = [],
            tpairs = [],
            prop = prop}
      end
  end;

fun invoke_oracle thy =
  invoke_oracle_i thy o NameSpace.intern (Theory.oracle_space thy);

end;

structure BasicThm: BASIC_THM = Thm;
open BasicThm;
