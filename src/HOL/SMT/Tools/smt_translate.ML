(*  Title:      HOL/SMT/Tools/smt_translate.ML
    Author:     Sascha Boehme, TU Muenchen

Translate theorems into an SMT intermediate format and serialize them,
depending on an SMT interface.
*)

signature SMT_TRANSLATE =
sig
  (* intermediate term structure *)
  datatype sym =
    SConst of string * typ |
    SFree of string * typ |
    SNum of int * typ
  datatype squant = SForall | SExists
  datatype 'a spattern = SPat of 'a list | SNoPat of 'a list
  datatype ('a, 'b) sterm =
    SVar of int |
    SApp of 'a * ('a, 'b) sterm list |
    SLet of (string * 'b) * ('a, 'b) sterm * ('a, 'b) sterm |
    SQuant of squant * (string * 'b) list * ('a, 'b) sterm spattern list *
      ('a, 'b) sterm

  (* table for built-in symbols *)
  type builtin_fun = typ -> (sym, typ) sterm list ->
    (string * (sym, typ) sterm list) option
  type builtin_table = (typ * builtin_fun) list Symtab.table
  val builtin_make: (term * string) list -> builtin_table
  val builtin_add: term * builtin_fun -> builtin_table -> builtin_table
  val builtin_lookup: builtin_table -> theory -> string * typ ->
    (sym, typ) sterm list -> (string * (sym, typ) sterm list) option
  val bv_rotate: (int -> string) -> builtin_fun
  val bv_extend: (int -> string) -> builtin_fun
  val bv_extract: (int -> int -> string) -> builtin_fun

  (* configuration options *)
  type prefixes = {
    var_prefix: string,
    typ_prefix: string,
    fun_prefix: string,
    pred_prefix: string }
  type markers = {
    term_marker: string,
    formula_marker: string }
  type builtins = {
    builtin_typ: typ -> string option,
    builtin_num: int * typ -> string option,
    builtin_fun: bool -> builtin_table }
  type sign = {
    typs: string list,
    funs: (string * (string list * string)) list,
    preds: (string * string list) list }
  type config = {
    strict: bool,
    prefixes: prefixes,
    markers: markers,
    builtins: builtins,
    serialize: sign -> (string, string) sterm list -> TextIO.outstream -> unit}
  type recon = {typs: typ Symtab.table, terms: term Symtab.table}

  val translate: config -> theory -> thm list -> TextIO.outstream ->
    recon * thm list

  val dest_binT: typ -> int
  val dest_funT: int -> typ -> typ list * typ
end

structure SMT_Translate: SMT_TRANSLATE =
struct

(* Intermediate term structure *)

datatype sym =
  SConst of string * typ |
  SFree of string * typ |
  SNum of int * typ
datatype squant = SForall | SExists
datatype 'a spattern = SPat of 'a list | SNoPat of 'a list
datatype ('a, 'b) sterm =
  SVar of int |
  SApp of 'a * ('a, 'b) sterm list |
  SLet of (string * 'b) * ('a, 'b) sterm * ('a, 'b) sterm |
  SQuant of squant * (string * 'b) list * ('a, 'b) sterm spattern list *
    ('a, 'b) sterm

fun app c ts = SApp (c, ts)

fun map_pat f (SPat ps) = SPat (map f ps)
  | map_pat f (SNoPat ps) = SNoPat (map f ps)

fun fold_map_pat f (SPat ps) = fold_map f ps #>> SPat
  | fold_map_pat f (SNoPat ps) = fold_map f ps #>> SNoPat

val make_sconst = SConst o Term.dest_Const


(* General type destructors. *)

fun dest_binT T =
  (case T of
    Type (@{type_name "Numeral_Type.num0"}, _) => 0
  | Type (@{type_name "Numeral_Type.num1"}, _) => 1
  | Type (@{type_name "Numeral_Type.bit0"}, [T]) => 2 * dest_binT T
  | Type (@{type_name "Numeral_Type.bit1"}, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

val dest_wordT = (fn
    Type (@{type_name "word"}, [T]) => dest_binT T
  | T => raise TYPE ("dest_wordT", [T], []))

val dest_funT =
  let
    fun dest Ts 0 T = (rev Ts, T)
      | dest Ts i (Type ("fun", [T, U])) = dest (T::Ts) (i-1) U
      | dest _ _ T = raise TYPE ("dest_funT", [T], [])
  in dest [] end


(* Table for built-in symbols *)

type builtin_fun = typ -> (sym, typ) sterm list ->
  (string * (sym, typ) sterm list) option
type builtin_table = (typ * builtin_fun) list Symtab.table

fun builtin_make entries =
  let
    fun dest (t, bn) =
      let val (n, T) = Term.dest_Const t
      in (n, (Logic.varifyT T, K (SOME o pair bn))) end
  in Symtab.make (AList.group (op =) (map dest entries)) end

fun builtin_add (t, f) tab =
  let val (n, T) = apsnd Logic.varifyT (Term.dest_Const t)
  in Symtab.map_default (n, []) (AList.update (op =) (T, f)) tab end

fun builtin_lookup tab thy (n, T) ts =
  AList.lookup (Sign.typ_instance thy) (Symtab.lookup_list tab n) T
  |> (fn SOME f => f T ts | NONE => NONE)

local
  val dest_nat = (fn
      SApp (SConst (@{const_name nat}, _), [SApp (SNum (i, _), _)]) => SOME i
    | _ => NONE)
in
fun bv_rotate mk_name T ts =
  dest_nat (hd ts) |> Option.map (fn i => (mk_name i, tl ts))

fun bv_extend mk_name T ts =
  (case (try dest_wordT (domain_type T), try dest_wordT (range_type T)) of
    (SOME i, SOME j) => if j - i >= 0 then SOME (mk_name (j - i), ts) else NONE
  | _ => NONE)

fun bv_extract mk_name T ts =
  (case (try dest_wordT (body_type T), dest_nat (hd ts)) of
    (SOME i, SOME lb) => SOME (mk_name (i + lb - 1) lb, tl ts)
  | _ => NONE)
end


(* Configuration options *)

type prefixes = {
  var_prefix: string,
  typ_prefix: string,
  fun_prefix: string,
  pred_prefix: string }
type markers = {
  term_marker: string,
  formula_marker: string }
type builtins = {
  builtin_typ: typ -> string option,
  builtin_num: int * typ -> string option,
  builtin_fun: bool -> builtin_table }
type sign = {
  typs: string list,
  funs: (string * (string list * string)) list,
  preds: (string * string list) list }
type config = {
  strict: bool,
  prefixes: prefixes,
  markers: markers,
  builtins: builtins,
  serialize: sign -> (string, string) sterm list -> TextIO.outstream -> unit}
type recon = {typs: typ Symtab.table, terms: term Symtab.table}


(* Translate Isabelle/HOL terms into SMT intermediate terms.
   We assume that lambda-lifting has been performed before, i.e., lambda
   abstractions occur only at quantifiers and let expressions.
*)
local
  val quantifier = (fn
      @{const_name All} => SOME SForall
    | @{const_name Ex} => SOME SExists
    | _ => NONE)

  fun group_quant qname vs (t as Const (q, _) $ Abs (n, T, u)) =
        if q = qname then group_quant qname ((n, T) :: vs) u else (vs, t)
    | group_quant qname vs t = (vs, t)

  fun dest_trigger (@{term trigger} $ tl $ t) = (HOLogic.dest_list tl, t)
    | dest_trigger t = ([], t)

  fun pat f ps (Const (@{const_name pat}, _) $ p) = SPat (rev (f p :: ps))
    | pat f ps (Const (@{const_name nopat}, _) $ p) = SNoPat (rev (f p :: ps))
    | pat f ps (Const (@{const_name andpat}, _) $ p $ t) = pat f (f p :: ps) t
    | pat _ _ t = raise TERM ("pat", [t])

  fun trans Ts t =
    (case Term.strip_comb t of
      (t1 as Const (qn, qT), [t2 as Abs (n, T, t3)]) =>
        (case quantifier qn of
          SOME q =>
            let
              val (vs, u) = group_quant qn [(n, T)] t3
              val Us = map snd vs @ Ts
              val (ps, b) = dest_trigger u
            in SQuant (q, rev vs, map (pat (trans Us) []) ps, trans Us b) end
        | NONE => raise TERM ("intermediate", [t]))
    | (Const (@{const_name Let}, _), [t1, Abs (n, T, t2)]) =>
        SLet ((n, T), trans Ts t1, trans (T :: Ts) t2)
    | (Const (c as (@{const_name distinct}, _)), [t1]) =>
        (* this is not type-correct, but will be corrected at a later stage *)
        SApp (SConst c, map (trans Ts) (HOLogic.dest_list t1))
    | (Const c, ts) =>
        (case try HOLogic.dest_number t of
          SOME (T, i) => SApp (SNum (i, T), [])
        | NONE => SApp (SConst c, map (trans Ts) ts))
    | (Free c, ts) => SApp (SFree c, map (trans Ts) ts)
    | (Bound i, []) => SVar i
    | _ => raise TERM ("intermediate", [t]))
in
fun intermediate ts = map (trans [] o HOLogic.dest_Trueprop) ts
end


(* Separate formulas from terms by adding special marker symbols ("term",
   "formula"). Atoms "P" whose head symbol also occurs as function symbol are
   rewritten to "term P = term True". Connectives and built-in predicates
   occurring at term level are replaced by new constants, and theorems
   specifying their meaning are added.
*)
local
  (** Add the marker symbols "term" and "formulas" to separate formulas and
      terms. **)

  val connectives = map make_sconst [@{term True}, @{term False},
    @{term Not}, @{term "op &"}, @{term "op |"}, @{term "op -->"},
    @{term "op = :: bool => _"}]

  fun note false c (ps, fs) = (insert (op =) c ps, fs)
    | note true c (ps, fs) = (ps, insert (op =) c fs)

  val term_marker = SConst (@{const_name term}, Term.dummyT)
  val formula_marker = SConst (@{const_name formula}, Term.dummyT)
  fun mark f true t = f true t #>> app term_marker o single
    | mark f false t = f false t #>> app formula_marker o single
  fun mark' f false t = f true t #>> app term_marker o single
    | mark' f true t = f true t
  val mark_term = app term_marker o single
  fun lift_term_marker c ts =
    let val rem = (fn SApp (SConst (@{const_name term}, _), [t]) => t | t => t)
    in mark_term (SApp (c, map rem ts)) end
  fun is_term (SApp (SConst (@{const_name term}, _), _)) = true
    | is_term _ = false

  fun either x = (fn y as SOME _ => y | _ => x)
  fun get_loc loc i t =
    (case t of
      SVar j => if i = j then SOME loc else NONE
    | SApp (SConst (@{const_name term}, _), us) => get_locs true i us
    | SApp (SConst (@{const_name formula}, _), us) => get_locs false i us
    | SApp (_, us) => get_locs loc i us
    | SLet (_, u1, u2) => either (get_loc true i u1) (get_loc loc (i+1) u2)
    | SQuant (_, vs, _, u) => get_loc loc (i + length vs) u)
  and get_locs loc i ts = fold (either o get_loc loc i) ts NONE

  fun sep loc t =
    (case t of
      SVar i => pair t
    | SApp (c as SConst (@{const_name If}, _), u :: us) =>
        mark sep false u ##>> fold_map (sep loc) us #>> app c o (op ::)
    | SApp (c, us) =>
        if not loc andalso member (op =) connectives c
        then fold_map (sep loc) us #>> app c
        else note loc c #> fold_map (mark' sep loc) us #>> app c
    | SLet (v, u1, u2) =>
        sep loc u2 #-> (fn u2' =>
        mark sep (the (get_loc loc 0 u2')) u1 #>> (fn u1' =>
        SLet (v, u1', u2')))
    | SQuant (q, vs, ps, u) =>
        fold_map (fold_map_pat (mark sep true)) ps ##>>
        sep loc u #>> (fn (ps', u') =>
        SQuant (q, vs, ps', u')))

  (** Rewrite atoms. **)

  val unterm_rule = @{lemma "term x == x" by (simp add: term_def)}
  val unterm_conv = More_Conv.top_sweep_conv (K (Conv.rewr_conv unterm_rule))

  val dest_word_type = (fn Type (@{type_name word}, [T]) => T | T => T)
  fun instantiate [] _ = I
    | instantiate (v :: _) T =
        Term.subst_TVars [(v, dest_word_type (Term.domain_type T))]

  fun dest_alls (Const (@{const_name All}, _) $ Abs (_, _, t)) = dest_alls t
    | dest_alls t = t
  val dest_iff = (fn (Const (@{const_name iff}, _) $ t $ _ ) => t | t => t)
  val dest_eq = (fn (Const (@{const_name "op ="}, _) $ t $ _ ) => t | t => t)
  val dest_not = (fn (@{term Not} $ t) => t | t => t)
  val head_of = HOLogic.dest_Trueprop #> dest_alls #> dest_iff #> dest_not #>
    dest_eq #> Term.head_of

  fun prepare ctxt thm =
    let
      val rule = Conv.fconv_rule (unterm_conv ctxt) thm
      val prop = Thm.prop_of thm
      val inst = instantiate (Term.add_tvar_names prop [])
      fun inst_for T = (singleton intermediate (inst T prop), rule)
    in (make_sconst (head_of (Thm.prop_of rule)), inst_for) end

  val logicals = map (prepare @{context})
    @{lemma 
      "~ holds False"
      "ALL p. holds (~ p) iff (~ holds p)"
      "ALL p q. holds (p & q) iff (holds p & holds q)"
      "ALL p q. holds (p | q) iff (holds p | holds q)"
      "ALL p q. holds (p --> q) iff (holds p --> holds q)"
      "ALL p q. holds (p iff q) iff (holds p iff holds q)"
      "ALL p q. holds (p = q) iff (p = q)"
      "ALL (a::int) b. holds (a < b) iff (a < b)"
      "ALL (a::int) b. holds (a <= b) iff (a <= b)"
      "ALL (a::real) b. holds (a < b) iff (a < b)"
      "ALL (a::real) b. holds (a <= b) iff (a <= b)"
      "ALL (a::'a::len0 word) b. holds (a < b) iff (a < b)"
      "ALL (a::'a::len0 word) b. holds (a <= b) iff (a <= b)"
      "ALL a b. holds (a <s b) iff (a <s b)"
      "ALL a b. holds (a <=s b) iff (a <=s b)"
      by (simp_all add: term_def iff_def)}

  fun is_instance thy (SConst (n, T), SConst (m, U)) =
        (n = m) andalso Sign.typ_instance thy (T, U)
    | is_instance _ _ = false

  fun lookup_logical thy (c as SConst (_, T)) =
        AList.lookup (is_instance thy) logicals c
        |> Option.map (fn inst_for => inst_for T)
    | lookup_logical _ _ = NONE

  val s_eq = make_sconst @{term "op = :: bool => _"}
  val s_True = mark_term (SApp (make_sconst @{term True}, []))
  fun holds (SApp (c, ts)) = SApp (s_eq, [lift_term_marker c ts, s_True])
    | holds t = SApp (s_eq, [mark_term t, s_True])

  val rewr_iff = (fn
      SConst (@{const_name "op ="}, T as @{typ "bool => bool => bool"}) =>
        SConst (@{const_name iff}, T)
    | c => c)

  fun rewrite ls =
    let
      fun rewr env loc t =
        (case t of
          SVar i => if not loc andalso nth env i then holds t else t
        | SApp (c as SConst (@{const_name term}, _), [u]) =>
            SApp (c, [rewr env true u])
        | SApp (c as SConst (@{const_name formula}, _), [u]) =>
            SApp (c, [rewr env false u])
        | SApp (c, us) =>
            let val f = if not loc andalso member (op =) ls c then holds else I
            in f (SApp (rewr_iff c, map (rewr env loc) us)) end
        | SLet (v, u1, u2) =>
            SLet (v, rewr env loc u1, rewr (is_term u1 :: env) loc u2)
        | SQuant (q, vs, ps, u) =>
            let val e = replicate (length vs) true @ env
            in SQuant (q, vs, map (map_pat (rewr e loc)) ps, rewr e loc u) end)
    in map (rewr [] false) end
in
fun separate thy ts =
  let
    val (ts', (ps, fs)) = fold_map (sep false) ts ([], [])
    val eq_name = (fn
        (SConst (n, _), SConst (m, _)) => n = m
      | (SFree (n, _), SFree (m, _)) => n = m
      | _ => false)
    val ls = filter (member eq_name fs) ps
    val (us, thms) = split_list (map_filter (lookup_logical thy) fs)
  in (thms, us @ rewrite ls ts') end
end


(* Collect the signature of intermediate terms, identify built-in symbols,
   rename uninterpreted symbols and types, make bound variables unique.
   We require @{term distinct} to be a built-in constant of the SMT solver.
*)
local
  fun empty_nctxt p = (p, 1)
  fun make_nctxt (pT, pf, pp) = (empty_nctxt pT, empty_nctxt (pf, pp))
  fun fresh_name (p, i) = (p ^ string_of_int i, (p, i+1))
  fun fresh_typ (nT, nfp) = fresh_name nT ||> (fn nT' => (nT', nfp))
  fun fresh_fun loc (nT, ((pf, pp), i)) =
    let val p = if loc then pf else pp
    in fresh_name (p, i) ||> (fn (_, i') => (nT, ((pf, pp), i'))) end

  val empty_sign = (Typtab.empty, Termtab.empty, Termtab.empty)
  fun lookup_typ (typs, _, _) = Typtab.lookup typs
  fun lookup_fun true (_, funs, _) = Termtab.lookup funs
    | lookup_fun false (_, _, preds) = Termtab.lookup preds
  fun add_typ x (typs, funs, preds) = (Typtab.update x typs, funs, preds)
  fun add_fun true x (typs, funs, preds) = (typs, Termtab.update x funs, preds)
    | add_fun false x (typs, funs, preds) = (typs, funs, Termtab.update x preds)
  fun make_sign (typs, funs, preds) = {
    typs = map snd (Typtab.dest typs),
    funs = map snd (Termtab.dest funs),
    preds = map (apsnd fst o snd) (Termtab.dest preds) }
  fun make_rtab (typs, funs, preds) =
    let
      val rTs = Typtab.dest typs |> map swap |> Symtab.make
      val rts = Termtab.dest funs @ Termtab.dest preds
        |> map (apfst fst o swap) |> Symtab.make
    in {typs=rTs, terms=rts} end

  fun either f g x = (case f x of NONE => g x | y => y)

  fun rep_typ ({builtin_typ, ...} : builtins) T (st as (vars, ns, sgn)) =
    (case either builtin_typ (lookup_typ sgn) T of
      SOME n => (n, st)
    | NONE =>
        let val (n, ns') = fresh_typ ns
        in (n, (vars, ns', add_typ (T, n) sgn)) end)

  fun rep_var bs (n, T) (vars, ns, sgn) =
    let val (n', vars') = fresh_name vars
    in (vars', ns, sgn) |> rep_typ bs T |>> pair n' end

  fun rep_fun bs loc t T i (st as (_, _, sgn0)) =
    (case lookup_fun loc sgn0 t of
      SOME (n, _) => (n, st)
    | NONE =>
        let
          val (Us, U) = dest_funT i T
          val (uns, (vars, ns, sgn)) =
            st |> fold_map (rep_typ bs) Us ||>> rep_typ bs U
          val (n, ns') = fresh_fun loc ns
        in (n, (vars, ns', add_fun loc (t, (n, uns)) sgn)) end)

  fun rep_num (bs as {builtin_num, ...} : builtins) (i, T) st =
    (case builtin_num (i, T) of
      SOME n => (n, st)
    | NONE => rep_fun bs true (HOLogic.mk_number T i) T 0 st)
in
fun signature_of prefixes markers builtins thy ts =
  let
    val {var_prefix, typ_prefix, fun_prefix, pred_prefix} = prefixes
    val {formula_marker, term_marker} = markers
    val {builtin_fun, ...} = builtins

    fun sign loc t =
      (case t of
        SVar i => pair (SVar i)
      | SApp (c as SConst (@{const_name term}, _), [u]) =>
          sign true u #>> app term_marker o single
      | SApp (c as SConst (@{const_name formula}, _), [u]) =>
          sign false u #>> app formula_marker o single
      | SApp (SConst (c as (_, T)), ts) =>
          (case builtin_lookup (builtin_fun loc) thy c ts of
            SOME (n, ts') => fold_map (sign loc) ts' #>> app n
          | NONE =>
              rep_fun builtins loc (Const c) T (length ts) ##>>
              fold_map (sign loc) ts #>> SApp)
      | SApp (SFree (c as (_, T)), ts) =>
          rep_fun builtins loc (Free c) T (length ts) ##>>
          fold_map (sign loc) ts #>> SApp
      | SApp (SNum n, _) => rep_num builtins n #>> (fn n => SApp (n, []))
      | SLet (v, u1, u2) =>
          rep_var builtins v #-> (fn v' =>
          sign loc u1 ##>> sign loc u2 #>> (fn (u1', u2') =>
          SLet (v', u1', u2')))
      | SQuant (q, vs, ps, u) =>
          fold_map (rep_var builtins) vs ##>>
          fold_map (fold_map_pat (sign loc)) ps ##>>
          sign loc u #>> (fn ((vs', ps'), u') =>
          SQuant (q, vs', ps', u')))
  in
    (empty_nctxt var_prefix, make_nctxt (typ_prefix, fun_prefix, pred_prefix),
      empty_sign)
    |> fold_map (sign false) ts
    |> (fn (us, (_, _, sgn)) => (make_rtab sgn, (make_sign sgn, us)))
  end
end


(* Combination of all translation functions and invocation of serialization. *)

fun translate config thy thms stream =
  let val {strict, prefixes, markers, builtins, serialize} = config
  in
    map Thm.prop_of thms
    |> SMT_Monomorph.monomorph thy
    |> intermediate
    |> (if strict then separate thy else pair [])
    ||>> signature_of prefixes markers builtins thy
    ||> (fn (sgn, ts) => serialize sgn ts stream)
    |> (fn ((thms', rtab), _) => (rtab, thms' @ thms))
  end

end
