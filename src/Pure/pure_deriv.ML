(*  Title:      Pure/pure_deriv.ML
    Author:     Makarius

The pure logic behind Isabelle/Pure: derivations of regular thm.ML (which is
sometimes called "the inference kernel").
*)

signature PURE_DERIV =
sig
  val strip_sortsT: Pure_Term.T -> Pure_Term.T
  val strip_sorts: Pure_Term.t -> Pure_Term.t
  val maxidx_type: Pure_Term.T -> int -> int
  val maxidx_term: Pure_Term.t -> int -> int
  val maxidx_proof: Pure_Logic.proof -> int -> int
  val pure_type_of: typ -> Pure_Term.T
  val typ_of_tvar: Var_Name.T * sort -> typ
  val typ_of: Pure_Term.T -> typ
  val init_cache: theory -> theory option
  val exit_cache: theory -> theory option
  val reset_cache: theory -> theory
  val check_cache: theory -> {pure_type: int, typ: int} option
  val pure_type_cache: theory -> typ -> Pure_Term.T
  val typ_cache: theory -> Pure_Term.T -> typ
  val pure_term_cache: theory -> {pure_term: term -> Pure_Term.t, pure_type: typ -> Pure_Term.T}
  val pure_term_of: theory -> term -> Pure_Term.t
  val pure_term_dummy_pattern: Pure_Term.T -> Pure_Term.t
  val pure_term_type: Pure_Term.T -> Pure_Term.t
  val term_of: theory -> Pure_Term.t -> term
  val norm_type: theory -> Type.tyenv -> Pure_Term.T -> Pure_Term.T
  val norm_term: theory -> Envir.env -> Pure_Term.t -> Pure_Term.t
  val norm_proof: theory -> Envir.env -> term list -> Pure_Logic.proof -> Pure_Logic.proof
  type box = serial * (Pure_Term.t * Pure_Logic.proof)
  val box_ord: box ord
  type boxes = box Ord_List.T
  val union_boxes: boxes -> boxes -> boxes
  val unions_boxes: boxes list -> boxes
  val add_box_proof: {unconstrain: bool} -> theory ->
    term list -> term -> Pure_Logic.proof -> boxes -> Pure_Logic.proof * boxes
  val thm_proof: theory -> Thm_Name.P -> term list -> term ->
    Pure_Logic.proof -> box * Pure_Logic.proof
  val axiom_proof:  theory -> string -> term -> Pure_Logic.proof
  val oracle_proof:  theory -> string -> term -> Pure_Logic.proof
  val assume_proof: theory -> term -> Pure_Logic.proof
  val trivial_proof: theory -> term -> Pure_Logic.proof
  val implies_intr_proof': Pure_Term.t -> Pure_Logic.proof -> Pure_Logic.proof
  val implies_intr_proof: theory -> term -> Pure_Logic.proof -> Pure_Logic.proof
  val forall_intr_proof: theory -> typ -> string * term -> Pure_Logic.proof -> Pure_Logic.proof
  val forall_elim_proof: theory -> term -> Pure_Logic.proof -> Pure_Logic.proof
  val of_class_proof: typ * class -> Pure_Logic.proof
  val reflexive_proof: theory -> typ -> term -> Pure_Logic.proof
  val symmetric_proof: theory -> typ -> term -> term -> Pure_Logic.proof -> Pure_Logic.proof
  val transitive_proof: theory -> typ -> term -> term -> term ->
    Pure_Logic.proof -> Pure_Logic.proof -> Pure_Logic.proof
  val equal_intr_proof: theory -> term -> term ->
    Pure_Logic.proof -> Pure_Logic.proof -> Pure_Logic.proof
  val equal_elim_proof: theory -> term -> term ->
    Pure_Logic.proof -> Pure_Logic.proof -> Pure_Logic.proof
  val abstract_rule_proof: theory -> typ -> typ -> string * term -> term -> term ->
    Pure_Logic.proof -> Pure_Logic.proof
  val combination_proof: theory -> typ -> typ -> term -> term -> term -> term ->
    Pure_Logic.proof -> Pure_Logic.proof -> Pure_Logic.proof
  val generalize_proof: Names.set * Names.set -> int -> Pure_Logic.proof -> Pure_Logic.proof
  val instantiate_proof: theory ->
    ((Var_Name.T * sort) * typ) list * ((Var_Name.T * typ) * term) list ->
    Pure_Logic.proof -> Pure_Logic.proof
  val varifyT_proof: ((string * sort) * (Var_Name.T * sort)) list ->
    Pure_Logic.proof -> Pure_Logic.proof
  val legacy_freezeT_proof: term -> Pure_Logic.proof -> Pure_Logic.proof
  val rotate_proof: theory -> term list -> term -> (string * typ) list ->
    term list -> int -> Pure_Logic.proof -> Pure_Logic.proof
  val permute_prems_proof: theory -> term list -> int -> int -> Pure_Logic.proof -> Pure_Logic.proof
  val incr_indexes_proof: int -> Pure_Logic.proof -> Pure_Logic.proof
  val lift_proof: theory -> term -> int -> term list -> Pure_Logic.proof -> Pure_Logic.proof
  val assumption_proof: theory -> Envir.env -> term list -> term -> int -> term list ->
    Pure_Logic.proof -> Pure_Logic.proof
  val bicompose_proof: theory -> Envir.env -> int -> bool -> term list -> term list ->
    term option -> term list -> int -> int -> term list ->
    Pure_Logic.proof -> Pure_Logic.proof -> Pure_Logic.proof
  type sorts_proof =
    (class * class -> Pure_Logic.proof) * (string * class list list * class -> Pure_Logic.proof)
  val of_sort_proof: Sorts.algebra -> sorts_proof -> (typ * class -> Pure_Logic.proof) ->
    typ * sort -> Pure_Logic.proof list
  val unconstrainT_proof: theory -> sorts_proof -> Logic.unconstrain_context ->
    Pure_Logic.proof -> Pure_Logic.proof
  val standard_vars: Name.context -> Pure_Term.t * Pure_Logic.proof option ->
    {typargs: (string * sort) list, args: (string * Pure_Term.T) list, prop: Pure_Term.t,
     proof: Pure_Logic.proof option}
end;

structure Pure_Deriv: PURE_DERIV =
struct

open Basic_Pure_Term Basic_Pure_Logic;


(* strip sorts *)

val strip_sortsT_same =
  Pure_Term.map_tvars_same
    (fn (_, []) => raise Same.SAME | (a, _) => TV (a, []));

val strip_sorts_same = Pure_Term.map_types_same strip_sortsT_same;

val strip_sortsT = Same.commit strip_sortsT_same;
val strip_sorts = Same.commit strip_sorts_same;


(* maximum index of variables *)

val maxidx_type = Pure_Term.fold_tvars (fn ((_, i), _) => Integer.max i);

fun maxidx_term t =
  Pure_Term.fold_types maxidx_type t #>
  Pure_Term.fold_aterms (fn FV ((_, i), _) => Integer.max i | _ => I) t;

val maxidx_proof = Pure_Logic.fold_proof {hyps = false} maxidx_type maxidx_term;


(* convert pure type vs. regular typ *)

fun pure_type_of (TFree (a, S)) = TV ((a, ~1), S)
  | pure_type_of (TVar v) = TV v
  | pure_type_of (Type ("fun", [T, U])) = FUN (pure_type_of T, pure_type_of U)
  | pure_type_of (Type ("prop", [])) = PROP
  | pure_type_of (Type (c, [])) = CON0 c
  | pure_type_of (Type (c, [T])) = CON1 (c, pure_type_of T)
  | pure_type_of (Type (c, ts)) = CONN (c, map pure_type_of ts);

fun typ_of_tvar ((a, ~1), S) = TFree (a, S)
  | typ_of_tvar v = TVar v;

fun typ_of (TV v) = typ_of_tvar v
  | typ_of (FUN (T, U)) = typ_of T --> typ_of U
  | typ_of PROP = propT
  | typ_of (CON0 c) = Type (c, [])
  | typ_of (CON1 (c, T)) = Type (c, [typ_of T])
  | typ_of (CONN (c, Ts)) = Type (c, map typ_of Ts);


(* cache within theory context *)

local

structure Data = Theory_Data
(
  type T = (T Typtab.cache_ops * typ Pure_Types.cache_ops) option;
  val empty = NONE;
  val merge = K NONE;
);

fun make_pure_type_cache () = Typtab.unsynchronized_cache pure_type_of;
fun make_typ_cache () = Pure_Types.unsynchronized_cache typ_of;

in

fun init_cache thy =
  if is_some (Data.get thy) then NONE
  else SOME (Data.put (SOME (make_pure_type_cache (), make_typ_cache ())) thy);

fun exit_cache thy =
  (case Data.get thy of
    SOME (cache1, cache2) => (#reset cache1 (); #reset cache2 (); SOME (Data.put NONE thy))
  | NONE => NONE);

val _ = Theory.setup (Theory.at_begin init_cache #> Theory.at_end exit_cache);

fun reset_cache thy =
  (case Data.get thy of
    SOME (cache1, cache2) => (#reset cache1 (); #reset cache2 (); thy)
  | NONE => thy);

fun check_cache thy =
  Data.get thy
  |> Option.map (fn (cache1, cache2) => {pure_type = #size cache1 (), typ = #size cache2 ()});

fun pure_type_cache thy =
  (case Data.get thy of
    SOME (cache, _) => cache
  | NONE => make_pure_type_cache ()) |> #apply;

fun typ_cache thy =
  (case Data.get thy of
    SOME (_, cache) => cache
  | NONE => make_typ_cache ()) |> #apply;

end;


(* convert pure term vs. regular term *)

fun pure_term_cache thy =
  let
    val typargs = Consts.typargs (Sign.consts_of thy);

    val pure_type = pure_type_cache thy;

    fun pure_term (Free (x, T)) = FV ((x, ~1), pure_type T)
      | pure_term (Var (xi, T)) = FV (xi, pure_type T)
      | pure_term (Bound i) = BV i
      | pure_term (Const (c, T)) =
          (case typargs (c, T) of
            [] => CONST0 c
          | [T] => CONST1 (c, pure_type T)
          | Ts => CONSTN (c, map pure_type Ts))
      | pure_term (Abs (a, T, b)) = ABS ((a, 0), pure_type T, pure_term b)
      | pure_term (tm as t $ u) =
          (case try Logic.match_of_class tm of
            SOME (T, c) => OFCLASS (pure_type T, c)
          | NONE => APP (pure_term t, pure_term u));
  in {pure_type = pure_type, pure_term = pure_term} end;

val pure_term_of = #pure_term o pure_term_cache;

fun pure_term_dummy_pattern T = CONST1 ("Pure.dummy_pattern", T);
fun pure_term_type T = CONST1 ("Pure.type", T);

fun term_of thy =
  let
    val instance = Consts.instance (Sign.consts_of thy);

    fun const (c, Ts) = Const (c, instance (c, Ts));

    fun term (FV ((x, ~1), T)) = Free (x, typ_of T)
      | term (FV (xi, T)) = Var (xi, typ_of T)
      | term (BV i) = Bound i
      | term (CONST0 c) = const (c, [])
      | term (CONST1 (c, T)) = const (c, [typ_of T])
      | term (CONSTN (c, Ts)) = const (c, map typ_of Ts)
      | term (ABS ((a, _), T, b)) = Abs (a, typ_of T, term b)
      | term (APP (t, u)) = term t $ term u
      | term (OFCLASS (T, c)) = Logic.mk_of_class (typ_of T, c);
  in term end;


(* normalization wrt. environment and beta contraction *)

fun norm_type_same pure_type tyenv =
  if Vartab.is_empty tyenv then Same.same
  else
    let
      fun norm (TV v) =
            (case Type.lookup tyenv v of
              SOME U => Same.commit norm (pure_type U)
            | NONE => raise Same.SAME)
        | norm (FUN (T, U)) =
            (FUN (norm T, Same.commit norm U)
              handle Same.SAME => FUN (T, norm U))
        | norm PROP = raise Same.SAME
        | norm (CON0 _) = raise Same.SAME
        | norm (CON1 (a, T)) = CON1 (a, norm T)
        | norm (CONN (a, Ts)) = CONN (a, Same.map norm Ts);
    in norm end;

fun norm_term_same {pure_type, pure_term} (envir as Envir.Envir {tyenv, tenv, ...}) =
  let
    val lookup =
      if Vartab.is_empty tenv then K NONE
      else
        Pure_Vars.apply_unsynchronized_cache
          (apsnd typ_of #> Envir.lookup envir #> Option.map pure_term);

    val normT = norm_type_same pure_type tyenv;

    fun norm (FV (xi, T)) =
          (case lookup (xi, T) of
            SOME u => Same.commit norm u
          | NONE => FV (xi, normT T))
      | norm (BV _) = raise Same.SAME
      | norm (CONST0 _) = raise Same.SAME
      | norm (CONST1 (a, T)) = CONST1 (a, normT T)
      | norm (CONSTN (a, Ts)) = CONSTN (a, Same.map normT Ts)
      | norm (ABS (a, T, t)) =
          (ABS (a, normT T, Same.commit norm t)
            handle Same.SAME => ABS (a, T, norm t))
      | norm (APP (ABS (_, _, body), t)) = Same.commit norm (Pure_Logic.subst_term_bound t body)
      | norm (APP (f, t)) =
          ((case norm f of
             ABS (_, _, body) => Same.commit norm (Pure_Logic.subst_term_bound t body)
           | nf => APP (nf, Same.commit norm t))
          handle Same.SAME => APP (f, norm t))
      | norm _ = raise Same.SAME;
  in fn t => if Envir.is_empty envir then Pure_Logic.beta_norm_term_same t else norm t end;

fun norm_proof_cache (cache as {pure_type, ...}) (envir as Envir.Envir {tyenv, ...}) =
  let
    val norm_tvar = TV #> Same.commit (norm_type_same pure_type tyenv);
    val norm_var = FV #> Same.commit (norm_term_same cache envir);
  in
    fn visible => fn prf =>
      if Envir.is_empty envir orelse null visible then Pure_Logic.beta_norm_prooft prf
      else
        let
          fun add_tvar v tab =
            if Pure_TVars.defined tab v then tab else Pure_TVars.update (v, norm_tvar v) tab;

          val inst_typ =
            if Vartab.is_empty tyenv then Same.same
            else
              Pure_TVars.build (visible |> (fold o Term.fold_types o Term.fold_atyps)
                (fn TVar v => add_tvar v | _ => I))
              |> Pure_Logic.instantiate_type_same;

          fun add_var (a, T) tab =
            let val v = (a, Same.commit inst_typ (pure_type T))
            in if Pure_Vars.defined tab v then tab else Pure_Vars.update (v, norm_var v) tab end;

          val inst_term =
            Pure_Vars.build (visible |> (fold o Term.fold_aterms) (fn Var v => add_var v | _ => I))
            |> Pure_Logic.instantiate_term_same inst_typ;

          val norm_term = Same.compose Pure_Logic.beta_norm_term_same inst_term;
        in
          Pure_Logic.beta_norm_prooft (Pure_Logic.map_proof {hyps = false} inst_typ norm_term prf)
        end
  end;

fun norm_type thy tyenv = Same.commit (norm_type_same (pure_type_cache thy) tyenv);
fun norm_term thy envir = Same.commit (norm_term_same (pure_term_cache thy) envir);
fun norm_proof thy envir = norm_proof_cache (pure_term_cache thy) envir;



(** proof construction **)

(* closed proof boxes *)

type box = serial * (t * proof);
val box_ord: box ord = fn ((i, _), (j, _)) => int_ord (j, i);

type boxes = box Ord_List.T;
val union_boxes = Ord_List.union box_ord;
val unions_boxes = Ord_List.unions box_ord;
val add_boxes = Ord_List.insert box_ord;

local

fun close_prop prems prop =
  fold_rev (fn A => fn B => APP (APP (CONST0 "Pure.imp", A), B)) prems prop;

fun close_proof prems prf =
  let
    val m = length prems - 1;
    val bounds = Pure_Terms.build (prems |> fold_index (fn (i, h) => Pure_Terms.update (h, m - i)));
    fun get_bound lev t = Pure_Terms.lookup bounds t |> Option.map (fn i => BVp (lev + i));

    fun proof lev (Hypp t) =
          (case get_bound lev t of
            SOME p => p
          | NONE => raise PURE_LOGIC ("Loose bound in proof term", [], [t], [prf]))
      | proof lev (OFCLASSp C) =
          (case get_bound lev (OFCLASS C) of
            SOME p => p
          | NONE => raise Same.SAME)
      | proof lev (Abst (x, T, p)) = Abst (x, T, proof lev p)
      | proof lev (Absp (x, t, p)) = Absp (x, t, proof (lev + 1) p)
      | proof lev (Appt (p, t)) = Appt (proof lev p, t)
      | proof lev (Appp (p, q)) =
          (Appp (proof lev p, Same.commit (proof lev) q)
            handle Same.SAME => Appp (p, proof lev q))
      | proof _ _ = raise Same.SAME;
  in Absps prems (Same.commit (proof 0) prf) end;

fun box_proof {unconstrain} thy thm_name hyps concl prf =
  let
    val {pure_term, ...} = pure_term_cache thy;

    val present_set_prf =
      Pure_TVars.build
        ((Pure_Logic.fold_proof_types {hyps = true} o Pure_Term.fold_tvars) Pure_TVars.add_set prf);
    val present_set =
      Types.build (Types.add_atyps concl #> fold Types.add_atyps hyps #>
        Pure_TVars.fold (Types.add_set o typ_of_tvar o #1) present_set_prf);
    val ucontext as {constraints, outer_constraints, ...} =
      Logic.unconstrain_context [] present_set;

    val typ_operation = #typ_operation ucontext {strip_sorts = true};
    val unconstrain_typ = Same.commit typ_operation;
    val unconstrain_pure_type =
      Pure_Types.apply_unsynchronized_cache
        (Same.function_eq (op =) (typ_of #> unconstrain_typ #> pure_type_of));
    val unconstrain_pure_term = pure_term o Term.map_types typ_operation;
    val unconstrain_proof =
      Same.commit (Pure_Logic.map_proof_types {hyps = true} unconstrain_pure_type);

    val constrain_instT =
      if unconstrain then Pure_TVars.empty
      else
        Pure_TVars.build (present_set |> Types.fold (fn (T, _) =>
          let
            val TV v = pure_type_of (unconstrain_typ T) and U = pure_type_of T;
            val equal = (case U of TV u => u = v | _ => false);
          in not equal ? Pure_TVars.add (v, U) end));
    val constrain_proof =
      if Pure_TVars.is_empty constrain_instT then I
      else
        Pure_Logic.map_proof_types {hyps = true}
          (Pure_Logic.subst_type_same (Same.function (Pure_TVars.lookup constrain_instT)));

    val hyps' = map unconstrain_pure_term hyps;
    val prems = map (pure_term o #2) constraints @ hyps';
    val prop' = Pure_Logic.beta_norm_term (close_prop prems (unconstrain_pure_term concl));
    val prf' = Pure_Logic.beta_norm_prooft (close_proof prems (unconstrain_proof prf));

    val i = serial ();
    val box: box = (i, (prop', prf'));

    val proof_name =
      Thm {theory_name = Context.theory_long_name thy, thm_name = thm_name, serial = i};

    val const = constrain_proof (Constp (Pure_Logic.proof_const (proof_name, prop')));
    val args1 =
      outer_constraints |> map (fn (T, c) =>
        OFCLASSp (pure_type_of (if unconstrain then unconstrain_typ T else T), c));
    val args2 = if unconstrain then map Hypp hyps' else map (Hypp o pure_term) hyps;
  in (box, Appps (Appps (const, args1), args2)) end;

in

val thm_proof = box_proof {unconstrain = false};

fun add_box_proof unconstrain thy hyps concl prf boxes =
  let
    val (box, prf') = box_proof unconstrain thy Thm_Name.none hyps concl prf;
    val boxes' = add_boxes box boxes;
  in (prf', boxes') end;

end;


(* basic logic *)

fun proof_axiom thy name A = Pure_Logic.proof_const (Axiom name, pure_term_of thy A);
val axiom_proof = Constp ooo proof_axiom;

fun oracle_proof thy name A =
  Constp (Pure_Logic.proof_const (Oracle name, pure_term_of thy A));

fun assume_proof thy A =
  Hypp (pure_term_of thy A);

fun trivial_proof thy A =
  Absp (Var_Name.H, pure_term_of thy A, BVp 0);

fun implies_intr_proof' h prf =
  let
    fun proof lev (Hypp t) = if Pure_Term.alpha_eq (h, t) then BVp lev else raise Same.SAME
      | proof lev (Abst (x, T, p)) = Abst (x, T, proof lev p)
      | proof lev (Absp (x, t, p)) = Absp (x, t, proof (lev + 1) p)
      | proof lev (Appt (p, t)) = Appt (proof lev p, t)
      | proof lev (Appp (p, q)) =
          (Appp (proof lev p, Same.commit (proof lev) q)
            handle Same.SAME => Appp (p, proof lev q))
      | proof _ _ = raise Same.SAME;
  in Absp (Var_Name.H, h, Same.commit (proof 0) prf) end;

fun implies_intr_proof thy = implies_intr_proof' o pure_term_of thy;

fun forall_intr_proof thy T (a, x) prf =
  let
    val {pure_type, pure_term} = pure_term_cache thy;
    val Z = pure_type T;
    val z = pure_term x;

    fun term i b =
      if Pure_Term.alpha_eq (b, z) then BV i
      else
        (case b of
          ABS (x, T, t) => ABS (x, T, term (i + 1) t)
        | APP (t, u) =>
            (APP (term i t, Same.commit (term i) u)
              handle Same.SAME => APP (t, term i u))
        | _ => raise Same.SAME);

    fun proof i (Abst (x, T, prf)) = Abst (x, T, proof (i + 1) prf)
      | proof i (Absp (x, t, prf)) =
          (Absp (x, term i t, Same.commit (proof i) prf)
            handle Same.SAME => Absp (x, t, proof i prf))
      | proof i (Appt (p, t)) =
          (Appt (proof i p, Same.commit (term i) t)
            handle Same.SAME => Appt (p, term i t))
      | proof i (Appp (p, q)) =
          (Appp (proof i p, Same.commit (proof i) q)
            handle Same.SAME => Appp (p, proof i q))
      | proof _ _ = raise Same.SAME;

  in Abst ((a, 0), Z, Same.commit (proof 0) prf) end;

fun forall_elim_proof thy t p = Appt (p, pure_term_of thy t);

fun of_class_proof (T, c) = OFCLASSp (pure_type_of T, c);


(* equality *)

local

val thy0 =
  (Theory.get_pure_bootstrap ())
  |> Sign.add_types_global [(Binding.name "fun", 2, NoSyn), (Binding.name "prop", 0, NoSyn)]
  |> Sign.local_path
  |> Sign.add_consts
   [(Binding.name "all", (Term.aT [] --> propT) --> propT, NoSyn),
    (Binding.name "imp", propT --> propT --> propT, NoSyn),
    (Binding.name "eq", Term.aT [] --> Term.aT [] --> propT, NoSyn)];

val [reflexive_axiom, symmetric_axiom, transitive_axiom, equal_intr_axiom, equal_elim_axiom,
  abstract_rule_axiom, combination_axiom] =
    Theory.equality_axioms |> map (fn (b, t) => proof_axiom thy0 (Sign.full_name thy0 b) t);

in

val is_reflexive_proof =
  fn Constp ((Axiom "Pure.reflexive", _), _) => true | _ => false;

fun reflexive_proof thy T t =
  let
    val {pure_type, pure_term} = pure_term_cache thy;
    val A = pure_type T;
    val x = pure_term t;
  in Pure_Logic.make_const_proof (fn "'a" => A, fn "x" => x) reflexive_axiom end;

fun symmetric_proof thy T t u prf =
  if is_reflexive_proof prf then prf
  else
    let
      val {pure_type, pure_term} = pure_term_cache thy;
      val A = pure_type T;
      val x = pure_term t;
      val y = pure_term u;
      val ax = Pure_Logic.make_const_proof (fn "'a" => A, fn "x" => x | "y" => y) symmetric_axiom;
    in Appp (ax, prf) end;

fun transitive_proof thy T t u v prf1 prf2 =
  if is_reflexive_proof prf1 then prf2
  else if is_reflexive_proof prf2 then prf1
  else
    let
      val {pure_type, pure_term} = pure_term_cache thy;
      val A = pure_type T;
      val x = pure_term t;
      val y = pure_term u;
      val z = pure_term v;
      val ax =
        Pure_Logic.make_const_proof (fn "'a" => A, fn "x" => x | "y" => y | "z" => z)
          transitive_axiom;
    in Appp (Appp (ax, prf1), prf2) end;

fun equal_intr_proof thy t u prf1 prf2 =
  let
    val {pure_term, ...} = pure_term_cache thy;
    val A = pure_term t;
    val B = pure_term u;
    val ax = Pure_Logic.make_const_proof (undefined, fn "A" => A | "B" => B) equal_intr_axiom;
  in Appp (Appp (ax, prf1), prf2) end;

fun equal_elim_proof thy t u prf1 prf2 =
  let
    val {pure_term, ...} = pure_term_cache thy;
    val A = pure_term t;
    val B = pure_term u;
    val ax = Pure_Logic.make_const_proof (undefined, fn "A" => A | "B" => B) equal_elim_axiom;
  in Appp (Appp (ax, prf1), prf2) end;

fun abstract_rule_proof thy T U x t u prf =
  let
    val {pure_type, pure_term} = pure_term_cache thy;
    val A = pure_type T;
    val B = pure_type U;
    val f = pure_term t;
    val g = pure_term u;
    val ax =
      Pure_Logic.make_const_proof (fn "'a" => A | "'b" => B, fn "f" => f | "g" => g)
        abstract_rule_axiom;
  in Appp (ax, forall_intr_proof thy T x prf) end;

fun combination_proof thy T U f g t u prf1 prf2 =
  let
    val {pure_type, pure_term} = pure_term_cache thy;
    val A = pure_type T;
    val B = pure_type U;
    val f' = pure_term f;
    val g' = pure_term g;
    val x = pure_term t;
    val y = pure_term u;
    val ax =
      Pure_Logic.make_const_proof
        (fn "'a" => A | "'b" => B, fn "f" => f' | "g" => g' | "x" => x | "y" => y)
        combination_axiom;
  in Appp (Appp (ax, prf1), prf2) end;

end;


(* substitution *)

fun generalize_proof (tfrees, frees) idx prf =
  let
    val typ =
      if Names.is_empty tfrees then Same.same
      else
        Pure_Types.apply_unsynchronized_cache
          (Pure_Logic.subst_type_same (fn ((a, i), S) =>
            if i = ~1 andalso Names.defined tfrees a then TV ((a, idx), S)
            else raise Same.SAME));
    val term =
      Pure_Logic.subst_term_same typ (fn ((x, i), T) =>
        if i = ~1 andalso Names.defined frees x then FV ((x, idx), T)
        else raise Same.SAME);
  in Pure_Logic.map_proof {hyps = false} typ term prf end;

fun instantiate_proof thy (Ts, ts) prf =
  let
    val {pure_type, pure_term} = pure_term_cache thy;
    val instT = Pure_TVars.build (Ts |> fold (fn (v, T) => Pure_TVars.add (v, pure_type T)));
    val inst =
      Pure_Vars.build (ts |> fold (fn ((v, T), t) => Pure_Vars.add ((v, pure_type T), pure_term t)));
    val typ = Pure_Logic.instantiate_type_same instT;
    val term = Pure_Logic.instantiate_term_same typ inst;
  in Pure_Logic.map_proof {hyps = false} typ term prf end;

fun varifyT_proof names prf =
  if null names then prf
  else
    let
      val tab = Pure_TVars.build (names |> fold (fn ((a, S), b) => Pure_TVars.add (((a, ~1), S), b)));
      val typ =
        Pure_Types.apply_unsynchronized_cache (Pure_Logic.subst_type_same (fn v =>
          (case Pure_TVars.lookup tab v of
            NONE => raise Same.SAME
          | SOME w => TV w)));
    in Pure_Logic.map_proof_types {hyps = false} typ prf end;

fun legacy_freezeT_proof t prf =
  (case Type.legacy_freezeT t of
    NONE => prf
  | SOME f =>
      let
        val tvar = pure_type_of o Same.function f;
        val typ = Pure_Types.apply_unsynchronized_cache (Pure_Logic.subst_type_same tvar);
      in Pure_Logic.map_proof_types {hyps = false} typ prf end);


(* permutations *)

fun rotate_proof thy Bs Bi' params asms m prf =
  let
    val {pure_type, pure_term} = pure_term_cache thy;
    val i = length asms;
    val j = length Bs;
  in
    Absps (map pure_term Bs @ [pure_term Bi']) (Appps (prf, map BVp
      (j downto 1) @
        [Absts (map (fn (x, T) => ((x, 0), pure_type T)) params) (Absps (map pure_term asms)
          (Appps (Appts (BVp i, map BV ((length params - 1) downto 0)),
            map BVp (((i - m - 1) downto 0) @ ((i - 1) downto (i - m))))))]))
  end;

fun permute_prems_proof thy prems' j k prf =
  let
    val {pure_term, ...} = pure_term_cache thy;
    val n = length prems';
  in
    Absps (map pure_term prems')
      (Appps (prf, map BVp ((n - 1 downto n - j) @ (k - 1 downto 0) @ (n - j - 1 downto k))))
  end;


(* lifting *)

fun incr_tvar_same inc =
  if inc = 0 then Same.same
  else
    let fun tvar ((a, i), S) = if i >= 0 then TV ((a, i + inc), S) else raise Same.SAME
    in Pure_Types.apply_unsynchronized_cache (Pure_Logic.subst_type_same tvar) end;

fun incr_indexes_proof inc prf =
  let
    val typ = incr_tvar_same inc;
    fun var ((x, i), T) = if i >= 0 then FV ((x, i + inc), T) else raise Same.SAME;
    val term = Pure_Logic.subst_term_same typ var;
  in Pure_Logic.map_proof {hyps = false} typ term prf end;

fun combound (t, n, k) =
  if k > 0 then APP (combound (t, n + 1, k - 1), BV n) else t;

fun lift_proof thy gprop inc prems prf =
  let
    val {pure_type, pure_term} = pure_term_cache thy;

    val typ = incr_tvar_same inc;

    fun term Ts lev =
      if null Ts andalso inc = 0 then Same.same
      else
        let
          val n = length Ts;
          fun incr lev (FV ((x, i), T)) =
                if i >= 0 then combound (FV ((x, i + inc), FUNs (Ts, Same.commit typ T)), lev, n)
                else raise Same.SAME
            | incr _ (BV _) = raise Same.SAME
            | incr _ (CONST0 _) = raise Same.SAME
            | incr _ (CONST1 (c, T)) = CONST1 (c, typ T)
            | incr _ (CONSTN (c, Ts)) = CONSTN (c, Same.map typ Ts)
            | incr lev (ABS (x, T, t)) =
                (ABS (x, typ T, Same.commit (incr (lev + 1)) t)
                  handle Same.SAME => ABS (x, T, incr (lev + 1) t))
            | incr lev (APP (t, u)) =
                (APP (incr lev t, Same.commit (incr lev) u)
                  handle Same.SAME => APP (t, incr lev u))
            | incr _ (OFCLASS (T, c)) = OFCLASS (typ T, c);
        in incr lev end;

    fun proof Ts lev (Abst (a, T, p)) =
          (Abst (a, typ T, Same.commit (proof Ts (lev + 1)) p)
            handle Same.SAME => Abst (a, T, proof Ts (lev + 1) p))
      | proof Ts lev (Absp (a, t, p)) =
          (Absp (a, term Ts lev t, Same.commit (proof Ts lev) p)
            handle Same.SAME => Absp (a, t, proof Ts lev p))
      | proof Ts lev (Appt (p, t)) =
          (Appt (proof Ts lev p, Same.commit (term Ts lev) t)
            handle Same.SAME => Appt (p, term Ts lev t))
      | proof Ts lev (Appp (p, q)) =
          (Appp (proof Ts lev p, Same.commit (proof Ts lev) q)
            handle Same.SAME => Appp (p, proof Ts lev q))
      | proof Ts lev (Constp (a, insts)) =
          Constp (a, Pure_Logic.map_insts_same typ (term Ts lev) insts)
      | proof _ _ (OFCLASSp (T, c)) = OFCLASSp (typ T, c)
      | proof _ _ _ = raise Same.SAME;

    val k = length prems;

    fun mk_app b (i, j, p) =
      if b then (i - 1, j, Appp (p, BVp i)) else (i, j - 1, Appt (p, BV j));

    fun lift Ts bs i j (Const ("Pure.imp", _) $ A $ B) =
          Absp (Var_Name.H, Same.commit (term Ts 0) (pure_term A), lift Ts (true :: bs) (i + 1) j B)
      | lift Ts bs i j (Const ("Pure.all", _) $ Abs (a, T, t)) =
          let val T' = pure_type T
          in Abst ((a, 0), T', lift (T' :: Ts) (false :: bs) i (j + 1) t) end
      | lift Ts bs i j _ =
          Appps (Same.commit (proof (rev Ts) 0) prf,
            map (fn k => (#3 (fold_rev mk_app bs (i - 1, j - 1, BVp k)))) (i + k - 1 downto i));
  in Absps (map pure_term prems) (lift [] [] 0 0 gprop) end;


(* higher-order resolution *)

fun mk_asm_prf C i m =
  let
    fun imp _ i 0 = BVp i
      | imp (APP (APP (CONST0 "Pure.imp", A), B)) i m = Absp (Var_Name.H, A, imp B (i + 1) (m - 1))
      | imp _ i _ = BVp i;
    fun all (APP (CONST1 ("Pure.all", _), ABS (a, T, t))) = Abst (a, T, all t)
      | all t = imp t (~ i) m
  in all C end;

fun assumption_proof thy envir Bs Bi n visible prf =
  let
    val cache as {pure_term, ...} = pure_term_cache thy;
    val normt = pure_term #> Same.commit (norm_term_same cache envir);
  in
    Absps (map normt Bs)
      (Appps (prf, map BVp (length Bs - 1 downto 0) @ [mk_asm_prf (normt Bi) n ~1]))
    |> norm_proof_cache cache envir visible
  end;

fun flatten_params_proof i j n (APP (APP (CONST0 "Pure.imp", A), B), k) =
      Absp (Var_Name.H, A, flatten_params_proof (i + 1) j n (B, k))
  | flatten_params_proof i j n (APP (CONST1 ("Pure.all", _), ABS (a, T, t)), k) =
      Abst (a, T, flatten_params_proof i (j + 1) n (t, k))
  | flatten_params_proof i j n (_, k) =
      Appps (Appts (BVp (k + i),
        map BV (j - 1 downto 0)), map BVp (remove (op =) (i - n) (i - 1 downto 0)));

fun bicompose_proof thy env smax flatten Bs As A oldAs n m visible rprf sprf =
  let
    val cache as {pure_term, ...} = pure_term_cache thy;
    val normt = pure_term #> Same.commit (norm_term_same cache env);
    val normp = norm_proof_cache cache env visible;

    val lb = length Bs;
    val la = length As;

    fun proof p q =
      Absps (map normt (Bs @ As))
        (Appp (Appps (q, map BVp (lb + la - 1 downto la)),
          Appps (p, (if n > 0 then [mk_asm_prf (normt (the A)) n m] else []) @
            map (if flatten then flatten_params_proof 0 0 n else BVp o snd)
              (map normt oldAs ~~ (la - 1 downto 0)))));
  in
    if Envir.is_empty env then proof rprf sprf
    else proof (normp rprf) (if Envir.above env smax then sprf else normp sprf)
  end;


(* sort constraints within the logic *)

type sorts_proof = (class * class -> proof) * (string * class list list * class -> proof);

fun of_sort_proof algebra (classrel_proof, arity_proof) hyps =
  Sorts.of_sort_derivation algebra
   {class_relation = fn _ => fn _ => fn (prf, c1) => fn c2 =>
      if c1 = c2 then prf else Appp (classrel_proof (c1, c2), prf),
    type_constructor = fn (a, _) => fn dom => fn c =>
      let val Ss = map (map snd) dom and prfs = maps (map fst) dom
      in Appps (arity_proof (a, Ss, c), prfs) end,
    type_variable = fn typ => map (fn c => (hyps (typ, c), c)) (Type.sort_of_atyp typ)};

fun unconstrainT_proof thy sorts_proof (ucontext: Logic.unconstrain_context) =
  let
    val algebra = Sign.classes_of thy;

    val cache = pure_term_cache thy;
    val typ_cache = typ_cache thy;

    val typ =
      Pure_Types.apply_unsynchronized_cache
        (typ_of #> #typ_operation ucontext {strip_sorts = true} #> pure_type_of);

    val typ_sort = #typ_operation ucontext {strip_sorts = false};

    fun hyps T =
      (case AList.lookup (op =) (#constraints ucontext) T of
        SOME t => Hypp (#pure_term cache t)
      | NONE => raise Fail "unconstrainT_proof: missing constraint");

    fun class (T, c) =
      let val T' = Same.commit typ_sort (typ_cache T)
      in the_single (of_sort_proof algebra sorts_proof hyps (T', [c])) end;
  in
    Pure_Logic.map_proof_types {hyps = false} typ #> Pure_Logic.map_class_proof class
    #> Pure_Logic.beta_norm_prooft
    #> fold_rev (implies_intr_proof' o #pure_term cache o #2) (#constraints ucontext)
  end;


(* standardization of variables for export: only frees and named bounds *)

local

fun declare_frees_term t = Pure_Term.fold_vars (fn ((x, ~1), _) => Name.declare x | _ => I) t;
val declare_frees_proof = Pure_Logic.fold_proof {hyps = true} (K I) declare_frees_term;

val (variant_abs_term, variant_abs_proof) =
  let
    fun term bs (ABS ((x, i), T, t)) =
          let
            val x' = #1 (Name.variant x (declare_frees_term t bs));
            val bs' = Name.declare x' bs;
          in ABS ((x', i), T, Same.commit_if (x <> x') (term bs') t) end
      | term bs (APP (t, u)) =
          (APP (term bs t, Same.commit (term bs) u)
            handle Same.SAME => APP (t, term bs u))
      | term _ _ = raise Same.SAME;

    fun proof bs (Abst ((x, i), T, p)) =
          let
            val x' = #1 (Name.variant x (declare_frees_proof p bs));
            val bs' = Name.declare x' bs;
          in Abst ((x', i), T, Same.commit_if (x <> x') (proof bs') p) end
      | proof bs (Absp ((x, i), t, p)) =
          let
            val x' = #1 (Name.variant x (declare_frees_term t (declare_frees_proof p bs)));
            val (t', term_eq) = Same.commit_id (term bs) t;
            val bs' = Name.declare x' bs;
          in Absp ((x', i), t', Same.commit_if (x <> x' orelse not term_eq) (proof bs') p) end
      | proof bs (Appt (p, t)) =
          (Appt (proof bs p, Same.commit (term bs) t)
            handle Same.SAME => Appt (p, term bs t))
      | proof bs (Appp (p, q)) =
          (Appp (proof bs p, Same.commit (proof bs) q)
            handle Same.SAME => Appp (p, proof bs q))
      | proof bs (Hypp t) = Hypp (term bs t)
      | proof _ _ = raise Same.SAME;
  in (term Name.context, proof Name.context) end;

val used_frees_type = Pure_Term.fold_tvars (fn ((a, ~1), _) => Name.declare a | _ => I);
fun used_frees_term t = Pure_Term.fold_types used_frees_type t #> declare_frees_term t;
val used_frees_proof = Pure_Logic.fold_proof {hyps = true} used_frees_type used_frees_term;

fun hidden_types prop proof =
  let
    val visible = (Pure_Term.fold_types o Pure_Term.fold_tvars) (insert (op =)) prop [];
    val add_hiddenT = Pure_Term.fold_tvars (fn v => not (member (op =) visible v) ? insert (op =) v);
  in
    rev (Pure_Logic.fold_proof {hyps = true} add_hiddenT (Pure_Term.fold_types add_hiddenT) proof [])
  end;

fun standard_hidden_types prop proof =
  let
    val hidden = hidden_types prop proof;
    val idx = maxidx_term prop (maxidx_proof proof ~1) + 1;
    fun zvar (v as (_, S)) =
      if not (member (op =) hidden v) then raise Same.SAME
      else if null S then Pure_Term.dummyT
      else TV (("'", idx), S);
    val typ = Pure_Term.map_tvars_same zvar;
  in
    proof |> not (null hidden) ? Pure_Logic.map_proof {hyps = true} typ (Pure_Term.map_types typ)
  end;

fun standard_hidden_terms prop proof =
  let
    fun add_unless excluded (FV v) = not (member (op =) excluded v) ? insert (op =) v
      | add_unless _ _ = I;
    val visible = Pure_Term.fold_aterms (add_unless []) prop [];
    val hidden =
      Pure_Logic.fold_proof {hyps = true} (K I)
        (Pure_Term.fold_aterms (add_unless visible)) proof [];
    fun var (v as (_, T)) =
      if member (op =) hidden v then pure_term_dummy_pattern T else raise Same.SAME;
    val term = Pure_Term.map_vars_same var;
  in proof |> not (null hidden) ? Pure_Logic.map_proof {hyps = true} Same.same term end;

fun standard_inst add mk (v as ((x, i), T)) (inst, used) =
  let
    val (x', used') = Name.variant_bound x used;
    val inst' = if x = x' andalso i = ~1 then inst else add (v, mk ((x', ~1), T)) inst;
  in (inst', used') end;

fun standard_inst_type used prf =
  let
    val add_tvars = Pure_Term.fold_tvars (fn v => Pure_TVars.add (v, ()));
    val (instT, _) =
      (Pure_TVars.empty, used) |> Pure_TVars.fold (standard_inst Pure_TVars.add TV o #1)
        (TVars.build
          (prf |> Pure_Logic.fold_proof {hyps = true} add_tvars (Pure_Term.fold_types add_tvars)));
  in Pure_Logic.instantiate_type_same instT end;

fun standard_inst_term used inst_type prf =
  let
    val add_vars = Pure_Term.fold_vars (fn (x, T) => Pure_Vars.add ((x, Same.commit inst_type T), ()));
    val (inst, _) =
      (Pure_Vars.empty, used) |> Pure_Vars.fold (standard_inst Pure_Vars.add FV o #1)
        (Pure_Vars.build (prf |> Pure_Logic.fold_proof {hyps = true} (K I) add_vars));
  in Pure_Logic.instantiate_term_same inst_type inst end;

val typargs_type = Pure_Term.fold_tvars (fn ((a, ~1), S) => TFrees.add_set (a, S) | _ => I);
val typargs_term = Pure_Term.fold_types typargs_type;
val typargs_proof = Pure_Logic.fold_proof {hyps = true} typargs_type typargs_term;

val add_standard_vars_term = Pure_Term.fold_aterms
  (fn FV ((x, ~1), T) =>
      (fn env =>
        (case AList.lookup (op =) env x of
          NONE => (x, T) :: env
        | SOME T' =>
            if T = T' then env
            else
              raise TYPE ("standard_vars_env: type conflict for variable " ^ quote x,
                [typ_of T, typ_of T'], [])))
    | _ => I);

val add_standard_vars = Pure_Logic.fold_proof {hyps = true} (K I) add_standard_vars_term;

in

fun standard_vars used (prop, opt_prf) =
  let
    val prf = the_default Nop opt_prf
      |> standard_hidden_types prop
      |> standard_hidden_terms prop;
    val prop_prf = Appp (Hypp prop, prf);

    val used' = used |> used_frees_proof prop_prf;
    val inst_type = standard_inst_type used' prop_prf;
    val inst_term = standard_inst_term used' inst_type prop_prf;
    val inst_proof = Pure_Logic.map_proof_same {hyps = true} inst_type inst_term;

    val prop' = prop |> Same.commit (Same.compose variant_abs_term inst_term);
    val opt_proof' =
      if is_none opt_prf then NONE
      else SOME (prf |> Same.commit (Same.compose variant_abs_proof inst_proof));
    val proofs' = the_list opt_proof';

    val args = build_rev (add_standard_vars_term prop' #> fold add_standard_vars proofs');
    val typargs = TFrees.list_set (TFrees.build (typargs_term prop' #> fold typargs_proof proofs'));
  in {typargs = typargs, args = args, prop = prop', proof = opt_proof'} end;

end;

end;

structure Basic_Pure_Logic: BASIC_PURE_LOGIC = Pure_Logic;
