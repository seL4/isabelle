(*  Title:      Pure/pure_logic.ML
    Author:     Makarius

The pure logic behind Isabelle/Pure: types, terms, and proofs.
*)

signature BASIC_PURE_LOGIC =
sig
  type thm_name = string * int
  datatype proof_name =
      Axiom of string
    | Oracle of string
    | Thm of {theory_name: string, thm_name: thm_name * Position.T, serial: serial}
  type proof_const =
    (proof_name * Pure_Term.t) * (Pure_Term.T Pure_TVars.table * Pure_Term.t Pure_Vars.table);
  datatype proof =
      Nop
    | Constp of proof_const
    | BVp of int
    | Abst of Var_Name.T * Pure_Term.T * proof
    | Absp of thm_name * Pure_Term.t * proof
    | Appt of proof * Pure_Term.t
    | Appp of proof * proof
    | Hypp of Pure_Term.t
    | OFCLASSp of Pure_Term.T * Pure_Term.class
  val Absts: (Var_Name.T * Pure_Term.T) list -> proof -> proof
  val Absps: Pure_Term.t list -> proof -> proof
  val Appts: proof * Pure_Term.t list -> proof
  val Appps: proof * proof list -> proof
  exception PURE_LOGIC of string * Pure_Term.T list * Pure_Term.t list * proof list
end;

signature PURE_LOGIC =
sig
  include BASIC_PURE_LOGIC
  val incr_bv_same: int -> int -> Pure_Term.t Same.operation
  val incr_proof_bv_same: int -> int -> int -> int -> proof Same.operation
  val incr_bv: int -> int -> Pure_Term.t -> Pure_Term.t
  val incr_boundvars: int -> Pure_Term.t -> Pure_Term.t
  val incr_proof_bv: int -> int -> int -> int -> proof -> proof
  val incr_proof_boundvars: int -> int -> proof -> proof
  val subst_term_bound_same: Pure_Term.t -> int -> Pure_Term.t Same.operation
  val subst_proof_bound_same: Pure_Term.t -> int -> proof Same.operation
  val subst_proof_boundp_same: proof -> int -> int -> proof Same.operation
  val subst_term_bound: Pure_Term.t -> Pure_Term.t -> Pure_Term.t
  val subst_proof_bound: Pure_Term.t -> proof -> proof
  val subst_proof_boundp: proof -> proof -> proof
  val subst_type_same: (Var_Name.T * Pure_Term.sort, Pure_Term.T) Same.function ->
    Pure_Term.T Same.operation
  val subst_term_same:
    Pure_Term.T Same.operation -> (Var_Name.T * Pure_Term.T, Pure_Term.t) Same.function ->
      Pure_Term.t Same.operation
  val instantiate_type_same: Pure_Term.T Pure_TVars.table -> Pure_Term.T Same.operation
  val instantiate_term_same: Pure_Term.T Same.operation -> Pure_Term.t Pure_Vars.table ->
    Pure_Term.t Same.operation
  exception BAD_INST of ((Var_Name.T * Pure_Term.T) * Pure_Term.t) list
  val map_insts_same: Pure_Term.T Same.operation -> Pure_Term.t Same.operation ->
    Pure_Term.T Pure_TVars.table * Pure_Term.t Pure_Vars.table ->
    Pure_Term.T Pure_TVars.table * Pure_Term.t Pure_Vars.table
  val fold_proof: {hyps: bool} -> (Pure_Term.T -> 'a -> 'a) -> (Pure_Term.t -> 'a -> 'a) ->
    proof -> 'a -> 'a
  val fold_proof_types: {hyps: bool} -> (Pure_Term.T -> 'a -> 'a) -> proof -> 'a -> 'a
  val map_proof_same: {hyps: bool} -> Pure_Term.T Same.operation ->
    Pure_Term.t Same.operation -> proof Same.operation
  val map_proof: {hyps: bool} -> Pure_Term.T Same.operation -> Pure_Term.t Same.operation ->
    proof -> proof
  val map_proof_types: {hyps: bool} -> Pure_Term.T Same.operation -> proof -> proof
  val map_class_proof: (Pure_Term.T * Pure_Term.class, proof) Same.function -> proof -> proof
  val beta_norm_term_same: Pure_Term.t Same.operation
  val beta_norm_prooft_same: proof Same.operation
  val beta_norm_proof_same: proof Same.operation
  val beta_norm_term: Pure_Term.t -> Pure_Term.t
  val beta_norm_prooft: proof -> proof
  val beta_norm_proof: proof -> proof
  val proof_const: proof_name * Pure_Term.t -> proof_const
  val proof_const_typargs: proof_const -> ((Var_Name.T * Pure_Term.sort) * Pure_Term.T) list
  val proof_const_args: proof_const -> ((Var_Name.T * Pure_Term.T) * Pure_Term.t) list
  val make_const_proof: (string -> Pure_Term.T) * (string -> Pure_Term.t) -> proof_const -> proof
end;

structure Pure_Logic: PURE_LOGIC =
struct

open Basic_Pure_Term;


(* datatypes *)

type thm_name = string * int;

datatype proof_name =
    Axiom of string
  | Oracle of string
  | Thm of {theory_name: string, thm_name: thm_name * Position.T, serial: serial};

type proof_const = (proof_name * t) * (T Pure_TVars.table * t Pure_Vars.table);

datatype proof =
    Nop
  | Constp of proof_const
  | BVp of int
  | Abst of Var_Name.T * T * proof
  | Absp of thm_name * t * proof
  | Appt of proof * t
  | Appp of proof * proof
  | Hypp of Pure_Term.t
  | OFCLASSp of Pure_Term.T * class;      (*OFCLASS proof from sorts algebra*)

val Absts = fold_rev (fn (x, T) => fn prf => Abst (x, T, prf));
val Absps = fold_rev (fn t => fn prf => Absp (Var_Name.H, t, prf));

val Appts = Library.foldl Appt;
val Appps = Library.foldl Appp;

exception PURE_LOGIC of string * Pure_Term.T list * Pure_Term.t list * proof list;


(* increment bound variables *)

fun incr_bv_same inc =
  if inc = 0 then fn _ => Same.same
  else
    let
      fun term lev (BV i) = if i >= lev then BV (i + inc) else raise Same.SAME
        | term lev (ABS (a, T, t)) = ABS (a, T, term (lev + 1) t)
        | term lev (APP (t, u)) =
            (APP (term lev t, Same.commit (term lev) u)
              handle Same.SAME => APP (t, term lev u))
        | term _ _ = raise Same.SAME;
    in term end;

fun incr_proof_bv_same incp inct =
  if incp = 0 andalso inct = 0 then fn _ => fn _ => Same.same
  else
    let
      val term = incr_bv_same inct;

      fun proof plev _ (BVp i) = if i >= plev then BVp (i + incp) else raise Same.SAME
        | proof plev tlev (Absp (a, t, p)) =
            (Absp (a, term tlev t, Same.commit (proof (plev + 1) tlev) p)
              handle Same.SAME => Absp (a, t, proof (plev + 1) tlev p))
        | proof plev tlev (Abst (a, T, p)) = Abst (a, T, proof plev (tlev + 1) p)
        | proof plev tlev (Appp (p, q)) =
            (Appp (proof plev tlev p, Same.commit (proof plev tlev) q)
              handle Same.SAME => Appp (p, proof plev tlev q))
        | proof plev tlev (Appt (p, t)) =
            (Appt (proof plev tlev p, Same.commit (term tlev) t)
              handle Same.SAME => Appt (p, term tlev t))
        | proof _ _ _ = raise Same.SAME;
    in proof end;

fun incr_bv inc lev = Same.commit (incr_bv_same inc lev);
fun incr_boundvars inc = incr_bv inc 0;

fun incr_proof_bv incp inct plev tlev = Same.commit (incr_proof_bv_same incp inct plev tlev);
fun incr_proof_boundvars incp inct = incr_proof_bv incp inct 0 0;


(* substitution of bound variables *)

fun subst_term_bound_same arg =
  let
    fun term lev (BV i) =
          if i < lev then raise Same.SAME   (*var is locally bound*)
          else if i = lev then incr_boundvars lev arg
          else BV (i - 1)   (*loose: change it*)
      | term lev (ABS (a, T, t)) = ABS (a, T, term (lev + 1) t)
      | term lev (APP (t, u)) =
          (APP (term lev t, Same.commit (term lev) u)
            handle Same.SAME => APP (t, term lev u))
      | term _ _ = raise Same.SAME;
  in term end;

fun subst_proof_bound_same arg =
  let
    val term = subst_term_bound_same arg;

    fun proof lev (Absp (a, t, p)) =
          (Absp (a, term lev t, Same.commit (proof lev) p)
            handle Same.SAME => Absp (a, t, proof lev p))
      | proof lev (Abst (a, T, p)) = Abst (a, T, proof (lev + 1) p)
      | proof lev (Appp (p, q)) =
          (Appp (proof lev p, Same.commit (proof lev) q)
            handle Same.SAME => Appp (p, proof lev q))
      | proof lev (Appt (p, t)) =
          (Appt (proof lev p, Same.commit (term lev) t)
            handle Same.SAME => Appt (p, term lev t))
      | proof _ _ = raise Same.SAME;
  in proof end;

fun subst_proof_boundp_same arg =
  let
    fun proof plev tlev (BVp i) =
          if i < plev then raise Same.SAME   (*var is locally bound*)
          else if i = plev then incr_proof_boundvars plev tlev arg
          else BVp (i - 1)   (*loose: change it*)
      | proof plev tlev (Absp (a, t, p)) = Absp (a, t, proof (plev + 1) tlev p)
      | proof plev tlev (Abst (a, T, p)) = Abst (a, T, proof plev (tlev + 1) p)
      | proof plev tlev (Appp (p, q)) =
          (Appp (proof plev tlev p, Same.commit (proof plev tlev) q)
            handle Same.SAME => Appp (p, proof plev tlev q))
      | proof plev tlev (Appt (p, t)) = Appt (proof plev tlev p, t)
      | proof _ _ _ = raise Same.SAME;
  in proof end;

fun subst_term_bound arg body = Same.commit (subst_term_bound_same arg 0) body;
fun subst_proof_bound arg body = Same.commit (subst_proof_bound_same arg 0) body;
fun subst_proof_boundp arg body = Same.commit (subst_proof_boundp_same arg 0 0) body;


(* substitution of free or schematic variables *)

fun subst_type_same tvar =
  let
    fun typ (TV x) = tvar x
      | typ (FUN (T, U)) =
          (FUN (typ T, Same.commit typ U)
            handle Same.SAME => FUN (T, typ U))
      | typ PROP = raise Same.SAME
      | typ (CON0 _) = raise Same.SAME
      | typ (CON1 (a, T)) = CON1 (a, typ T)
      | typ (CONN (a, Ts)) = CONN (a, Same.map typ Ts);
  in typ end;

fun subst_term_same typ var =
  let
    fun term (FV (x, T)) =
          let val (T', same) = Same.commit_id typ T in
            (case Same.catch var (x, T') of
              NONE => if same then raise Same.SAME else FV (x, T')
            | SOME t' => t')
          end
      | term (BV _) = raise Same.SAME
      | term (CONST0 _) = raise Same.SAME
      | term (CONST1 (a, T)) = CONST1 (a, typ T)
      | term (CONSTN (a, Ts)) = CONSTN (a, Same.map typ Ts)
      | term (ABS (a, T, t)) =
          (ABS (a, typ T, Same.commit term t)
            handle Same.SAME => ABS (a, T, term t))
      | term (APP (t, u)) =
          (APP (term t, Same.commit term u)
            handle Same.SAME => APP (t, term u))
      | term (OFCLASS (T, c)) = OFCLASS (typ T, c);
  in term end;

fun instantiate_type_same instT =
  if Pure_TVars.is_empty instT then Same.same
  else
    Pure_Types.apply_unsynchronized_cache
      (subst_type_same (Same.function (Pure_TVars.lookup instT)));

fun instantiate_term_same typ inst =
  subst_term_same typ (Same.function (Pure_Vars.lookup inst));


(* fold types/terms within proof *)

fun fold_proof {hyps} typ term =
  let
    fun proof Nop acc = acc
      | proof (Constp (_, (instT, inst))) acc =
          acc |> Pure_TVars.fold (typ o #2) instT |> Pure_Vars.fold (term o #2) inst
      | proof (BVp _) acc = acc
      | proof (Abst (_, T, p)) acc = acc |> typ T |> proof p
      | proof (Absp (_, t, p)) acc = acc |> term t |> proof p
      | proof (Appt (p, t)) acc = acc |> proof p |> term t
      | proof (Appp (p, q)) acc = acc |> proof p |> proof q
      | proof (Hypp h) acc = acc |> hyps ? term h
      | proof (OFCLASSp (T, _)) acc = acc |> hyps ? typ T;
  in proof end;

fun fold_proof_types hyps typ =
  fold_proof hyps typ (Pure_Term.fold_types typ);


(* map types/terms within proof *)

exception BAD_INST of ((Var_Name.T * T) * t) list;

fun make_inst inst =
  Pure_Vars.build (inst |> fold (Pure_Vars.insert Pure_Term.alpha_eq))
    handle Pure_Vars.DUP _ => raise BAD_INST inst;

fun map_insts_same typ term (instT, inst) =
  let
    val changed = Unsynchronized.ref false;
    fun apply f x =
      (case Same.catch f x of
        NONE => NONE
      | some => (changed := true; some));

    val instT' =
      (instT, instT) |-> Pure_TVars.fold (fn (v, T) =>
        (case apply typ T of
          NONE => I
        | SOME T' => Pure_TVars.update (v, T')));

    val vars' =
      (inst, Pure_Vars.empty) |-> Pure_Vars.fold (fn ((v, T), _) =>
        (case apply typ T of
          NONE => I
        | SOME T' => Pure_Vars.add ((v, T), (v, T'))));

    val inst' =
      if Pure_Vars.is_empty vars' then
        (inst, inst) |-> Pure_Vars.fold (fn (v, t) =>
          (case apply term t of
            NONE => I
          | SOME t' => Pure_Vars.update (v, t')))
      else
        build (inst |> Pure_Vars.fold_rev (fn (v, t) =>
          cons (the_default v (Pure_Vars.lookup vars' v), the_default t (apply term t))))
        |> make_inst;
  in if ! changed then (instT', inst') else raise Same.SAME end;

fun map_proof_same {hyps} typ term =
  let
    fun proof Nop = raise Same.SAME
      | proof (Constp (a, (instT, inst))) =
          Constp (a, map_insts_same typ term (instT, inst))
      | proof (BVp _) = raise Same.SAME
      | proof (Abst (a, T, p)) =
          (Abst (a, typ T, Same.commit proof p)
            handle Same.SAME => Abst (a, T, proof p))
      | proof (Absp (a, t, p)) =
          (Absp (a, term t, Same.commit proof p)
            handle Same.SAME => Absp (a, t, proof p))
      | proof (Appt (p, t)) =
          (Appt (proof p, Same.commit term t)
            handle Same.SAME => Appt (p, term t))
      | proof (Appp (p, q)) =
          (Appp (proof p, Same.commit proof q)
            handle Same.SAME => Appp (p, proof q))
      | proof (Hypp h) = if hyps then Hypp (term h) else raise Same.SAME
      | proof (OFCLASSp (T, c)) = if hyps then OFCLASSp (typ T, c) else raise Same.SAME;
  in proof end;

fun map_proof hyps typ term = Same.commit (map_proof_same hyps typ term);
fun map_proof_types hyps typ = map_proof hyps typ (subst_term_same typ Same.same);


(* map class proofs *)

fun map_class_proof class =
  let
    fun proof (OFCLASSp C) = class C
      | proof (Abst (a, T, p)) = Abst (a, T, proof p)
      | proof (Absp (a, t, p)) = Absp (a, t, proof p)
      | proof (Appt (p, t)) = Appt (proof p, t)
      | proof (Appp (p, q)) =
          (Appp (proof p, Same.commit proof q)
            handle Same.SAME => Appp (p, proof q))
      | proof _ = raise Same.SAME;
  in Same.commit proof end;


(* beta contraction *)

val beta_norm_term_same =
  let
    fun norm (ABS (a, T, t)) = ABS (a, T, Same.commit norm t)
      | norm (APP (ABS (_, _, body), t)) = Same.commit norm (subst_term_bound t body)
      | norm (APP (f, t)) =
          ((case norm f of
             ABS (_, _, body) => Same.commit norm (subst_term_bound t body)
           | nf => APP (nf, Same.commit norm t))
          handle Same.SAME => APP (f, norm t))
      | norm _ = raise Same.SAME;
  in norm end;

val beta_norm_prooft_same =
  let
    val term = beta_norm_term_same;

    fun norm (Abst (a, T, p)) = Abst (a, T, norm p)
      | norm (Appt (Abst (_, _, body), t)) = Same.commit norm (subst_proof_bound t body)
      | norm (Appt (f, t)) =
          ((case norm f of
             Abst (_, _, body) => Same.commit norm (subst_proof_bound t body)
           | nf => Appt (nf, Same.commit term t))
          handle Same.SAME => Appt (f, term t))
      | norm _ = raise Same.SAME;
  in norm end;

val beta_norm_proof_same =
  let
    val term = beta_norm_term_same;

    fun norm (Abst (a, T, p)) = Abst (a, T, norm p)
      | norm (Absp (a, t, p)) =
          (Absp (a, term t, Same.commit norm p)
            handle Same.SAME => Absp (a, t, norm p))
      | norm (Appt (Abst (_, _, body), t)) = Same.commit norm (subst_proof_bound t body)
      | norm (Appp (Absp (_, _, body), p)) = Same.commit norm (subst_proof_boundp p body)
      | norm (Appt (f, t)) =
          ((case norm f of
             Abst (_, _, body) => Same.commit norm (subst_proof_bound t body)
           | nf => Appt (nf, Same.commit term t))
          handle Same.SAME => Appt (f, term t))
      | norm (Appp (f, p)) =
          ((case norm f of
             Absp (_, _, body) => Same.commit norm (subst_proof_boundp p body)
           | nf => Appp (nf, Same.commit norm p))
          handle Same.SAME => Appp (f, norm p))
      | norm _ = raise Same.SAME;
  in norm end;

val beta_norm_term = Same.commit beta_norm_term_same;
val beta_norm_proof = Same.commit beta_norm_proof_same;
val beta_norm_prooft = Same.commit beta_norm_prooft_same;


(* proof constants *)

fun proof_const (a, A) : proof_const =
  let
    val instT =
      Pure_TVars.build (A |> (Pure_Term.fold_types o Pure_Term.fold_tvars) (fn v => fn tab =>
        if Pure_TVars.defined tab v then tab else Pure_TVars.update (v, TV v) tab));
    val inst =
      Pure_Vars.build (A |> Pure_Term.fold_vars (fn v => fn tab =>
        if Pure_Vars.defined tab v then tab else Pure_Vars.update (v, FV v) tab));
  in ((a, A), (instT, inst)) end;

fun proof_const_typargs (((_, A), (instT, _)): proof_const) =
  Pure_TVars.build (A |> Pure_TVars.add_tvars) |> Pure_TVars.list_set
  |> map (fn v => (v, the_default (TV v) (Pure_TVars.lookup instT v)));

fun proof_const_args (((_, A), (_, inst)): proof_const) =
  Pure_Vars.build (A |> Pure_Vars.add_vars) |> Pure_Vars.list_set
  |> map (fn v => (v, the_default (FV v) (Pure_Vars.lookup inst v)));

fun make_const_proof (f, g) ((a, insts): proof_const) =
  let
    val typ = subst_type_same (Same.function (fn ((x, _), _) => try f x));
    val term = Same.function (fn FV ((x, _), _) => try g x | _ => NONE);
  in Constp (a, Same.commit (map_insts_same typ term) insts) end;

end;

structure Basic_Pure_Logic: BASIC_PURE_LOGIC = Pure_Logic;
