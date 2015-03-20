(*  Title:      Pure/Tools/rule_insts.ML
    Author:     Makarius

Rule instantiations -- operations within implicit rule / subgoal context.
*)

signature RULE_INSTS =
sig
  val where_rule: Proof.context ->
    ((indexname * Position.T) * string) list ->
    (binding * string option * mixfix) list -> thm -> thm
  val of_rule: Proof.context -> string option list * string option list ->
    (binding * string option * mixfix) list -> thm -> thm
  val read_instantiate: Proof.context ->
    ((indexname * Position.T) * string) list -> string list -> thm -> thm
  val res_inst_tac: Proof.context ->
    ((indexname * Position.T) * string) list -> thm -> int -> tactic
  val eres_inst_tac: Proof.context ->
    ((indexname * Position.T) * string) list -> thm -> int -> tactic
  val cut_inst_tac: Proof.context ->
    ((indexname * Position.T) * string) list -> thm -> int -> tactic
  val forw_inst_tac: Proof.context ->
    ((indexname * Position.T) * string) list -> thm -> int -> tactic
  val dres_inst_tac: Proof.context ->
    ((indexname * Position.T) * string) list -> thm -> int -> tactic
  val thin_tac: Proof.context -> string -> int -> tactic
  val subgoal_tac: Proof.context -> string -> int -> tactic
  val make_elim_preserve: Proof.context -> thm -> thm
  val method:
    (Proof.context -> ((indexname * Position.T) * string) list -> thm -> int -> tactic) ->
    (Proof.context -> thm list -> int -> tactic) -> (Proof.context -> Proof.method) context_parser
end;

structure Rule_Insts: RULE_INSTS =
struct

(** reading instantiations **)

fun partition_insts mixed_insts =
  List.partition (fn (((x, _), _), _) => String.isPrefix "'" x) mixed_insts;

fun error_var msg (xi, pos) =
  error (msg ^ quote (Term.string_of_vname xi) ^ Position.here pos);

fun the_sort tvars (xi, pos) : sort =
  (case AList.lookup (op =) tvars xi of
    SOME S => S
  | NONE => error_var "No such type variable in theorem: " (xi, pos));

fun the_type vars (xi, pos) : typ =
  (case AList.lookup (op =) vars xi of
    SOME T => T
  | NONE => error_var "No such variable in theorem: " (xi, pos));

local

fun instantiate inst =
  Term_Subst.instantiate ([], map (fn (xi, t) => ((xi, Term.fastype_of t), t)) inst) #>
  Envir.beta_norm;

fun make_instT f v =
  let
    val T = TVar v;
    val T' = f T;
  in if T = T' then NONE else SOME (v, T') end;

fun make_inst f v =
  let
    val t = Var v;
    val t' = f t;
  in if t aconv t' then NONE else SOME (v, t') end;

in

fun readT ctxt tvars ((xi, pos), s) =
  let
    val S = the_sort tvars (xi, pos);
    val T = Syntax.read_typ ctxt s;
  in
    if Sign.of_sort (Proof_Context.theory_of ctxt) (T, S) then ((xi, S), T)
    else error_var "Bad sort for instantiation of type variable: " (xi, pos)
  end;

fun read_termTs ctxt ss Ts =
  let
    fun parse T = if T = propT then Syntax.parse_prop ctxt else Syntax.parse_term ctxt;
    val ts = map2 parse Ts ss;
    val ts' =
      map2 (Type.constraint o Type_Infer.paramify_vars) Ts ts
      |> Syntax.check_terms ctxt
      |> Variable.polymorphic ctxt;
    val Ts' = map Term.fastype_of ts';
    val tyenv = fold Type.raw_match (Ts ~~ Ts') Vartab.empty;
    val tyenv' = Vartab.fold (fn (xi, (S, T)) => cons ((xi, S), T)) tyenv [];
  in (ts', tyenv') end;

fun read_insts ctxt mixed_insts thm =
  let
    val (type_insts, term_insts) = partition_insts mixed_insts;

    val tvars = Thm.fold_terms Term.add_tvars thm [];
    val vars = Thm.fold_terms Term.add_vars thm [];


    (* type instantiations *)

    val instT1 = Term_Subst.instantiateT (map (readT ctxt tvars) type_insts);
    val vars1 = map (apsnd instT1) vars;


    (* term instantiations *)

    val (xs, ss) = split_list term_insts;
    val Ts = map (the_type vars1) xs;
    val (ts, inferred) = read_termTs ctxt ss Ts;

    val instT2 = Term_Subst.instantiateT inferred;
    val vars2 = map (apsnd instT2) vars1;
    val inst2 = instantiate (map #1 xs ~~ ts);


    (* result *)

    val inst_tvars = map_filter (make_instT (instT2 o instT1)) tvars;
    val inst_vars = map_filter (make_inst inst2) vars2;
  in (inst_tvars, inst_vars) end;

fun where_rule ctxt mixed_insts fixes thm =
  let
    val ctxt' = ctxt
      |> Proof_Context.read_vars fixes |-> Proof_Context.add_fixes |> #2
      |> Variable.declare_thm thm;
    val (inst_tvars, inst_vars) = read_insts ctxt' mixed_insts thm;
  in
    thm
    |> Drule.instantiate_normalize
      (map (apply2 (Thm.ctyp_of ctxt) o apfst TVar) inst_tvars,
       map (apply2 (Thm.cterm_of ctxt) o apfst Var) inst_vars)
    |> singleton (Proof_Context.export ctxt' ctxt)
    |> Rule_Cases.save thm
  end;

fun of_rule ctxt (args, concl_args) fixes thm =
  let
    fun zip_vars _ [] = []
      | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
      | zip_vars ((x, _) :: xs) (SOME t :: rest) = ((x, Position.none), t) :: zip_vars xs rest
      | zip_vars [] _ = error "More instantiations than variables in theorem";
    val insts =
      zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) [])) args @
      zip_vars (rev (Term.add_vars (Thm.concl_of thm) [])) concl_args;
  in where_rule ctxt insts fixes thm end;

end;

fun read_instantiate ctxt insts xs =
  where_rule ctxt insts (map (fn x => (Binding.name x, NONE, NoSyn)) xs);



(** attributes **)

(* where: named instantiation *)

val _ = Theory.setup
  (Attrib.setup @{binding "where"}
    (Scan.lift
      (Parse.and_list (Parse.position Args.var -- (Args.$$$ "=" |-- Args.name_inner_syntax))
        -- Parse.for_fixes) >> (fn (insts, fixes) =>
          Thm.rule_attribute (fn context => where_rule (Context.proof_of context) insts fixes)))
    "named instantiation of theorem");


(* of: positional instantiation (terms only) *)

local

val inst = Args.maybe Args.name_inner_syntax;
val concl = Args.$$$ "concl" -- Args.colon;

val insts =
  Scan.repeat (Scan.unless concl inst) --
  Scan.optional (concl |-- Scan.repeat inst) [];

in

val _ = Theory.setup
  (Attrib.setup @{binding "of"}
    (Scan.lift (insts -- Parse.for_fixes) >> (fn (args, fixes) =>
      Thm.rule_attribute (fn context => of_rule (Context.proof_of context) args fixes)))
    "positional instantiation of theorem");

end;



(** tactics **)

(* resolution after lifting and instantiation; may refer to parameters of the subgoal *)

fun bires_inst_tac bires_flag ctxt mixed_insts thm i st = CSUBGOAL (fn (cgoal, _) =>
  let
    val (Tinsts, tinsts) = partition_insts mixed_insts;


    (* goal context *)

    val goal = Thm.term_of cgoal;
    val params =
      Logic.strip_params goal
      (*as they are printed: bound variables with the same name are renamed*)
      |> Term.rename_wrt_term goal
      |> rev;
    val (param_names, ctxt') = ctxt
      |> Variable.declare_thm thm
      |> Thm.fold_terms Variable.declare_constraints st
      |> Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) params);


    (* preprocess rule *)

    val tvars = Thm.fold_terms Term.add_tvars thm [];
    val vars = Thm.fold_terms Term.add_vars thm [];

    val Tinsts_env = map (readT ctxt' tvars) Tinsts;
    val (xis, ss) = split_list tinsts;
    val Ts = map (Term_Subst.instantiateT Tinsts_env o the_type vars) xis;

    val (ts, envT) =
      read_termTs (Proof_Context.set_mode Proof_Context.mode_schematic ctxt') ss Ts;
    val envT' = map (fn (v, T) => (TVar v, T)) (envT @ Tinsts_env);
    val cenv =
      map (fn ((xi, _), t) => apply2 (Thm.cterm_of ctxt') (Var (xi, fastype_of t), t))
        (distinct
          (fn ((x1, t1), (x2, t2)) => x1 = x2 andalso t1 aconv t2)
          (xis ~~ ts));


    (* lift and instantiate rule *)

    val maxidx = Thm.maxidx_of st;
    val paramTs = map #2 params;
    val inc = maxidx + 1;

    fun lift_var (Var ((a, j), T)) = Var ((a, j + inc), paramTs ---> Logic.incr_tvar inc T)
      | lift_var t = raise TERM ("Variable expected", [t]);
    fun lift_term t =
      fold_rev absfree (param_names ~~ paramTs) (Logic.incr_indexes (paramTs, inc) t);
    fun lift_inst (cv, ct) = (cterm_fun lift_var cv, cterm_fun lift_term ct);
    val lift_tvar = apply2 (Thm.ctyp_of ctxt' o Logic.incr_tvar inc);

    val rule =
      Drule.instantiate_normalize
        (map lift_tvar envT', map lift_inst cenv)
        (Thm.lift_rule cgoal thm);
  in
    compose_tac ctxt' (bires_flag, rule, Thm.nprems_of thm) i
  end) i st;

val res_inst_tac = bires_inst_tac false;
val eres_inst_tac = bires_inst_tac true;


(* forward resolution *)

fun make_elim_preserve ctxt rl =
  let
    val maxidx = Thm.maxidx_of rl;
    fun cvar xi = Thm.cterm_of ctxt (Var (xi, propT));
    val revcut_rl' =
      Drule.instantiate_normalize ([], [(cvar ("V", 0), cvar ("V", maxidx + 1)),
        (cvar ("W", 0), cvar ("W", maxidx + 1))]) Drule.revcut_rl;
  in
    (case Seq.list_of
      (Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = false}
        (false, rl, Thm.nprems_of rl) 1 revcut_rl')
     of
      [th] => th
    | _ => raise THM ("make_elim_preserve", 1, [rl]))
  end;

(*instantiate and cut -- for atomic fact*)
fun cut_inst_tac ctxt insts rule = res_inst_tac ctxt insts (make_elim_preserve ctxt rule);

(*forward tactic applies a rule to an assumption without deleting it*)
fun forw_inst_tac ctxt insts rule = cut_inst_tac ctxt insts rule THEN' assume_tac ctxt;

(*dresolve tactic applies a rule to replace an assumption*)
fun dres_inst_tac ctxt insts rule = eres_inst_tac ctxt insts (make_elim_preserve ctxt rule);


(* derived tactics *)

(*deletion of an assumption*)
fun thin_tac ctxt s =
  eres_inst_tac ctxt [((("V", 0), Position.none), s)] Drule.thin_rl;

(*Introduce the given proposition as lemma and subgoal*)
fun subgoal_tac ctxt A =
  DETERM o res_inst_tac ctxt [((("psi", 0), Position.none), A)] cut_rl;



(* method wrapper *)

fun method inst_tac tac =
  Args.goal_spec --
  Scan.optional (Scan.lift
    (Parse.and_list1 (Parse.position Args.var -- (Args.$$$ "=" |-- Parse.!!! Args.name_inner_syntax))
      --| Args.$$$ "in")) [] --
  Attrib.thms >>
  (fn ((quant, insts), thms) => fn ctxt => METHOD (fn facts =>
    if null insts then quant (Method.insert_tac facts THEN' tac ctxt thms)
    else
      (case thms of
        [thm] => quant (Method.insert_tac facts THEN' inst_tac ctxt insts thm)
      | _ => error "Cannot have instantiations with multiple rules")));


(* setup *)

(*warning: rule_tac etc. refer to dynamic subgoal context!*)

val _ = Theory.setup
 (Method.setup @{binding rule_tac} (method res_inst_tac resolve_tac)
    "apply rule (dynamic instantiation)" #>
  Method.setup @{binding erule_tac} (method eres_inst_tac eresolve_tac)
    "apply rule in elimination manner (dynamic instantiation)" #>
  Method.setup @{binding drule_tac} (method dres_inst_tac dresolve_tac)
    "apply rule in destruct manner (dynamic instantiation)" #>
  Method.setup @{binding frule_tac} (method forw_inst_tac forward_tac)
    "apply rule in forward manner (dynamic instantiation)" #>
  Method.setup @{binding cut_tac} (method cut_inst_tac (K cut_rules_tac))
    "cut rule (dynamic instantiation)" #>
  Method.setup @{binding subgoal_tac}
    (Args.goal_spec -- Scan.lift (Scan.repeat1 Args.name_inner_syntax) >>
      (fn (quant, props) => fn ctxt =>
        SIMPLE_METHOD'' quant (EVERY' (map (subgoal_tac ctxt) props))))
    "insert subgoal (dynamic instantiation)" #>
  Method.setup @{binding thin_tac}
    (Args.goal_spec -- Scan.lift Args.name_inner_syntax >>
      (fn (quant, prop) => fn ctxt => SIMPLE_METHOD'' quant (thin_tac ctxt prop)))
      "remove premise (dynamic instantiation)");

end;
