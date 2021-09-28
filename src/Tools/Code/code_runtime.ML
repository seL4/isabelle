(*  Title:      Tools/Code/code_runtime.ML
    Author:     Florian Haftmann, TU Muenchen

Runtime services building on code generation into implementation language SML.
*)

signature CODE_RUNTIME =
sig
  val target: string
  val value: Proof.context ->
    (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string ->
    string * string -> 'a
  type 'a cookie = (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string
  val dynamic_value: 'a cookie -> Proof.context -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a option
  val dynamic_value_strict: 'a cookie -> Proof.context -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a
  val dynamic_value_exn: 'a cookie -> Proof.context -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a Exn.result
  val dynamic_holds_conv: Proof.context -> conv
  val code_reflect: (string * string list option) list -> string list -> string
    -> Path.binding option -> theory -> theory
  val code_reflect_cmd: (string * string list option) list -> string list -> string
    -> Path.binding option -> theory -> theory
  datatype truth = Holds
  val put_truth: (unit -> truth) -> Proof.context -> Proof.context
  val mount_computation: Proof.context -> (string * typ) list -> typ
    -> (term -> 'ml) -> ((term -> term) -> 'ml option -> 'a) -> Proof.context -> term -> 'a
  val mount_computation_conv: Proof.context -> (string * typ) list -> typ
    -> (term -> 'ml) -> (Proof.context -> 'ml -> conv) -> Proof.context -> conv
  val mount_computation_check: Proof.context -> (string * typ) list
    -> (term -> truth) -> Proof.context -> conv
  val polyml_as_definition: (binding * typ) list -> Path.T list -> theory -> theory
  val trace: bool Config.T
end;

structure Code_Runtime : CODE_RUNTIME =
struct

open Basic_Code_Symbol;

(** ML compiler as evaluation environment **)

(* technical prerequisites *)

val thisN = "Code_Runtime";
val prefix_this = Long_Name.append thisN;
val truthN = prefix_this "truth";
val HoldsN = prefix_this "Holds";

val target = "Eval";

datatype truth = Holds;

val _ = Theory.setup
  (Code_Target.add_derived_target (target, [(Code_ML.target_SML, I)])
  #> Code_Target.set_printings (Type_Constructor (\<^type_name>\<open>prop\<close>,
    [(target, SOME (0, (K o K o K) (Code_Printer.str truthN)))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>Code_Generator.holds\<close>,
    [(target, SOME (Code_Printer.plain_const_syntax HoldsN))]))
  #> Code_Target.add_reserved target thisN
  #> fold (Code_Target.add_reserved target) ["oo", "ooo", "oooo", "upto", "downto", "orf", "andf"]);
       (*avoid further pervasive infix names*)

val trace = Attrib.setup_config_bool \<^binding>\<open>code_runtime_trace\<close> (K false);

fun compile_ML verbose code context =
 (if Config.get_generic context trace then tracing code else ();
  Code_Preproc.timed "compiling ML" Context.proof_of
    (ML_Context.exec (fn () => ML_Compiler0.ML ML_Env.context
    {line = 0, file = "generated code", verbose = verbose,
       debug = false} code)) context);

fun value ctxt (get, put, put_ml) (prelude, value) =
  let
    val code =
      prelude ^ "\nval _ = Context.put_generic_context (SOME (Context.map_proof (" ^
      put_ml ^ " (fn () => " ^ value ^ ")) (Context.the_generic_context ())))";
    val ctxt' = ctxt
      |> put (fn () => error ("Bad compilation for " ^ quote put_ml))
      |> Context.proof_map (compile_ML false code);
    val computator = get ctxt';
  in Code_Preproc.timed_exec "running ML" computator ctxt' end;


(* evaluation into ML language values *)

type 'a cookie = (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string;

fun reject_vars ctxt t =
  ((Sign.no_frees ctxt o Sign.no_vars ctxt o map_types (K dummyT)) t; t);

fun build_compilation_text ctxt some_target program consts =
  Code_Target.compilation_text ctxt (the_default target some_target) program consts false
  #>> (fn ml_modules => space_implode "\n\n" (map snd ml_modules));

fun run_compilation_text cookie ctxt comp vs_t args =
  let
    val (program_code, value_name) = comp vs_t;
    val value_code = space_implode " "
      (value_name :: "()" :: map (enclose "(" ")") args);
  in Exn.interruptible_capture (value ctxt cookie) (program_code, value_code) end;

fun partiality_as_none e = SOME (Exn.release e)
  handle General.Match => NONE
    | General.Bind => NONE
    | General.Fail _ => NONE;

fun dynamic_value_exn cookie ctxt some_target postproc t args =
  let
    val _ = reject_vars ctxt t;
    val _ = if Config.get ctxt trace
      then tracing ("Evaluation of term " ^ quote (Syntax.string_of_term ctxt t))
      else ()
    fun comp program _ vs_ty_t deps =
      run_compilation_text cookie ctxt (build_compilation_text ctxt some_target program deps) vs_ty_t args;
  in Code_Thingol.dynamic_value ctxt (Exn.map_res o postproc) comp t end;

fun dynamic_value_strict cookie ctxt some_target postproc t args =
  Exn.release (dynamic_value_exn cookie ctxt some_target postproc t args);

fun dynamic_value cookie ctxt some_target postproc t args =
  partiality_as_none (dynamic_value_exn cookie ctxt some_target postproc t args);


(* evaluation for truth or nothing *)

structure Truth_Result = Proof_Data
(
  type T = unit -> truth;
  val empty: T = fn () => raise Fail "Truth_Result";
  fun init _ = empty;
);
val put_truth = Truth_Result.put;
val truth_cookie = (Truth_Result.get, put_truth, prefix_this "put_truth");

local

val reject_vars = fn ctxt => tap (reject_vars ctxt o Thm.term_of);

fun check_holds ctxt evaluator vs_t ct =
  let
    val t = Thm.term_of ct;
    val _ = if fastype_of t <> propT
      then error ("Not a proposition: " ^ Syntax.string_of_term ctxt t)
      else ();
    val iff = Thm.cterm_of ctxt (Term.Const (\<^const_name>\<open>Pure.eq\<close>, propT --> propT --> propT));
    val result = case partiality_as_none (run_compilation_text truth_cookie ctxt evaluator vs_t [])
     of SOME Holds => true
      | _ => false;
  in
    Thm.mk_binop iff ct (if result then \<^cprop>\<open>PROP Code_Generator.holds\<close> else ct)
  end;

val (_, raw_check_holds_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>holds_by_evaluation\<close>,
  fn (ctxt, evaluator, vs_t, ct) => check_holds ctxt evaluator vs_t ct)));

fun check_holds_oracle ctxt evaluator vs_ty_t ct =
  raw_check_holds_oracle (ctxt, evaluator, vs_ty_t, ct);

in

fun dynamic_holds_conv ctxt = Code_Thingol.dynamic_conv ctxt
  (fn program => fn vs_t => fn deps =>
    check_holds_oracle ctxt (build_compilation_text ctxt NONE program deps) vs_t)
      o reject_vars ctxt;

end; (*local*)


(** generator for computations -- partial implementations of the universal morphism from Isabelle to ML terms **)

(* auxiliary *)

val generated_computationN = "Generated_Computation";


(* possible type signatures of constants *)

fun typ_signatures' T =
  let
    val (Ts, T') = strip_type T;
  in map_range (fn n => (drop n Ts ---> T', take n Ts)) (length Ts + 1) end;

fun typ_signatures cTs =
  let
    fun add (c, T) =
      fold (fn (T, Ts) => Typtab.map_default (T, []) (cons (c, Ts)))
        (typ_signatures' T);
  in
    Typtab.empty
    |> fold add cTs
    |> Typtab.lookup_list
  end;


(* name mangling *)

local

fun tycos_of (Type (tyco, Ts)) = maps tycos_of Ts @ [tyco]
  | tycos_of _ = [];

val ml_name_of = Name.desymbolize NONE o Long_Name.base_name;

in

val covered_constsN = "covered_consts";

fun of_term_for_typ Ts =
  let
    val names = Ts
      |> map (suffix "_of_term" o space_implode "_" o map ml_name_of o tycos_of)
      |> Name.variant_list [];
  in the o AList.lookup (op =) (Ts ~~ names) end;

fun eval_for_const ctxt cTs =
  let
    fun symbol_list (c, T) = c :: maps tycos_of (Sign.const_typargs (Proof_Context.theory_of ctxt) (c, T))
    val names = cTs
      |> map (prefix "eval_" o space_implode "_" o map ml_name_of o symbol_list)
      |> Name.variant_list [];
  in the o AList.lookup (op =) (cTs ~~ names) end;

end;


(* checks for input terms *)

fun monomorphic T = fold_atyps ((K o K) false) T true;

fun check_typ ctxt T t =
  Syntax.check_term ctxt (Type.constraint T t);

fun check_computation_input ctxt cTs t =
  let
    fun check t = check_comb (strip_comb t)
    and check_comb (t as Abs _, _) =
          error ("Bad term, contains abstraction: " ^ Syntax.string_of_term ctxt t)
      | check_comb (t as Const (cT as (c, T)), ts) =
          let
            val _ = if not (member (op =) cTs cT)
              then error ("Bad term, computation cannot proceed on constant " ^ Syntax.string_of_term ctxt t)
              else ();
            val _ = if not (monomorphic T)
              then error ("Bad term, contains polymorphic constant " ^ Syntax.string_of_term ctxt t)
              else ();
            val _ = map check ts;
          in () end;
    val _ = check t;
  in t end;


(* code generation for of the universal morphism *)

val print_const = ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_typ;

fun print_of_term_funs { typ_signatures_for, eval_for_const, of_term_for_typ } Ts =
  let
    val var_names = map_range (fn n => "t" ^ string_of_int (n + 1));
    fun print_lhs c xs = "Const (" ^ quote c ^ ", _)"
      |> fold (fn x => fn s => s ^ " $ " ^ x) xs
      |> enclose "(" ")";
    fun print_rhs c Ts T xs = eval_for_const (c, Ts ---> T)
      |> fold2 (fn T' => fn x => fn s =>
         s ^ (" (" ^ of_term_for_typ T' ^ " " ^ x ^ ")")) Ts xs
    fun print_eq T (c, Ts) =
      let
        val xs = var_names (length Ts);
      in print_lhs c xs ^ " = " ^ print_rhs c Ts T xs end;
    fun print_eqs T =
      let
        val typ_signs = typ_signatures_for T;
        val name = of_term_for_typ T;
      in
        map (print_eq T) typ_signs
        |> map (prefix (name ^ " "))
        |> space_implode "\n  | "
      end;
  in
    map print_eqs Ts
    |> space_implode "\nand "
    |> prefix "fun "
  end;

fun print_computation_code ctxt compiled_value [] requested_Ts =
      if null requested_Ts then ("", [])
      else error ("No equation available for requested type "
        ^ Syntax.string_of_typ ctxt (hd requested_Ts))
  | print_computation_code ctxt compiled_value cTs requested_Ts =
      let
        val proper_cTs = map_filter I cTs;
        val typ_signatures_for = typ_signatures proper_cTs;
        fun add_typ T Ts =
          if member (op =) Ts T
          then Ts
          else case typ_signatures_for T of
            [] => error ("No equation available for requested type "
              ^ Syntax.string_of_typ ctxt T)
          | typ_signs =>
              Ts
              |> cons T
              |> fold (fold add_typ o snd) typ_signs;
        val required_Ts = fold add_typ requested_Ts [];
        val of_term_for_typ' = of_term_for_typ required_Ts;
        val eval_for_const' = eval_for_const ctxt proper_cTs;
        val eval_for_const'' = the_default "_" o Option.map eval_for_const';
        val eval_tuple = enclose "(" ")" (commas (map eval_for_const' proper_cTs));
        fun mk_abs s = "fn " ^ s ^ " => ";
        val eval_abs = space_implode ""
          (map (mk_abs o eval_for_const'') cTs);
        val of_term_code = print_of_term_funs {
          typ_signatures_for = typ_signatures_for,
          eval_for_const = eval_for_const',
          of_term_for_typ = of_term_for_typ' } required_Ts;
        val of_term_names = map (Long_Name.append generated_computationN
          o of_term_for_typ') requested_Ts;
      in
        cat_lines [
          "structure " ^ generated_computationN ^ " =",
          "struct",
          "",
          "val " ^ covered_constsN ^ " = " ^ ML_Syntax.print_list print_const proper_cTs ^ ";",
          "",
          "val " ^ eval_tuple ^ " = " ^ compiled_value ^ " ()",
          "  (" ^ eval_abs,
          "    " ^ eval_tuple ^ ");",
          "",
          of_term_code,
          "",
          "end"
        ] |> rpair of_term_names
      end;


(* dedicated preprocessor for computations *)

structure Computation_Preproc_Data = Theory_Data
(
  type T = thm list;
  val empty = [];
  val extend = I;
  val merge = Library.merge Thm.eq_thm_prop;
);

local

fun add thm thy =
  let
    val thms = Simplifier.mksimps (Proof_Context.init_global thy) thm;
  in
    thy
    |> Computation_Preproc_Data.map (fold (insert Thm.eq_thm_prop o Thm.trim_context) thms)
  end;

fun get ctxt =
  Computation_Preproc_Data.get (Proof_Context.theory_of ctxt)
  |> map (Thm.transfer' ctxt)

in

fun preprocess_conv { ctxt } = 
  let
    val rules = get ctxt;
  in fn ctxt' => Raw_Simplifier.rewrite ctxt' false rules end;

fun preprocess_term { ctxt } =
  let
    val rules = map (Logic.dest_equals o Thm.plain_prop_of) (get ctxt);
  in fn ctxt' => Pattern.rewrite_term (Proof_Context.theory_of ctxt') rules [] end;

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>code_computation_unfold\<close>
    (Scan.succeed (Thm.declaration_attribute (fn thm => Context.mapping (add thm) I)))
    "preprocessing equations for computation");

end;


(* mounting computations *)

fun prechecked_computation T raw_computation ctxt =
  check_typ ctxt T
  #> reject_vars ctxt
  #> raw_computation ctxt;

fun prechecked_conv T raw_conv ctxt =
  tap (check_typ ctxt T o reject_vars ctxt o Thm.term_of)
  #> raw_conv ctxt;

fun checked_computation cTs raw_computation ctxt =
  check_computation_input ctxt cTs
  #> Exn.interruptible_capture raw_computation
  #> partiality_as_none;

fun mount_computation ctxt cTs T raw_computation lift_postproc =
  let
    val preprocess = preprocess_term { ctxt = ctxt };
    val computation = prechecked_computation T (Code_Preproc.static_value
      { ctxt = ctxt, lift_postproc = lift_postproc, consts = [] }
      (K (checked_computation cTs raw_computation)));
  in fn ctxt' => preprocess ctxt' #> computation ctxt' end;

fun mount_computation_conv ctxt cTs T raw_computation conv =
  let
    val preprocess = preprocess_conv { ctxt = ctxt };
    val computation_conv = prechecked_conv T (Code_Preproc.static_conv
      { ctxt = ctxt, consts = [] }
      (K (fn ctxt' => fn t =>
        case checked_computation cTs raw_computation ctxt' t of
          SOME x => conv ctxt' x
        | NONE => Conv.all_conv)));
  in fn ctxt' => preprocess ctxt' then_conv computation_conv ctxt' end;

local

fun holds ct = Thm.mk_binop \<^cterm>\<open>Pure.eq :: prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  ct \<^cprop>\<open>PROP Code_Generator.holds\<close>;

val (_, holds_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>holds\<close>, holds)));

in

fun mount_computation_check ctxt cTs raw_computation =
  mount_computation_conv ctxt cTs \<^typ>\<open>prop\<close> raw_computation
    ((K o K) holds_oracle);

end;


(** variants of universal runtime code generation **)

(*FIXME consolidate variants*)

fun runtime_code'' ctxt module_name program tycos consts =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (ml_modules, target_names) =
      Code_Target.produce_code_for ctxt
        target module_name NONE [] program false (map Constant consts @ map Type_Constructor tycos);
    val ml_code = space_implode "\n\n" (map snd ml_modules);
    val (consts', tycos') = chop (length consts) target_names;
    val consts_map = map2 (fn const =>
      fn NONE =>
          error ("Constant " ^ (quote o Code.string_of_const thy) const ^
            "\nhas a user-defined serialization")
       | SOME const' => (const, const')) consts consts'
    val tycos_map = map2 (fn tyco =>
      fn NONE =>
          error ("Type " ^ quote (Proof_Context.markup_type ctxt tyco) ^
            "\nhas a user-defined serialization")
        | SOME tyco' => (tyco, tyco')) tycos tycos';
  in (ml_code, (tycos_map, consts_map)) end;

fun runtime_code' ctxt some_module_name named_tycos named_consts computation_Ts program evals vs_ty_evals deps =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun the_const (Const cT) = cT
      | the_const t = error ("No constant after preprocessing: " ^ Syntax.string_of_term ctxt t)
    val raw_computation_cTs = case evals of
        Abs (_, _, t) => (map the_const o snd o strip_comb) t
      | _ => error ("Bad term after preprocessing: " ^ Syntax.string_of_term ctxt evals);
    val computation_cTs = fold_rev (fn cT => fn cTs =>
      (if member (op =) cTs (SOME cT) then NONE else SOME cT) :: cTs) raw_computation_cTs [];
    val consts' = fold (fn NONE => I | SOME (c, _) => insert (op =) c)
      computation_cTs named_consts;
    val program' = Code_Thingol.consts_program ctxt consts';
      (*FIXME insufficient interfaces require double invocation of code generator*)
    val program'' = Code_Symbol.Graph.merge (K true) (program, program');
    val ((ml_modules, compiled_value), deresolve) =
      Code_Target.compilation_text' ctxt target some_module_name program''
        (map Code_Symbol.Type_Constructor named_tycos @ map Code_Symbol.Constant consts' @ deps) true vs_ty_evals;
        (*FIXME constrain signature*)
    fun deresolve_tyco tyco = case (deresolve o Code_Symbol.Type_Constructor) tyco of
          NONE => error ("Type " ^ quote (Proof_Context.markup_type ctxt tyco) ^
            "\nhas a user-defined serialization")
        | SOME c' => c';
    fun deresolve_const c = case (deresolve o Code_Symbol.Constant) c of
          NONE => error ("Constant " ^ (quote o Code.string_of_const thy) c ^
            "\nhas a user-defined serialization")
        | SOME c' => c';
    val tyco_names =  map deresolve_tyco named_tycos;
    val const_names = map deresolve_const named_consts;
    val generated_code = space_implode "\n\n" (map snd ml_modules);
    val (of_term_code, of_term_names) =
      print_computation_code ctxt compiled_value computation_cTs computation_Ts;
    val compiled_computation = generated_code ^ "\n" ^ of_term_code;
  in
    compiled_computation
    |> rpair { tyco_map = named_tycos ~~ tyco_names,
      const_map = named_consts ~~ const_names,
      of_term_map = computation_Ts ~~ of_term_names }
  end;

fun funs_of_maps { tyco_map, const_map, of_term_map } =
  { name_for_tyco = the o AList.lookup (op =) tyco_map,
    name_for_const = the o AList.lookup (op =) const_map,
    of_term_for_typ = the o AList.lookup (op =) of_term_map };

fun runtime_code ctxt some_module_name named_tycos named_consts computation_Ts program evals vs_ty_evals deps =
  runtime_code' ctxt some_module_name named_tycos named_consts computation_Ts program evals vs_ty_evals deps
  ||> funs_of_maps;


(** code and computation antiquotations **)

local

val mount_computationN = prefix_this "mount_computation";
val mount_computation_convN = prefix_this "mount_computation_conv";
val mount_computation_checkN = prefix_this "mount_computation_check";

structure Code_Antiq_Data = Proof_Data
(
  type T = { named_consts: string list,
    computation_Ts: typ list, computation_cTs: (string * typ) list,
    position_index: int,
    generated_code: (string * {
      name_for_tyco: string -> string,
      name_for_const: string -> string,
      of_term_for_typ: typ -> string
    }) lazy
  };
  val empty: T = { named_consts = [],
    computation_Ts = [], computation_cTs = [],
    position_index = 0,
    generated_code = Lazy.lazy (fn () => raise Fail "empty")
  };
  fun init _ = empty;
);

val current_position_index = #position_index o Code_Antiq_Data.get;

fun register { named_consts, computation_Ts, computation_cTs } ctxt =
  let
    val data = Code_Antiq_Data.get ctxt;
    val named_consts' = union (op =) named_consts (#named_consts data);
    val computation_Ts' = union (op =) computation_Ts (#computation_Ts data);
    val computation_cTs' = union (op =) computation_cTs (#computation_cTs data);
    val position_index' = #position_index data + 1;
    fun generated_code' () =
      let
        val evals =
          Abs ("eval", map snd computation_cTs' ---> Term.aT [],
            list_comb (Bound 0, map Const computation_cTs'))
          |> preprocess_term { ctxt = ctxt } ctxt
      in Code_Thingol.dynamic_value ctxt
        (K I) (runtime_code ctxt NONE [] named_consts' computation_Ts') evals
      end;
  in
    ctxt
    |> Code_Antiq_Data.put { 
        named_consts = named_consts',
        computation_Ts = computation_Ts',
        computation_cTs = computation_cTs',
        position_index = position_index',
        generated_code = Lazy.lazy generated_code'
      }
  end;

fun register_const const =
  register { named_consts = [const],
    computation_Ts = [],
    computation_cTs = [] };

fun register_computation cTs T =
  register { named_consts = [],
    computation_Ts = [T],
    computation_cTs = cTs };

fun print body_code_for ctxt ctxt' =
  let
    val position_index = current_position_index ctxt;
    val (code, name_ofs) = (Lazy.force o #generated_code o Code_Antiq_Data.get) ctxt';
    val context_code = if position_index = 0 then code else "";
    val body_code = body_code_for name_ofs (ML_Context.struct_name ctxt');
  in (context_code, body_code) end;

fun print_code ctxt const =
  print (fn { name_for_const, ... } => fn prfx =>
    Long_Name.append prfx (name_for_const const)) ctxt;

fun print_computation kind ctxt T =
  print (fn { of_term_for_typ, ... } => fn prfx =>
    enclose "(" ")" (space_implode " " [
      kind,
      "(Context.proof_of (Context.the_generic_context ()))",
      Long_Name.implode [prfx, generated_computationN, covered_constsN],
      (ML_Syntax.atomic o ML_Syntax.print_typ) T,
      Long_Name.append prfx (of_term_for_typ T)
    ])) ctxt;

fun print_computation_check ctxt =
  print (fn { of_term_for_typ, ... } => fn prfx =>
    enclose "(" ")" (space_implode " " [
      mount_computation_checkN,
      "(Context.proof_of (Context.the_generic_context ()))",
      Long_Name.implode [prfx, generated_computationN, covered_constsN],
      Long_Name.append prfx (of_term_for_typ \<^typ>\<open>prop\<close>)
    ])) ctxt;

fun add_all_constrs ctxt (dT as Type (tyco, Ts)) =
  case Code.get_type (Proof_Context.theory_of ctxt) tyco of
    ((vs, constrs), false) =>
      let
        val subst_TFree = the o AList.lookup (op =) (map fst vs ~~ Ts);
        val cs = map (fn (c, (_, Ts')) =>
          (c, (map o map_atyps) (fn TFree (v, _) => subst_TFree v) Ts'
            ---> dT)) constrs;
      in
        union (op =) cs
        #> fold (add_all_constrs ctxt) Ts
      end
  | (_, true) => I;

fun prep_spec ctxt (raw_ts, raw_dTs) =
  let
    val ts = map (Syntax.check_term ctxt) raw_ts;
    val dTs = map (Syntax.check_typ ctxt) raw_dTs;
  in
    []
    |> (fold o fold_aterms)
      (fn (t as Const (cT as (_, T))) =>
        if not (monomorphic T) then error ("Polymorphic constant: " ^ Syntax.string_of_term ctxt t)
        else insert (op =) cT | _ => I) ts
    |> fold (fn dT =>
        if not (monomorphic dT) then error ("Polymorphic datatype: " ^ Syntax.string_of_typ ctxt dT)
        else add_all_constrs ctxt dT) dTs
  end;

in

fun ml_code_antiq raw_const ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val const = Code.check_const thy raw_const;
  in (print_code ctxt const, register_const const ctxt) end;

fun gen_ml_computation_antiq kind (raw_T, raw_spec) ctxt =
  let
    val cTs = prep_spec ctxt raw_spec;
    val T = Syntax.check_typ ctxt raw_T;
    val _ = if not (monomorphic T)
      then error ("Polymorphic type: " ^ Syntax.string_of_typ ctxt T)
      else ();
  in (print_computation kind ctxt T, register_computation cTs T ctxt) end;

val ml_computation_antiq = gen_ml_computation_antiq mount_computationN;

val ml_computation_conv_antiq = gen_ml_computation_antiq mount_computation_convN;

fun ml_computation_check_antiq raw_spec ctxt =
  let
    val cTs = insert (op =) (dest_Const \<^Const>\<open>holds\<close>) (prep_spec ctxt raw_spec);
  in (print_computation_check ctxt, register_computation cTs \<^typ>\<open>prop\<close> ctxt) end;

end; (*local*)


(** reflection support **)

fun check_datatype thy tyco some_consts =
  let
    val declared_constrs = (map fst o snd o fst o Code.get_type thy) tyco;
    val constrs = case some_consts
     of SOME [] => []
      | SOME consts =>
          let
            val missing_constrs = subtract (op =) consts declared_constrs;
            val _ = if null missing_constrs then []
              else error ("Missing constructor(s) " ^ commas_quote missing_constrs
                ^ " for datatype " ^ quote tyco);
            val false_constrs = subtract (op =) declared_constrs consts;
            val _ = if null false_constrs then []
              else error ("Non-constructor(s) " ^ commas_quote false_constrs
                ^ " for datatype " ^ quote tyco)
          in consts end
      | NONE => declared_constrs;
  in (tyco, constrs) end;

fun add_eval_tyco (tyco, tyco') thy =
  let
    val k = Sign.arity_number thy tyco;
    fun pr pr' _ [] = tyco'
      | pr pr' _ [ty] =
          Code_Printer.concat [pr' Code_Printer.BR ty, tyco']
      | pr pr' _ tys =
          Code_Printer.concat [Code_Printer.enum "," "(" ")" (map (pr' Code_Printer.BR) tys), tyco']
  in
    thy
    |> Code_Target.set_printings (Type_Constructor (tyco, [(target, SOME (k, pr))]))
  end;

fun add_eval_constr (const, const') thy =
  let
    val k = Code.args_number thy const;
    fun pr pr' fxy ts = Code_Printer.brackify fxy
      (const' :: the_list (Code_Printer.tuplify pr' Code_Printer.BR (map fst ts)));
  in
    thy
    |> Code_Target.set_printings (Constant (const,
      [(target, SOME (Code_Printer.simple_const_syntax (k, pr)))]))
  end;

fun add_eval_const (const, const') = Code_Target.set_printings (Constant
  (const, [(target, SOME (Code_Printer.simple_const_syntax (0, (K o K o K) const')))]));

fun process_reflection (code, (tyco_map, (constr_map, const_map))) module_name NONE thy =
      thy
      |> Code_Target.add_reserved target module_name
      |> Context.theory_map (compile_ML true code)
      |> fold (add_eval_tyco o apsnd Code_Printer.str) tyco_map
      |> fold (add_eval_constr o apsnd Code_Printer.str) constr_map
      |> fold (add_eval_const o apsnd Code_Printer.str) const_map
  | process_reflection (code, _) _ (SOME binding) thy =
      let
        val code_binding = Path.map_binding Code_Target.code_path binding;
        val preamble =
          "(* Generated from " ^
            Path.implode (Resources.thy_path (Path.basic (Context.theory_name thy))) ^
          "; DO NOT EDIT! *)";
        val thy' = Code_Target.export code_binding (preamble ^ "\n\n" ^ code) thy;
        val _ = Code_Target.code_export_message thy';
      in thy' end;

fun gen_code_reflect prep_type prep_const raw_datatypes raw_functions module_name file_prefix thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val datatypes = map (fn (raw_tyco, raw_cos) =>
      (prep_type ctxt raw_tyco, (Option.map o map) (prep_const thy) raw_cos)) raw_datatypes;
    val (tycos, constrs) = map_split (uncurry (check_datatype thy)) datatypes
      |> apsnd flat;
    val functions = map (prep_const thy) raw_functions;
    val consts = constrs @ functions;
    val program = Code_Thingol.consts_program ctxt consts;
    val result = runtime_code'' ctxt module_name program tycos consts
      |> (apsnd o apsnd) (chop (length constrs));
  in
    thy
    |> process_reflection result module_name file_prefix
  end;

val code_reflect = gen_code_reflect Code_Target.cert_tyco (K I);
val code_reflect_cmd = gen_code_reflect Code_Target.read_tyco Code.read_const;


(** Isar setup **)

local

val parse_consts_spec =
  Scan.optional (Scan.lift (Args.$$$ "terms" -- Args.colon) |-- Scan.repeat1 Args.term) []
  -- Scan.optional (Scan.lift (Args.$$$ "datatypes"  -- Args.colon) |-- Scan.repeat1 Args.typ) [];

in

val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>code\<close>
    Args.term (K ml_code_antiq)
  #> ML_Antiquotation.declaration \<^binding>\<open>computation\<close>
    (Args.typ -- parse_consts_spec) (K ml_computation_antiq)
  #> ML_Antiquotation.declaration \<^binding>\<open>computation_conv\<close>
    (Args.typ -- parse_consts_spec) (K ml_computation_conv_antiq)
  #> ML_Antiquotation.declaration \<^binding>\<open>computation_check\<close>
    parse_consts_spec (K ml_computation_check_antiq));

end;

local

val parse_datatype =
  Parse.name -- Scan.optional (\<^keyword>\<open>=\<close> |--
    (((Parse.sym_ident || Parse.string) >> (fn "_" => NONE | _ => Scan.fail ()))
    || ((Parse.term ::: (Scan.repeat (\<^keyword>\<open>|\<close> |-- Parse.term))) >> SOME))) (SOME []);

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_reflect\<close>
    "enrich runtime environment with generated code"
    (Parse.name -- Scan.optional (\<^keyword>\<open>datatypes\<close> |-- Parse.!!! (parse_datatype
      ::: Scan.repeat (\<^keyword>\<open>and\<close> |-- parse_datatype))) []
    -- Scan.optional (\<^keyword>\<open>functions\<close> |-- Parse.!!!  (Scan.repeat1 Parse.name)) []
    -- Scan.option (\<^keyword>\<open>file_prefix\<close> |-- Parse.!!! (Parse.position Parse.embedded))
    >> (fn (((module_name, raw_datatypes), raw_functions), file_prefix) =>
      Toplevel.theory (fn thy =>
        code_reflect_cmd raw_datatypes raw_functions module_name
          (Option.map Path.explode_binding file_prefix) thy)));

end; (*local*)


(** using external SML files as substitute for proper definitions -- only for polyml!  **)

local

structure Loaded_Values = Theory_Data
(
  type T = string list
  val empty = []
  val extend = I
  fun merge data : T = Library.merge (op =) data
);

fun notify_val (string, value) = 
  let
    val _ = #enterVal ML_Env.name_space (string, value);
    val _ = Theory.setup (Loaded_Values.map (insert (op =) string));
  in () end;

fun abort _ = error "Only value bindings allowed.";

val notifying_context : ML_Compiler0.context =
 {name_space =
   {lookupVal    = #lookupVal ML_Env.name_space,
    lookupType   = #lookupType ML_Env.name_space,
    lookupFix    = #lookupFix ML_Env.name_space,
    lookupStruct = #lookupStruct ML_Env.name_space,
    lookupSig    = #lookupSig ML_Env.name_space,
    lookupFunct  = #lookupFunct ML_Env.name_space,
    enterVal     = notify_val,
    enterType    = abort,
    enterFix     = abort,
    enterStruct  = abort,
    enterSig     = abort,
    enterFunct   = abort,
    allVal       = #allVal ML_Env.name_space,
    allType      = #allType ML_Env.name_space,
    allFix       = #allFix ML_Env.name_space,
    allStruct    = #allStruct ML_Env.name_space,
    allSig       = #allSig ML_Env.name_space,
    allFunct     = #allFunct ML_Env.name_space},
  print_depth = NONE,
  here = #here ML_Env.context,
  print = #print ML_Env.context,
  error = #error ML_Env.context};

in

fun use_file filepath thy =
  let
    val thy' = Loaded_Values.put [] thy;
    val _ = Context.put_generic_context ((SOME o Context.Theory) thy');
    val _ =
      ML_Compiler0.ML notifying_context
        {line = 0, file = Path.implode filepath, verbose = false, debug = false}
        (File.read filepath);
    val thy'' = Context.the_global_context ();
    val names = Loaded_Values.get thy'';
  in (names, thy'') end;

end;

fun add_definiendum (ml_name, (b, T)) thy =
  thy
  |> Code_Target.add_reserved target ml_name
  |> Specification.axiomatization [(b, SOME T, NoSyn)] [] [] []
  |-> (fn ([Const (const, _)], _) =>
    Code_Target.set_printings (Constant (const,
      [(target, SOME (Code_Printer.simple_const_syntax (0, (K o K o K o Code_Printer.str) ml_name)))]))
  #> tap (fn thy => Code_Target.produce_code (Proof_Context.init_global thy) false [const] target Code_Target.generatedN NONE []));

fun process_file filepath (definienda, thy) =
  let
    val (ml_names, thy') = use_file filepath thy;
    val superfluous = subtract (fn ((name1, _), name2) => name1 = name2) definienda ml_names;
    val _ = if null superfluous then ()
      else error ("Value binding(s) " ^ commas_quote superfluous
        ^ " found in external file " ^ Path.print filepath
        ^ " not present among the given contants binding(s).");
    val these_definienda = AList.make (the o AList.lookup (op =) definienda) ml_names;
    val thy'' = fold add_definiendum these_definienda thy';
    val definienda' = fold (AList.delete (op =)) ml_names definienda;
  in (definienda', thy'') end;

fun polyml_as_definition bTs filepaths thy =
  let
    val definienda = map (fn bT => ((Binding.name_of o fst) bT, bT)) bTs;
    val (remaining, thy') = fold process_file filepaths (definienda, thy);
    val _ = if null remaining then ()
      else error ("Constant binding(s) " ^ commas_quote (map fst remaining)
        ^ " not present in external file(s).");
  in thy' end;

end; (*struct*)
