(*  Title:      Pure/ML/ml_instantiate.ML
    Author:     Makarius

ML antiquotation to instantiate logical entities.
*)

signature ML_INSTANTIATE =
sig
  val make_ctyp: Proof.context -> typ -> ctyp
  val make_cterm: Proof.context -> term -> cterm
  type insts = ((indexname * sort) * typ) list * ((indexname * typ) * term) list
  type cinsts = ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list
  val instantiate_typ: insts -> typ -> typ
  val instantiate_ctyp: Position.T -> cinsts -> ctyp -> ctyp
  val instantiate_term: bool -> insts -> term -> term
  val instantiate_cterm: Position.T -> bool -> cinsts -> cterm -> cterm
  val instantiate_thm: Position.T -> bool -> cinsts -> thm -> thm
  val instantiate_thms: Position.T -> bool -> cinsts -> thm list -> thm list
  val get_thms: Proof.context -> int -> thm list
  val get_thm: Proof.context -> int -> thm
end;

structure ML_Instantiate: ML_INSTANTIATE =
struct

(* exported operations *)

fun make_ctyp ctxt T = Thm.ctyp_of ctxt T |> Thm.trim_context_ctyp;
fun make_cterm ctxt t = Thm.cterm_of ctxt t |> Thm.trim_context_cterm;

type insts = ((indexname * sort) * typ) list * ((indexname * typ) * term) list
type cinsts = ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list

fun instantiate_typ (insts: insts) =
  Term_Subst.instantiateT (TVars.make (#1 insts));

fun instantiate_ctyp pos (cinsts: cinsts) cT =
  Thm.instantiate_ctyp (TVars.make (#1 cinsts)) cT
  handle CTERM (msg, args) => Exn.reraise (CTERM (msg ^ Position.here pos, args));

fun instantiate_term beta (insts: insts) =
  let
    val instT = TVars.make (#1 insts);
    val instantiateT = Term_Subst.instantiateT instT;
    val inst = Vars.make ((map o apfst o apsnd) instantiateT (#2 insts));
  in (if beta then Term_Subst.instantiate_beta else Term_Subst.instantiate) (instT, inst) end;

fun make_cinsts (cinsts: cinsts) =
  let
    val cinstT = TVars.make (#1 cinsts);
    val instantiateT = Term_Subst.instantiateT (TVars.map (K Thm.typ_of) cinstT);
    val cinst = Vars.make ((map o apfst o apsnd) instantiateT (#2 cinsts));
  in (cinstT, cinst) end;

fun instantiate_cterm pos beta cinsts ct =
  (if beta then Thm.instantiate_beta_cterm else Thm.instantiate_cterm) (make_cinsts cinsts) ct
  handle CTERM (msg, args) => Exn.reraise (CTERM (msg ^ Position.here pos, args));

fun instantiate_thm pos beta cinsts th =
  (if beta then Thm.instantiate_beta else Thm.instantiate) (make_cinsts cinsts) th
  handle THM (msg, i, args) => Exn.reraise (THM (msg ^ Position.here pos, i, args));

fun instantiate_thms pos beta cinsts = map (instantiate_thm pos beta cinsts);


(* context data *)

structure Data = Proof_Data
(
  type T = int * thm list Inttab.table;
  fun init _ = (0, Inttab.empty);
);

fun put_thms ths ctxt =
  let
    val (i, thms) = Data.get ctxt;
    val ctxt' = ctxt |> Data.put (i + 1, Inttab.update (i, map Thm.trim_context ths) thms);
  in (i, ctxt') end;

fun get_thms ctxt i = the (Inttab.lookup (#2 (Data.get ctxt)) i);
fun get_thm ctxt i = the_single (get_thms ctxt i);


(* ML antiquotation *)

local

val make_keywords =
  Thy_Header.get_keywords'
  #> Keyword.no_major_keywords
  #> Keyword.add_major_keywords ["typ", "term", "prop", "ctyp", "cterm", "cprop", "lemma"];

val parse_inst_name = Parse.position (Parse.type_ident >> pair true || Parse.name >> pair false);

val parse_inst =
  (parse_inst_name -- (Parse.$$$ "=" |-- Parse.!!! Parse.embedded_ml) ||
    Scan.ahead parse_inst_name -- Parse.embedded_ml)
  >> (fn (((b, a), pos), ml) => (b, ((a, pos), ml)));

val parse_insts =
  Parse.and_list1 parse_inst >> (List.partition #1 #> apply2 (map #2));

val ml = ML_Lex.tokenize_no_range;
val ml_range = ML_Lex.tokenize_range;
fun ml_parens x = ml "(" @ x @ ml ")";
fun ml_bracks x = ml "[" @ x @ ml "]";
fun ml_commas xs = flat (separate (ml ", ") xs);
val ml_list = ml_bracks o ml_commas;
fun ml_pair (x, y) = ml_parens (ml_commas [x, y]);
val ml_list_pair = ml_list o ListPair.map ml_pair;
val ml_here = ML_Syntax.atomic o ML_Syntax.print_position;

fun get_tfree envT (a, pos) =
  (case AList.lookup (op =) envT a of
    SOME S => (a, S)
  | NONE => error ("No occurrence of type variable " ^ quote a ^ Position.here pos));

fun check_free ctxt env (x, pos) =
  (case AList.lookup (op =) env x of
    SOME T =>
      (Context_Position.reports ctxt (map (pair pos) (Syntax_Phases.markup_free ctxt x)); (x, T))
  | NONE => error ("No occurrence of variable " ^ quote x ^ Position.here pos));

fun missing_instT pos envT instT =
  (case filter_out (fn (a, _) => exists (fn (b, _) => a = b) instT) envT of
    [] => ()
  | bad =>
      error ("No instantiation for free type variable(s) " ^ commas_quote (map #1 bad) ^
        Position.here pos));

fun missing_inst pos env inst =
  (case filter_out (fn (a, _) => exists (fn (b, _) => a = b) inst) env of
    [] => ()
  | bad =>
      error ("No instantiation for free variable(s) " ^ commas_quote (map #1 bad) ^
        Position.here pos));

fun make_instT (a, pos) T =
  (case try (Term.dest_TVar o Logic.dest_type) T of
    NONE => error ("Not a free type variable " ^ quote a ^ Position.here pos)
  | SOME v => ml (ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_sort v));

fun make_inst (a, pos) t =
  (case try Term.dest_Var t of
    NONE => error ("Not a free variable " ^ quote a ^ Position.here pos)
  | SOME v => ml (ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_typ v));

fun make_env ts =
  let
    val envT = fold Term.add_tfrees ts [];
    val env = fold Term.add_frees ts [];
  in (envT, env) end;

fun prepare_insts pos {schematic} ctxt1 ctxt0 (instT, inst) ts =
  let
    val (envT, env) = make_env ts;
    val freesT = map (Logic.mk_type o TFree o get_tfree envT) instT;
    val frees = map (Free o check_free ctxt1 env) inst;
    val (ts', (varsT, vars)) =
      Variable.export_terms ctxt1 ctxt0 (ts @ freesT @ frees)
      |> chop (length ts) ||> chop (length freesT);
    val ml_insts = (map2 make_instT instT varsT, map2 make_inst inst vars);
  in
    if schematic then ()
    else
      let val (envT', env') = make_env ts' in
        missing_instT pos (subtract (eq_fst op =) envT' envT) instT;
        missing_inst pos (subtract (eq_fst op =) env' env) inst
      end;
    (ml_insts, ts')
  end;

fun prepare_ml range kind ml1 ml2 ml_val (ml_instT, ml_inst) ctxt =
  let
    val (ml_name, ctxt') = ML_Context.variant kind ctxt;
    val ml_env = ml ("val " ^ ml_name ^ " = ") @ ml ml1 @ ml_parens (ml ml_val) @ ml ";\n";
    fun ml_body (ml_argsT, ml_args) =
      ml_parens (ml ml2 @
        ml_pair (ml_list_pair (ml_instT, ml_argsT), ml_list_pair (ml_inst, ml_args)) @
        ml_range range (ML_Context.struct_name ctxt ^ "." ^ ml_name));
  in ((ml_env, ml_body), ctxt') end;

fun prepare_beta {beta} = " " ^ Value.print_bool beta;

fun prepare_type range ((((kind, pos), ml1, ml2), schematic), s) insts ctxt =
  let
    val T = Syntax.read_typ ctxt s;
    val t = Logic.mk_type T;
    val ctxt1 = Proof_Context.augment t ctxt;
    val (ml_insts, T') =
      prepare_insts pos schematic ctxt1 ctxt insts [t] ||> (the_single #> Logic.dest_type);
  in prepare_ml range kind ml1 ml2 (ML_Syntax.print_typ T') ml_insts ctxt end;

fun prepare_term read range ((((kind, pos), ml1, ml2), schematic), (s, fixes)) beta insts ctxt =
  let
    val ctxt' = #2 (Proof_Context.add_fixes_cmd fixes ctxt);
    val t = read ctxt' s;
    val ctxt1 = Proof_Context.augment t ctxt';
    val (ml_insts, t') = prepare_insts pos schematic ctxt1 ctxt insts [t] ||> the_single;
  in prepare_ml range kind ml1 (ml2 ^ prepare_beta beta) (ML_Syntax.print_term t') ml_insts ctxt end;

fun prepare_lemma range ((pos, schematic), make_lemma) beta insts ctxt =
  let
    val (ths, (props, ctxt1)) = make_lemma ctxt
    val (i, thms_ctxt) = put_thms ths ctxt;
    val ml_insts = #1 (prepare_insts pos schematic ctxt1 ctxt insts props);
    val args = ml_here pos ^ prepare_beta beta;
    val (ml1, ml2) =
      if length ths = 1
      then ("ML_Instantiate.get_thm ML_context", "ML_Instantiate.instantiate_thm " ^ args)
      else ("ML_Instantiate.get_thms ML_context", "ML_Instantiate.instantiate_thms " ^ args);
  in prepare_ml range "lemma" ml1 ml2 (ML_Syntax.print_int i) ml_insts thms_ctxt end;

fun typ_ml (kind, pos: Position.T) = ((kind, pos), "", "ML_Instantiate.instantiate_typ ");
fun term_ml (kind, pos: Position.T) = ((kind, pos), "", "ML_Instantiate.instantiate_term ");
fun ctyp_ml (kind, pos) =
  ((kind, pos),
    "ML_Instantiate.make_ctyp ML_context", "ML_Instantiate.instantiate_ctyp " ^ ml_here pos);
fun cterm_ml (kind, pos) =
  ((kind, pos),
    "ML_Instantiate.make_cterm ML_context", "ML_Instantiate.instantiate_cterm " ^ ml_here pos);

val command_name = Parse.position o Parse.command_name;

val parse_beta = Args.mode "no_beta" >> (fn b => {beta = not b});
val parse_schematic = Args.mode "schematic" >> (fn b => {schematic = b});

fun parse_body range =
  (command_name "typ" >> typ_ml || command_name "ctyp" >> ctyp_ml) -- parse_schematic --
    Parse.!!! Parse.typ >> (K o prepare_type range) ||
  (command_name "term" >> term_ml || command_name "cterm" >> cterm_ml) -- parse_schematic --
    Parse.!!! (Parse.term -- Parse.for_fixes) >> prepare_term Syntax.read_term range ||
  (command_name "prop" >> term_ml || command_name "cprop" >> cterm_ml) -- parse_schematic --
    Parse.!!! (Parse.term -- Parse.for_fixes) >> prepare_term Syntax.read_prop range ||
  (command_name "lemma" >> #2) -- parse_schematic -- ML_Thms.embedded_lemma >> prepare_lemma range;

val _ = Theory.setup
  (ML_Context.add_antiquotation_embedded \<^binding>\<open>instantiate\<close>
    (fn range => fn input => fn ctxt =>
      let
        val ((beta, insts), prepare_val) = input
          |> Parse.read_embedded ctxt (make_keywords ctxt)
              (parse_beta -- (parse_insts --| Parse.$$$ "in") -- parse_body range);

        val (((ml_env, ml_body), decls), ctxt1) = ctxt
          |> prepare_val beta (apply2 (map #1) insts)
          ||>> ML_Context.expand_antiquotes_list (op @ (apply2 (map #2) insts));

        fun decl' ctxt' =
          let val (ml_args_env, ml_args) = split_list (decls ctxt')
          in (ml_env @ flat ml_args_env, ml_body (chop (length (#1 insts)) ml_args)) end;
      in (decl', ctxt1) end));

in end;

end;
