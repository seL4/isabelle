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
  val instantiate_term: insts -> term -> term
  val instantiate_cterm: Position.T -> cinsts -> cterm -> cterm
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

fun instantiate_term (insts: insts) =
  let
    val instT = TVars.make (#1 insts);
    val instantiateT = Term_Subst.instantiateT instT;
    val inst = Vars.make ((map o apfst o apsnd) instantiateT (#2 insts));
  in Term_Subst.instantiate_beta (instT, inst) end;

fun instantiate_cterm pos (cinsts: cinsts) ct =
  let
    val cinstT = TVars.make (#1 cinsts);
    val instantiateT = Term_Subst.instantiateT (TVars.map (K Thm.typ_of) cinstT);
    val cinst = Vars.make ((map o apfst o apsnd) instantiateT (#2 cinsts));
  in Thm.instantiate_beta_cterm (cinstT, cinst) ct end
  handle CTERM (msg, args) => Exn.reraise (CTERM (msg ^ Position.here pos, args));


(* ML antiquotation *)

local

fun make_keywords ctxt =
  Thy_Header.get_keywords' ctxt
  |> Keyword.no_major_keywords
  |> Keyword.add_major_keywords ["typ", "term", "prop", "ctyp", "cterm", "cprop"];

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

fun get_tfree envT (a, pos) =
  (case AList.lookup (op =) envT a of
    SOME S => (a, S)
  | NONE => error ("No occurrence of type variable " ^ quote a ^ Position.here pos));

fun check_free ctxt env (x, pos) =
  (case AList.lookup (op =) env x of
    SOME T =>
      (Context_Position.reports ctxt (map (pair pos) (Syntax_Phases.markup_free ctxt x)); (x, T))
  | NONE => error ("No occurrence of variable " ^ quote x ^ Position.here pos));

fun missing_instT envT instT =
  (case filter_out (fn (a, _) => exists (fn (b, _) => a = b) instT) envT of
    [] => ()
  | bad => error ("No instantiation for free type variable(s) " ^ commas_quote (map #1 bad)));

fun missing_inst env inst =
  (case filter_out (fn (a, _) => exists (fn (b, _) => a = b) inst) env of
    [] => ()
  | bad => error ("No instantiation for free variable(s) " ^ commas_quote (map #1 bad)));

fun make_instT (a, pos) T =
  (case try (Term.dest_TVar o Logic.dest_type) T of
    NONE => error ("Not a free type variable " ^ quote a ^ Position.here pos)
  | SOME v => ml (ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_sort v));

fun make_inst (a, pos) t =
  (case try Term.dest_Var t of
    NONE => error ("Not a free variable " ^ quote a ^ Position.here pos)
  | SOME v => ml (ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_typ v));

fun term_env t = (Term.add_tfrees t [], Term.add_frees t []);

fun prepare_insts ctxt1 ctxt0 (instT, inst) t =
  let
    val (envT, env) = term_env t;
    val freesT = map (Logic.mk_type o TFree o get_tfree envT) instT;
    val frees = map (Free o check_free ctxt1 env) inst;
    val (t' :: varsT, vars) =
      Variable.export_terms ctxt1 ctxt0 (t :: freesT @ frees)
      |> chop (1 + length freesT);

    val (envT', env') = term_env t';
    val _ = missing_instT (subtract (eq_fst op =) envT' envT) instT;
    val _ = missing_inst (subtract (eq_fst op =) env' env) inst;

    val ml_insts = (map2 make_instT instT varsT, map2 make_inst inst vars);
  in (ml_insts, t') end;

fun prepare_ml range (kind, ml1, ml2) ml_val (ml_instT, ml_inst) ctxt =
  let
    val (ml_name, ctxt') = ML_Context.variant kind ctxt;
    val ml_env = ml ("val " ^ ml_name ^ " = ") @ ml ml1 @ ml_parens (ml ml_val) @ ml ";\n";
    fun ml_body (ml_argsT, ml_args) =
      ml_parens (ml ml2 @
        ml_pair (ml_list_pair (ml_instT, ml_argsT), ml_list_pair (ml_inst, ml_args)) @
        ml_range range (ML_Context.struct_name ctxt ^ "." ^ ml_name));
  in ((ml_env, ml_body), ctxt') end;

fun prepare_type range (arg, s) insts ctxt =
  let
    val T = Syntax.read_typ ctxt s;
    val t = Logic.mk_type T;
    val ctxt1 = Proof_Context.augment t ctxt;
    val (ml_insts, T') = prepare_insts ctxt1 ctxt insts t ||> Logic.dest_type;
  in prepare_ml range arg (ML_Syntax.print_typ T') ml_insts ctxt end;

fun prepare_term read range (arg, (s, fixes)) insts ctxt =
  let
    val ctxt' = #2 (Proof_Context.add_fixes_cmd fixes ctxt);
    val t = read ctxt' s;
    val ctxt1 = Proof_Context.augment t ctxt';
    val (ml_insts, t') = prepare_insts ctxt1 ctxt insts t;
  in prepare_ml range arg (ML_Syntax.print_term t') ml_insts ctxt end;

val ml_here = ML_Syntax.atomic o ML_Syntax.print_position;

fun typ_ml (kind, _: Position.T) = (kind, "", "ML_Instantiate.instantiate_typ ");
fun term_ml (kind, _: Position.T) = (kind, "", "ML_Instantiate.instantiate_term ");
fun ctyp_ml (kind, pos) =
  (kind, "ML_Instantiate.make_ctyp ML_context", "ML_Instantiate.instantiate_ctyp " ^ ml_here pos);
fun cterm_ml (kind, pos) =
  (kind, "ML_Instantiate.make_cterm ML_context", "ML_Instantiate.instantiate_cterm " ^ ml_here pos);

val command_name = Parse.position o Parse.command_name;

fun parse_body range =
  (command_name "typ" >> typ_ml || command_name "ctyp" >> ctyp_ml) --
    Parse.!!! Parse.typ >> prepare_type range ||
  (command_name "term" >> term_ml || command_name "cterm" >> cterm_ml)
    -- Parse.!!! (Parse.term -- Parse.for_fixes) >> prepare_term Syntax.read_term range ||
  (command_name "prop" >> term_ml || command_name "cprop" >> cterm_ml)
    -- Parse.!!! (Parse.term -- Parse.for_fixes) >> prepare_term Syntax.read_prop range;

val _ = Theory.setup
  (ML_Context.add_antiquotation \<^binding>\<open>instantiate\<close> true
    (fn range => fn src => fn ctxt =>
      let
        val (insts, prepare_val) = src
          |> Parse.read_embedded_src ctxt (make_keywords ctxt)
              ((parse_insts --| Parse.$$$ "in") -- parse_body range);

        val (((ml_env, ml_body), decls), ctxt1) = ctxt
          |> prepare_val (apply2 (map #1) insts)
          ||>> ML_Context.expand_antiquotes_list (op @ (apply2 (map #2) insts));

        fun decl' ctxt' =
          let val (ml_args_env, ml_args) = split_list (decls ctxt')
          in (ml_env @ flat ml_args_env, ml_body (chop (length (#1 insts)) ml_args)) end;
      in (decl', ctxt1) end));

in end;

end;
