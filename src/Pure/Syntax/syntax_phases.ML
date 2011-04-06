(*  Title:      Pure/Syntax/syntax_phases.ML
    Author:     Makarius

Main phases of inner syntax processing, with standard implementations
of parse/unparse operations.
*)

signature SYNTAX_PHASES =
sig
  val term_sorts: term -> (indexname * sort) list
  val typ_of_term: (indexname -> sort) -> term -> typ
  val decode_term: Proof.context ->
    Position.reports * term Exn.result -> Position.reports * term Exn.result
  val parse_ast_pattern: Proof.context -> string * string -> Ast.ast
end

structure Syntax_Phases: SYNTAX_PHASES =
struct

(** decode parse trees **)

(* sort_of_term *)

fun sort_of_term tm =
  let
    fun err () = raise TERM ("sort_of_term: bad encoding of classes", [tm]);

    fun class s = Lexicon.unmark_class s handle Fail _ => err ();

    fun classes (Const (s, _)) = [class s]
      | classes (Const ("_classes", _) $ Const (s, _) $ cs) = class s :: classes cs
      | classes _ = err ();

    fun sort (Const ("_topsort", _)) = []
      | sort (Const (s, _)) = [class s]
      | sort (Const ("_sort", _) $ cs) = classes cs
      | sort _ = err ();
  in sort tm end;


(* term_sorts *)

fun term_sorts tm =
  let
    val sort_of = sort_of_term;

    fun add_env (Const ("_ofsort", _) $ Free (x, _) $ cs) =
          insert (op =) ((x, ~1), sort_of cs)
      | add_env (Const ("_ofsort", _) $ (Const ("_tfree", _) $ Free (x, _)) $ cs) =
          insert (op =) ((x, ~1), sort_of cs)
      | add_env (Const ("_ofsort", _) $ Var (xi, _) $ cs) =
          insert (op =) (xi, sort_of cs)
      | add_env (Const ("_ofsort", _) $ (Const ("_tvar", _) $ Var (xi, _)) $ cs) =
          insert (op =) (xi, sort_of cs)
      | add_env (Abs (_, _, t)) = add_env t
      | add_env (t1 $ t2) = add_env t1 #> add_env t2
      | add_env _ = I;
  in add_env tm [] end;


(* typ_of_term *)

fun typ_of_term get_sort tm =
  let
    fun err () = raise TERM ("typ_of_term: bad encoding of type", [tm]);

    fun typ_of (Free (x, _)) = TFree (x, get_sort (x, ~1))
      | typ_of (Var (xi, _)) = TVar (xi, get_sort xi)
      | typ_of (Const ("_tfree",_) $ (t as Free _)) = typ_of t
      | typ_of (Const ("_tvar",_) $ (t as Var _)) = typ_of t
      | typ_of (Const ("_ofsort", _) $ Free (x, _) $ _) = TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ (Const ("_tfree",_) $ Free (x, _)) $ _) =
          TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ Var (xi, _) $ _) = TVar (xi, get_sort xi)
      | typ_of (Const ("_ofsort", _) $ (Const ("_tvar",_) $ Var (xi, _)) $ _) =
          TVar (xi, get_sort xi)
      | typ_of (Const ("_dummy_ofsort", _) $ t) = TFree ("'_dummy_", sort_of_term t)
      | typ_of t =
          let
            val (head, args) = Term.strip_comb t;
            val a =
              (case head of
                Const (c, _) => (Lexicon.unmark_type c handle Fail _ => err ())
              | _ => err ());
          in Type (a, map typ_of args) end;
  in typ_of tm end;


(* parsetree_to_ast *)

fun lookup_tr tab c = Option.map fst (Symtab.lookup tab c);

fun parsetree_to_ast ctxt constrain_pos trf parsetree =
  let
    val {get_class, get_type, markup_class, markup_type} = ProofContext.type_context ctxt;

    val reports = Unsynchronized.ref ([]: Position.reports);
    fun report pos = Position.reports reports [pos];

    fun trans a args =
      (case trf a of
        NONE => Ast.mk_appl (Ast.Constant a) args
      | SOME f => f ctxt args);

    fun ast_of (Parser.Node ("_class_name", [Parser.Tip tok])) =
          let
            val c = get_class (Lexicon.str_of_token tok);
            val _ = report (Lexicon.pos_of_token tok) markup_class c;
          in Ast.Constant (Lexicon.mark_class c) end
      | ast_of (Parser.Node ("_type_name", [Parser.Tip tok])) =
          let
            val c = get_type (Lexicon.str_of_token tok);
            val _ = report (Lexicon.pos_of_token tok) markup_type c;
          in Ast.Constant (Lexicon.mark_type c) end
      | ast_of (Parser.Node ("_constrain_position", [pt as Parser.Tip tok])) =
          if constrain_pos then
            Ast.Appl [Ast.Constant "_constrain", ast_of pt,
              Ast.Variable (Lexicon.encode_position (Lexicon.pos_of_token tok))]
          else ast_of pt
      | ast_of (Parser.Node (a, pts)) = trans a (map ast_of pts)
      | ast_of (Parser.Tip tok) = Ast.Variable (Lexicon.str_of_token tok);

    val ast = Exn.interruptible_capture ast_of parsetree;
  in (! reports, ast) end;


(* ast_to_term *)

fun ast_to_term ctxt trf =
  let
    fun trans a args =
      (case trf a of
        NONE => Term.list_comb (Lexicon.const a, args)
      | SOME f => f ctxt args);

    fun term_of (Ast.Constant a) = trans a []
      | term_of (Ast.Variable x) = Lexicon.read_var x
      | term_of (Ast.Appl (Ast.Constant a :: (asts as _ :: _))) =
          trans a (map term_of asts)
      | term_of (Ast.Appl (ast :: (asts as _ :: _))) =
          Term.list_comb (term_of ast, map term_of asts)
      | term_of (ast as Ast.Appl _) = raise Ast.AST ("ast_to_term: malformed ast", [ast]);
  in term_of end;


(* decode_term -- transform parse tree into raw term *)

fun markup_bound def id =
  [Markup.properties [(if def then Markup.defN else Markup.refN, id)] Markup.bound];

fun decode_term _ (result as (_: Position.reports, Exn.Exn _)) = result
  | decode_term ctxt (reports0, Exn.Result tm) =
      let
        val {get_const, get_free, markup_const, markup_free, markup_var} =
          ProofContext.term_context ctxt;
        val decodeT = typ_of_term (ProofContext.get_sort ctxt (term_sorts tm));

        val reports = Unsynchronized.ref reports0;
        fun report ps = Position.reports reports ps;

        fun decode ps qs bs (Const ("_constrain", _) $ t $ typ) =
              (case Syntax.decode_position_term typ of
                SOME p => decode (p :: ps) qs bs t
              | NONE => Type.constraint (decodeT typ) (decode ps qs bs t))
          | decode ps qs bs (Const ("_constrainAbs", _) $ t $ typ) =
              (case Syntax.decode_position_term typ of
                SOME q => decode ps (q :: qs) bs t
              | NONE => Type.constraint (decodeT typ --> dummyT) (decode ps qs bs t))
          | decode _ qs bs (Abs (x, T, t)) =
              let
                val id = serial_string ();
                val _ = report qs (markup_bound true) id;
              in Abs (x, T, decode [] [] (id :: bs) t) end
          | decode _ _ bs (t $ u) = decode [] [] bs t $ decode [] [] bs u
          | decode ps _ _ (Const (a, T)) =
              (case try Lexicon.unmark_fixed a of
                SOME x => (report ps markup_free x; Free (x, T))
              | NONE =>
                  let
                    val c =
                      (case try Lexicon.unmark_const a of
                        SOME c => c
                      | NONE => snd (get_const a));
                    val _ = report ps markup_const c;
                  in Const (c, T) end)
          | decode ps _ _ (Free (a, T)) =
              (case (get_free a, get_const a) of
                (SOME x, _) => (report ps markup_free x; Free (x, T))
              | (_, (true, c)) => (report ps markup_const c; Const (c, T))
              | (_, (false, c)) =>
                  if Long_Name.is_qualified c
                  then (report ps markup_const c; Const (c, T))
                  else (report ps markup_free c; Free (c, T)))
          | decode ps _ _ (Var (xi, T)) = (report ps markup_var xi; Var (xi, T))
          | decode ps _ bs (t as Bound i) =
              (case try (nth bs) i of
                SOME id => (report ps (markup_bound false) id; t)
              | NONE => t);

        val tm' = Exn.interruptible_capture (fn () => decode [] [] [] tm) ();
      in (! reports, tm') end;



(** parse **)

(* results *)

fun ambiguity_msg pos = "Parse error: ambiguous syntax" ^ Position.str_of pos;

fun proper_results results = map_filter (fn (y, Exn.Result x) => SOME (y, x) | _ => NONE) results;
fun failed_results results = map_filter (fn (y, Exn.Exn e) => SOME (y, e) | _ => NONE) results;

fun report ctxt = List.app (fn (pos, m) => Context_Position.report ctxt pos m);

fun report_result ctxt pos results =
  (case (proper_results results, failed_results results) of
    ([], (reports, exn) :: _) => (report ctxt reports; reraise exn)
  | ([(reports, x)], _) => (report ctxt reports; x)
  | _ => error (ambiguity_msg pos));


(* parse_asts *)

fun parse_asts ctxt raw root (syms, pos) =
  let
    val {lexicon, gram, parse_ast_trtab, ...} = Syntax.rep_syntax (ProofContext.syn_of ctxt);

    val toks = Lexicon.tokenize lexicon raw syms;
    val _ = List.app (Lexicon.report_token ctxt) toks;

    val pts = Parser.parse ctxt gram root (filter Lexicon.is_proper toks)
      handle ERROR msg =>
        error (msg ^
          implode (map (Markup.markup Markup.report o Lexicon.reported_token_range ctxt) toks));
    val len = length pts;

    val limit = Config.get ctxt Syntax.ambiguity_limit;
    val _ =
      if len <= Config.get ctxt Syntax.ambiguity_level then ()
      else if not (Config.get ctxt Syntax.ambiguity_enabled) then error (ambiguity_msg pos)
      else
        (Context_Position.if_visible ctxt warning (cat_lines
          (("Ambiguous input" ^ Position.str_of pos ^
            "\nproduces " ^ string_of_int len ^ " parse trees" ^
            (if len <= limit then "" else " (" ^ string_of_int limit ^ " displayed)") ^ ":") ::
            map (Pretty.string_of o Parser.pretty_parsetree) (take limit pts))));

    val constrain_pos = not raw andalso Config.get ctxt Syntax.positions;
    val parsetree_to_ast = parsetree_to_ast ctxt constrain_pos (lookup_tr parse_ast_trtab);
  in map parsetree_to_ast pts end;


(* read_raw *)

fun read_raw ctxt root input =
  let
    val {parse_ruletab, parse_trtab, ...} = Syntax.rep_syntax (ProofContext.syn_of ctxt);
    val norm = Ast.normalize ctxt (Symtab.lookup_list parse_ruletab);
    val ast_to_term = ast_to_term ctxt (lookup_tr parse_trtab);
  in
    parse_asts ctxt false root input
    |> (map o apsnd o Exn.maps_result) (norm #> Exn.interruptible_capture ast_to_term)
  end;


(* read sorts *)

fun standard_parse_sort ctxt (syms, pos) =
  read_raw ctxt "sort" (syms, pos)
  |> report_result ctxt pos
  |> sort_of_term;


(* read types *)

fun standard_parse_typ ctxt (syms, pos) =
  read_raw ctxt "type" (syms, pos)
  |> report_result ctxt pos
  |> (fn t => typ_of_term (ProofContext.get_sort ctxt (term_sorts t)) t);


(* read terms -- brute-force disambiguation via type-inference *)

fun standard_parse_term check ctxt root (syms, pos) =
  let
    val results = read_raw ctxt root (syms, pos) |> map (decode_term ctxt);

    val level = Config.get ctxt Syntax.ambiguity_level;
    val limit = Config.get ctxt Syntax.ambiguity_limit;

    val ambiguity = length (proper_results results);

    fun ambig_msg () =
      if ambiguity > 1 andalso ambiguity <= level then
        "Got more than one parse tree.\n\
        \Retry with smaller syntax_ambiguity_level for more information."
      else "";

    val results' =
      if ambiguity > 1 then
        (Par_List.map_name "Syntax.disambig" o apsnd o Exn.maps_result) check results
      else results;
    val reports' = fst (hd results');

    val errs = map snd (failed_results results');
    val checked = map snd (proper_results results');
    val len = length checked;

    val show_term = Syntax.string_of_term (Config.put Syntax.show_brackets true ctxt);
  in
    if len = 0 then
      report_result ctxt pos
        [(reports', Exn.Exn (Exn.EXCEPTIONS (ERROR (ambig_msg ()) :: errs)))]
    else if len = 1 then
      (if ambiguity > level then
        Context_Position.if_visible ctxt warning
          "Fortunately, only one parse tree is type correct.\n\
          \You may still want to disambiguate your grammar or your input."
      else (); report_result ctxt pos results')
    else
      report_result ctxt pos
        [(reports', Exn.Exn (ERROR (cat_lines (ambig_msg () ::
          (("Ambiguous input, " ^ string_of_int len ^ " terms are type correct" ^
            (if len <= limit then "" else " (" ^ string_of_int limit ^ " displayed)") ^ ":") ::
            map show_term (take limit checked))))))]
  end;


(* standard operations *)

fun parse_failed ctxt pos msg kind =
  cat_error msg ("Failed to parse " ^ kind ^
    Markup.markup Markup.report (Context_Position.reported_text ctxt pos Markup.bad ""));

fun parse_sort ctxt text =
  let
    val (syms, pos) = Syntax.parse_token ctxt Markup.sort text;
    val S = standard_parse_sort ctxt (syms, pos)
      handle ERROR msg => parse_failed ctxt pos msg "sort";
  in Type.minimize_sort (ProofContext.tsig_of ctxt) S end;

fun parse_typ ctxt text =
  let
    val (syms, pos) = Syntax.parse_token ctxt Markup.typ text;
    val T = standard_parse_typ ctxt (syms, pos)
      handle ERROR msg => parse_failed ctxt pos msg "type";
  in T end;

fun parse_term T ctxt text =
  let
    val (T', _) = Type_Infer.paramify_dummies T 0;
    val (markup, kind) =
      if T' = propT then (Markup.prop, "proposition") else (Markup.term, "term");
    val (syms, pos) = Syntax.parse_token ctxt markup text;

    val default_root = Config.get ctxt Syntax.default_root;
    val root =
      (case T' of
        Type (c, _) =>
          if c <> "prop" andalso Type.is_logtype (ProofContext.tsig_of ctxt) c
          then default_root else c
      | _ => default_root);

    fun check t = (Syntax.check_term ctxt (Type.constraint T' t); Exn.Result t)
      handle exn as ERROR _ => Exn.Exn exn;
    val t = standard_parse_term check ctxt root (syms, pos)
      handle ERROR msg => parse_failed ctxt pos msg kind;
  in t end;


(* parse_ast_pattern *)

fun parse_ast_pattern ctxt (root, str) =
  let
    val syn = ProofContext.syn_of ctxt;

    fun constify (ast as Ast.Constant _) = ast
      | constify (ast as Ast.Variable x) =
          if Syntax.is_const syn x orelse Long_Name.is_qualified x then Ast.Constant x
          else ast
      | constify (Ast.Appl asts) = Ast.Appl (map constify asts);

    val (syms, pos) = Syntax.read_token str;
  in
    parse_asts ctxt true root (syms, pos)
    |> report_result ctxt pos
    |> constify
  end;



(** unparse **)

fun unparse_sort ctxt =
  Syntax.standard_unparse_sort {extern_class = Type.extern_class (ProofContext.tsig_of ctxt)}
    ctxt (ProofContext.syn_of ctxt);

fun unparse_typ ctxt =
  let
    val tsig = ProofContext.tsig_of ctxt;
    val extern = {extern_class = Type.extern_class tsig, extern_type = Type.extern_type tsig};
  in Syntax.standard_unparse_typ extern ctxt (ProofContext.syn_of ctxt) end;

fun unparse_term ctxt =
  let
    val tsig = ProofContext.tsig_of ctxt;
    val syntax = ProofContext.syntax_of ctxt;
    val consts = ProofContext.consts_of ctxt;
    val extern =
     {extern_class = Type.extern_class tsig,
      extern_type = Type.extern_type tsig,
      extern_const = Consts.extern consts};
  in
    Syntax.standard_unparse_term (Local_Syntax.idents_of syntax) extern ctxt
      (Local_Syntax.syn_of syntax) (not (Pure_Thy.old_appl_syntax (ProofContext.theory_of ctxt)))
  end;


(** install operations **)

val _ = Syntax.install_operations
  {parse_sort = parse_sort,
   parse_typ = parse_typ,
   parse_term = parse_term dummyT,
   parse_prop = parse_term propT,
   unparse_sort = unparse_sort,
   unparse_typ = unparse_typ,
   unparse_term = unparse_term};

end;
