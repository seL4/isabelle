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
  val term_of_typ: Proof.context -> typ -> term
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

fun parsetree_to_ast ctxt constrain_pos trf parsetree =
  let
    val tsig = ProofContext.tsig_of ctxt;

    val get_class = ProofContext.read_class ctxt;
    val get_type = #1 o dest_Type o ProofContext.read_type_name_proper ctxt false;
    fun markup_class c = [Name_Space.markup_entry (Type.class_space tsig) c];
    fun markup_type c = [Name_Space.markup_entry (Type.type_space tsig) c];

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
              Ast.Variable (Term_Position.encode (Lexicon.pos_of_token tok))]
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

fun decode_term _ (result as (_: Position.reports, Exn.Exn _)) = result
  | decode_term ctxt (reports0, Exn.Result tm) =
      let
        val consts = ProofContext.consts_of ctxt;
        fun get_const a =
          ((true, #1 (Term.dest_Const (ProofContext.read_const_proper ctxt false a)))
            handle ERROR _ => (false, Consts.intern consts a));
        val get_free = ProofContext.intern_skolem ctxt;
        fun markup_const c = [Name_Space.markup_entry (Consts.space_of consts) c];
        fun markup_free x =
          [if can Name.dest_skolem x then Markup.skolem else Markup.free] @
          (if not (Variable.is_body ctxt) orelse Variable.is_fixed ctxt x then []
           else [Markup.hilite]);
        fun markup_var xi = [Markup.name (Term.string_of_vname xi) Markup.var];
        fun markup_bound def id =
          [Markup.properties [(if def then Markup.defN else Markup.refN, id)] Markup.bound];

        val decodeT = typ_of_term (ProofContext.get_sort ctxt (term_sorts tm));

        val reports = Unsynchronized.ref reports0;
        fun report ps = Position.reports reports ps;

        fun decode ps qs bs (Const ("_constrain", _) $ t $ typ) =
              (case Term_Position.decode_position typ of
                SOME p => decode (p :: ps) qs bs t
              | NONE => Type.constraint (decodeT typ) (decode ps qs bs t))
          | decode ps qs bs (Const ("_constrainAbs", _) $ t $ typ) =
              (case Term_Position.decode_position typ of
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


(* parse raw asts *)

fun parse_asts ctxt raw root (syms, pos) =
  let
    val syn = ProofContext.syn_of ctxt;
    val ast_tr = Syntax.parse_ast_translation syn;

    val toks = Syntax.tokenize syn raw syms;
    val _ = List.app (Lexicon.report_token ctxt) toks;

    val pts = Syntax.parse ctxt syn root (filter Lexicon.is_proper toks)
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
    val parsetree_to_ast = parsetree_to_ast ctxt constrain_pos ast_tr;
  in map parsetree_to_ast pts end;

fun parse_raw ctxt root input =
  let
    val syn = ProofContext.syn_of ctxt;
    val tr = Syntax.parse_translation syn;
    val parse_rules = Syntax.parse_rules syn;
  in
    parse_asts ctxt false root input
    |> (map o apsnd o Exn.maps_result)
        (Ast.normalize ctxt parse_rules #> Exn.interruptible_capture (ast_to_term ctxt tr))
  end;


(* parse logical entities *)

fun parse_failed ctxt pos msg kind =
  cat_error msg ("Failed to parse " ^ kind ^
    Markup.markup Markup.report (Context_Position.reported_text ctxt pos Markup.bad ""));

fun parse_sort ctxt text =
  let
    val (syms, pos) = Syntax.parse_token ctxt Markup.sort text;
    val S =
      parse_raw ctxt "sort" (syms, pos)
      |> report_result ctxt pos
      |> sort_of_term
      handle ERROR msg => parse_failed ctxt pos msg "sort";
  in Type.minimize_sort (ProofContext.tsig_of ctxt) S end;

fun parse_typ ctxt text =
  let
    val (syms, pos) = Syntax.parse_token ctxt Markup.typ text;
    val T =
      parse_raw ctxt "type" (syms, pos)
      |> report_result ctxt pos
      |> (fn t => typ_of_term (ProofContext.get_sort ctxt (term_sorts t)) t)
      handle ERROR msg => parse_failed ctxt pos msg "type";
  in T end;

fun parse_term is_prop ctxt text =
  let
    val (markup, kind, root, constrain) =
      if is_prop
      then (Markup.prop, "proposition", "prop", Type.constraint propT)
      else (Markup.term, "term", Config.get ctxt Syntax.default_root, I);
    val (syms, pos) = Syntax.parse_token ctxt markup text;
  in
    let
      val results = parse_raw ctxt root (syms, pos) |> map (decode_term ctxt);
      val ambiguity = length (proper_results results);

      val level = Config.get ctxt Syntax.ambiguity_level;
      val limit = Config.get ctxt Syntax.ambiguity_limit;

      fun ambig_msg () =
        if ambiguity > 1 andalso ambiguity <= level then
          "Got more than one parse tree.\n\
          \Retry with smaller syntax_ambiguity_level for more information."
        else "";

      (*brute-force disambiguation via type-inference*)
      fun check t = (Syntax.check_term ctxt (constrain t); Exn.Result t)
        handle exn as ERROR _ => Exn.Exn exn;

      val results' =
        if ambiguity > 1 then
          (Par_List.map_name "Syntax_Phases.parse_term" o apsnd o Exn.maps_result)
            check results
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
    end handle ERROR msg => parse_failed ctxt pos msg kind
  end;


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



(** encode parse trees **)

(* term_of_sort *)

fun term_of_sort S =
  let
    val class = Lexicon.const o Lexicon.mark_class;

    fun classes [c] = class c
      | classes (c :: cs) = Lexicon.const "_classes" $ class c $ classes cs;
  in
    (case S of
      [] => Lexicon.const "_topsort"
    | [c] => class c
    | cs => Lexicon.const "_sort" $ classes cs)
  end;


(* term_of_typ *)

fun term_of_typ ctxt ty =
  let
    val show_sorts = Config.get ctxt show_sorts;

    fun of_sort t S =
      if show_sorts then Lexicon.const "_ofsort" $ t $ term_of_sort S
      else t;

    fun term_of (Type (a, Ts)) =
          Term.list_comb (Lexicon.const (Lexicon.mark_type a), map term_of Ts)
      | term_of (TFree (x, S)) =
          if is_some (Term_Position.decode x) then Lexicon.free x
          else of_sort (Lexicon.const "_tfree" $ Lexicon.free x) S
      | term_of (TVar (xi, S)) = of_sort (Lexicon.const "_tvar" $ Lexicon.var xi) S;
  in term_of ty end;


(* simple_ast_of *)

fun simple_ast_of ctxt =
  let
    val tune_var = if Config.get ctxt show_question_marks then I else unprefix "?";
    fun ast_of (Const (c, _)) = Ast.Constant c
      | ast_of (Free (x, _)) = Ast.Variable x
      | ast_of (Var (xi, _)) = Ast.Variable (tune_var (Term.string_of_vname xi))
      | ast_of (t as _ $ _) =
          let val (f, args) = strip_comb t
          in Ast.mk_appl (ast_of f) (map ast_of args) end
      | ast_of (Bound i) = Ast.Variable ("B." ^ string_of_int i)
      | ast_of (Abs _) = raise Fail "simple_ast_of: Abs";
  in ast_of end;


(* sort_to_ast and typ_to_ast *)

fun ast_of_termT ctxt trf tm =
  let
    val ctxt' = Config.put show_sorts false ctxt;
    fun ast_of (t as Const ("_tfree", _) $ Free _) = simple_ast_of ctxt t
      | ast_of (t as Const ("_tvar", _) $ Var _) = simple_ast_of ctxt t
      | ast_of (Const (a, _)) = trans a []
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, _), args) => trans a args
          | (f, args) => Ast.Appl (map ast_of (f :: args)))
      | ast_of t = simple_ast_of ctxt t
    and trans a args = ast_of (trf a ctxt' dummyT args)
      handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args);
  in ast_of tm end;

fun sort_to_ast ctxt trf S = ast_of_termT ctxt trf (term_of_sort S);
fun typ_to_ast ctxt trf T = ast_of_termT ctxt trf (term_of_typ ctxt T);


(* term_to_ast *)

fun term_to_ast idents is_syntax_const ctxt trf tm =
  let
    val show_types =
      Config.get ctxt show_types orelse Config.get ctxt show_sorts orelse
      Config.get ctxt show_all_types;
    val show_structs = Config.get ctxt show_structs;
    val show_free_types = Config.get ctxt show_free_types;
    val show_all_types = Config.get ctxt show_all_types;

    val {structs, fixes} = idents;

    fun mark_atoms ((t as Const (c, _)) $ u) =
          if member (op =) Syntax.token_markers c
          then t $ u else mark_atoms t $ mark_atoms u
      | mark_atoms (t $ u) = mark_atoms t $ mark_atoms u
      | mark_atoms (Abs (x, T, t)) = Abs (x, T, mark_atoms t)
      | mark_atoms (t as Const (c, T)) =
          if is_syntax_const c then t
          else Const (Lexicon.mark_const c, T)
      | mark_atoms (t as Free (x, T)) =
          let val i = find_index (fn s => s = x) structs + 1 in
            if i = 0 andalso member (op =) fixes x then
              Const (Lexicon.mark_fixed x, T)
            else if i = 1 andalso not show_structs then
              Lexicon.const "_struct" $ Lexicon.const "_indexdefault"
            else Lexicon.const "_free" $ t
          end
      | mark_atoms (t as Var (xi, T)) =
          if xi = Syntax.dddot_indexname then Const ("_DDDOT", T)
          else Lexicon.const "_var" $ t
      | mark_atoms a = a;

    fun prune_typs (t_seen as (Const _, _)) = t_seen
      | prune_typs (t as Free (x, ty), seen) =
          if ty = dummyT then (t, seen)
          else if not show_free_types orelse member (op aconv) seen t then (Lexicon.free x, seen)
          else (t, t :: seen)
      | prune_typs (t as Var (xi, ty), seen) =
          if ty = dummyT then (t, seen)
          else if not show_free_types orelse member (op aconv) seen t then (Lexicon.var xi, seen)
          else (t, t :: seen)
      | prune_typs (t_seen as (Bound _, _)) = t_seen
      | prune_typs (Abs (x, ty, t), seen) =
          let val (t', seen') = prune_typs (t, seen);
          in (Abs (x, ty, t'), seen') end
      | prune_typs (t1 $ t2, seen) =
          let
            val (t1', seen') = prune_typs (t1, seen);
            val (t2', seen'') = prune_typs (t2, seen');
          in (t1' $ t2', seen'') end;

    fun ast_of tm =
      (case strip_comb tm of
        (t as Abs _, ts) => Ast.mk_appl (ast_of (Syn_Trans.abs_tr' ctxt t)) (map ast_of ts)
      | ((c as Const ("_free", _)), Free (x, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.free x) T) (map ast_of ts)
      | ((c as Const ("_var", _)), Var (xi, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.var xi) T) (map ast_of ts)
      | ((c as Const ("_bound", _)), Free (x, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.free x) T) (map ast_of ts)
      | (Const ("_idtdummy", T), ts) =>
          Ast.mk_appl (constrain (Lexicon.const "_idtdummy") T) (map ast_of ts)
      | (const as Const (c, T), ts) =>
          if show_all_types
          then Ast.mk_appl (constrain const T) (map ast_of ts)
          else trans c T ts
      | (t, ts) => Ast.mk_appl (simple_ast_of ctxt t) (map ast_of ts))

    and trans a T args = ast_of (trf a ctxt T args)
      handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args)

    and constrain t T =
      if show_types andalso T <> dummyT then
        Ast.Appl [Ast.Constant "_constrain", simple_ast_of ctxt t,
          ast_of_termT ctxt trf (term_of_typ ctxt T)]
      else simple_ast_of ctxt t;
  in
    tm
    |> Syn_Trans.prop_tr'
    |> show_types ? (#1 o prune_typs o rpair [])
    |> mark_atoms
    |> ast_of
  end;



(** unparse **)

local

fun free_or_skolem ctxt x =
  let
    val m =
      if Variable.is_fixed ctxt x orelse Syntax.is_pretty_global ctxt
      then Markup.fixed x
      else Markup.hilite;
  in
    if can Name.dest_skolem x
    then ([m, Markup.skolem], ProofContext.revert_skolem ctxt x)
    else ([m, Markup.free], x)
  end;

fun var_or_skolem s =
  (case Lexicon.read_variable s of
    SOME (x, i) =>
      (case try Name.dest_skolem x of
        NONE => (Markup.var, s)
      | SOME x' => (Markup.skolem, Term.string_of_vname (x', i)))
  | NONE => (Markup.var, s));

fun unparse_t t_to_ast prt_t markup ctxt t =
  let
    val syn = ProofContext.syn_of ctxt;

    fun token_trans "_tfree" x = SOME (Pretty.mark_str (Markup.tfree, x))
      | token_trans "_tvar" x = SOME (Pretty.mark_str (Markup.tvar, x))
      | token_trans "_free" x = SOME (Pretty.marks_str (free_or_skolem ctxt x))
      | token_trans "_bound" x = SOME (Pretty.mark_str (Markup.bound, x))
      | token_trans "_var" x = SOME (Pretty.mark_str (var_or_skolem x))
      | token_trans "_numeral" x = SOME (Pretty.mark_str (Markup.numeral, x))
      | token_trans "_inner_string" x = SOME (Pretty.mark_str (Markup.inner_string, x))
      | token_trans _ _ = NONE;

    val markup_extern = Lexicon.unmark
     {case_class = fn x => ([Markup.tclass x], Type.extern_class (ProofContext.tsig_of ctxt) x),
      case_type = fn x => ([Markup.tycon x], Type.extern_type (ProofContext.tsig_of ctxt) x),
      case_const = fn x => ([Markup.const x], Consts.extern (ProofContext.consts_of ctxt) x),
      case_fixed = fn x => free_or_skolem ctxt x,
      case_default = fn x => ([], x)};
  in
    t_to_ast ctxt (Syntax.print_translation syn) t
    |> Ast.normalize ctxt (Syntax.print_rules syn)
    |> prt_t ctxt (Syntax.prtabs syn) (Syntax.print_ast_translation syn) token_trans markup_extern
    |> Pretty.markup markup
  end;

in

val unparse_sort = unparse_t sort_to_ast Printer.pretty_typ_ast Markup.sort;
val unparse_typ = unparse_t typ_to_ast Printer.pretty_typ_ast Markup.typ;

fun unparse_term ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val syn = ProofContext.syn_of ctxt;
    val idents = Local_Syntax.idents_of (ProofContext.syntax_of ctxt);
  in
    unparse_t (term_to_ast idents (Syntax.is_const syn))
      (Printer.pretty_term_ast (not (Pure_Thy.old_appl_syntax thy)))
      Markup.term ctxt
  end;

end;



(** translations **)

(* type propositions *)

fun type_prop_tr' ctxt T [Const ("\\<^const>Pure.sort_constraint", _)] =
      Lexicon.const "_sort_constraint" $ term_of_typ (Config.put show_sorts true ctxt) T
  | type_prop_tr' ctxt T [t] =
      Lexicon.const "_ofclass" $ term_of_typ ctxt T $ t
  | type_prop_tr' _ T ts = raise TYPE ("type_prop_tr'", [T], ts);


(* type reflection *)

fun type_tr' ctxt (Type ("itself", [T])) ts =
      Term.list_comb (Lexicon.const "_TYPE" $ term_of_typ ctxt T, ts)
  | type_tr' _ _ _ = raise Match;


(* type constraints *)

fun type_constraint_tr' ctxt (Type ("fun", [T, _])) (t :: ts) =
      Term.list_comb (Lexicon.const "_constrain" $ t $ term_of_typ ctxt T, ts)
  | type_constraint_tr' _ _ _ = raise Match;


(* setup translations *)

val _ = Context.>> (Context.map_theory
  (Sign.add_advanced_trfunsT
   [("_type_prop", type_prop_tr'),
    ("\\<^const>TYPE", type_tr'),
    ("_type_constraint_", type_constraint_tr')]));



(** install operations **)

val _ = Syntax.install_operations
  {parse_sort = parse_sort,
   parse_typ = parse_typ,
   parse_term = parse_term false,
   parse_prop = parse_term true,
   unparse_sort = unparse_sort,
   unparse_typ = unparse_typ,
   unparse_term = unparse_term};

end;
