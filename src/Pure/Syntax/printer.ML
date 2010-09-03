(*  Title:      Pure/Syntax/printer.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Pretty printing of asts, terms, types and print (ast) translation.
*)

signature PRINTER0 =
sig
  val show_brackets: bool Unsynchronized.ref
  val show_sorts: bool Unsynchronized.ref
  val show_types: bool Unsynchronized.ref
  val show_free_types: bool Config.T
  val show_all_types: bool Config.T
  val show_structs: bool Unsynchronized.ref
  val show_question_marks_default: bool Unsynchronized.ref
  val show_question_marks_value: Config.value Config.T
  val show_question_marks: bool Config.T
  val pp_show_brackets: Pretty.pp -> Pretty.pp
end;

signature PRINTER =
sig
  include PRINTER0
  val sort_to_ast: Proof.context ->
    (string -> (Proof.context -> bool -> typ -> term list -> term) list) -> sort -> Ast.ast
  val typ_to_ast: Proof.context ->
    (string -> (Proof.context -> bool -> typ -> term list -> term) list) -> typ -> Ast.ast
  val term_to_ast: {structs: string list, fixes: string list} -> string list -> Proof.context ->
    (string -> (Proof.context -> bool -> typ -> term list -> term) list) -> term -> Ast.ast
  type prtabs
  val empty_prtabs: prtabs
  val update_prtabs: string -> Syn_Ext.xprod list -> prtabs -> prtabs
  val remove_prtabs: string -> Syn_Ext.xprod list -> prtabs -> prtabs
  val merge_prtabs: prtabs -> prtabs -> prtabs
  val pretty_term_ast: {extern_class: string -> xstring, extern_type: string -> xstring,
      extern_const: string -> xstring} -> Proof.context -> bool -> prtabs ->
    (string -> (Proof.context -> Ast.ast list -> Ast.ast) list) ->
    (string -> (Proof.context -> string -> Pretty.T) option) -> Ast.ast -> Pretty.T list
  val pretty_typ_ast: {extern_class: string -> xstring, extern_type: string -> xstring} ->
    Proof.context -> bool -> prtabs ->
    (string -> (Proof.context -> Ast.ast list -> Ast.ast) list) ->
    (string -> (Proof.context -> string -> Pretty.T) option) -> Ast.ast -> Pretty.T list
end;

structure Printer: PRINTER =
struct


(** options for printing **)

val show_types = Unsynchronized.ref false;
val show_sorts = Unsynchronized.ref false;
val show_brackets = Unsynchronized.ref false;
val show_free_types = Config.bool (Config.declare "show_free_types" (fn _ => Config.Bool true));
val show_all_types = Config.bool (Config.declare "show_all_types" (fn _ => Config.Bool false));
val show_structs = Unsynchronized.ref false;

val show_question_marks_default = Unsynchronized.ref true;
val show_question_marks_value =
  Config.declare "show_question_marks" (fn _ => Config.Bool (! show_question_marks_default));
val show_question_marks = Config.bool show_question_marks_value;

fun pp_show_brackets pp = Pretty.pp (setmp_CRITICAL show_brackets true (Pretty.term pp),
  Pretty.typ pp, Pretty.sort pp, Pretty.classrel pp, Pretty.arity pp);



(** misc utils **)

(* apply print (ast) translation function *)

fun apply_trans ctxt fns args =
  let
    fun app_first [] = raise Match
      | app_first (f :: fs) = f ctxt args handle Match => app_first fs;
  in app_first fns end;

fun apply_typed x y fs = map (fn f => fn ctxt => f ctxt x y) fs;


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



(** sort_to_ast, typ_to_ast **)

fun ast_of_termT ctxt trf tm =
  let
    fun ast_of (t as Const ("_tfree", _) $ Free _) = simple_ast_of ctxt t
      | ast_of (t as Const ("_tvar", _) $ Var _) = simple_ast_of ctxt t
      | ast_of (Const (a, _)) = trans a []
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, _), args) => trans a args
          | (f, args) => Ast.Appl (map ast_of (f :: args)))
      | ast_of t = simple_ast_of ctxt t
    and trans a args =
      ast_of (apply_trans ctxt (apply_typed false dummyT (trf a)) args)
        handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args);
  in ast_of tm end;

fun sort_to_ast ctxt trf S = ast_of_termT ctxt trf (Type_Ext.term_of_sort S);
fun typ_to_ast ctxt trf T = ast_of_termT ctxt trf (Type_Ext.term_of_typ (! show_sorts) T);



(** term_to_ast **)

fun ast_of_term idents consts ctxt trf show_types show_sorts show_structs tm =
  let
    val show_free_types = Config.get ctxt show_free_types;
    val show_all_types = Config.get ctxt show_all_types;

    val {structs, fixes} = idents;

    fun mark_atoms ((t as Const (c, T)) $ u) =
          if member (op =) Syn_Ext.standard_token_markers c
          then t $ u else mark_atoms t $ mark_atoms u
      | mark_atoms (t $ u) = mark_atoms t $ mark_atoms u
      | mark_atoms (Abs (x, T, t)) = Abs (x, T, mark_atoms t)
      | mark_atoms (t as Const (c, T)) =
          if member (op =) consts c then t
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
          if xi = Syn_Ext.dddot_indexname then Const ("_DDDOT", T)
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
        (t as Abs _, ts) => Ast.mk_appl (ast_of (Syn_Trans.abs_tr' t)) (map ast_of ts)
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

    and trans a T args =
      ast_of (apply_trans ctxt (apply_typed show_sorts T (trf a)) args)
        handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args)

    and constrain t T =
      if show_types andalso T <> dummyT then
        Ast.Appl [Ast.Constant Syn_Ext.constrainC, simple_ast_of ctxt t,
          ast_of_termT ctxt trf (Type_Ext.term_of_typ show_sorts T)]
      else simple_ast_of ctxt t;
  in
    tm
    |> Syn_Trans.prop_tr'
    |> show_types ? (#1 o prune_typs o rpair [])
    |> mark_atoms
    |> ast_of
  end;

fun term_to_ast idents consts ctxt trf tm =
  ast_of_term idents consts ctxt trf
    (! show_types orelse ! show_sorts orelse Config.get ctxt show_all_types)
    (! show_sorts) (! show_structs) tm;



(** type prtabs **)

datatype symb =
  Arg of int |
  TypArg of int |
  String of string |
  Space of string |
  Break of int |
  Block of int * symb list;

type prtabs = (string * ((symb list * int * int) list) Symtab.table) list;

fun mode_tab prtabs mode = the_default Symtab.empty (AList.lookup (op =) prtabs mode);
fun mode_tabs prtabs modes = map_filter (AList.lookup (op =) prtabs) (modes @ [""]);


(* xprod_to_fmt *)

fun xprod_to_fmt (Syn_Ext.XProd (_, _, "", _)) = NONE
  | xprod_to_fmt (Syn_Ext.XProd (_, xsymbs, const, pri)) =
      let
        fun arg (s, p) =
          (if s = "type" then TypArg else Arg)
          (if Lexicon.is_terminal s then Syn_Ext.max_pri else p);

        fun xsyms_to_syms (Syn_Ext.Delim s :: xsyms) =
              apfst (cons (String s)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Syn_Ext.Argument s_p :: xsyms) =
              apfst (cons (arg s_p)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Syn_Ext.Space s :: xsyms) =
              apfst (cons (Space s)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Syn_Ext.Bg i :: xsyms) =
              let
                val (bsyms, xsyms') = xsyms_to_syms xsyms;
                val (syms, xsyms'') = xsyms_to_syms xsyms';
              in
                (Block (i, bsyms) :: syms, xsyms'')
              end
          | xsyms_to_syms (Syn_Ext.Brk i :: xsyms) =
              apfst (cons (Break i)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Syn_Ext.En :: xsyms) = ([], xsyms)
          | xsyms_to_syms [] = ([], []);

        fun nargs (Arg _ :: syms) = nargs syms + 1
          | nargs (TypArg _ :: syms) = nargs syms + 1
          | nargs (String _ :: syms) = nargs syms
          | nargs (Space _ :: syms) = nargs syms
          | nargs (Break _ :: syms) = nargs syms
          | nargs (Block (_, bsyms) :: syms) = nargs syms + nargs bsyms
          | nargs [] = 0;
      in
        (case xsyms_to_syms xsymbs of
          (symbs, []) => SOME (const, (symbs, nargs symbs, pri))
        | _ => raise Fail "Unbalanced pretty-printing blocks")
      end;


(* empty, extend, merge prtabs *)

val empty_prtabs = [];

fun update_prtabs mode xprods prtabs =
  let
    val fmts = map_filter xprod_to_fmt xprods;
    val tab' = fold (Symtab.update_list (op =)) fmts (mode_tab prtabs mode);
  in AList.update (op =) (mode, tab') prtabs end;

fun remove_prtabs mode xprods prtabs =
  let
    val tab = mode_tab prtabs mode;
    val fmts = map_filter (fn xprod as Syn_Ext.XProd (_, _, c, _) =>
      if null (Symtab.lookup_list tab c) then NONE
      else xprod_to_fmt xprod) xprods;
    val tab' = fold (Symtab.remove_list (op =)) fmts tab;
  in AList.update (op =) (mode, tab') prtabs end;

fun merge_prtabs prtabs1 prtabs2 =
  let
    val modes = distinct (op =) (map fst (prtabs1 @ prtabs2));
    fun merge m = (m, Symtab.merge_list (op =) (mode_tab prtabs1 m, mode_tab prtabs2 m));
  in map merge modes end;



(** pretty term or typ asts **)

fun is_chain [Block (_, pr)] = is_chain pr
  | is_chain [Arg _] = true
  | is_chain _  = false;

fun pretty extern ctxt tabs trf tokentrf type_mode curried ast0 p0 =
  let
    val {extern_class, extern_type, extern_const} = extern;

    fun token_trans a x =
      (case tokentrf a of
        NONE =>
          if member (op =) Syn_Ext.standard_token_classes a
          then SOME (Pretty.str x) else NONE
      | SOME f => SOME (f ctxt x));

    (*default applications: prefix / postfix*)
    val appT =
      if type_mode then Type_Ext.tappl_ast_tr'
      else if curried then Syn_Trans.applC_ast_tr'
      else Syn_Trans.appl_ast_tr';

    fun synT _ ([], args) = ([], args)
      | synT markup (Arg p :: symbs, t :: args) =
          let val (Ts, args') = synT markup (symbs, args);
          in (astT (t, p) @ Ts, args') end
      | synT markup (TypArg p :: symbs, t :: args) =
          let
            val (Ts, args') = synT markup (symbs, args);
          in
            if type_mode then (astT (t, p) @ Ts, args')
            else (pretty extern ctxt tabs trf tokentrf true curried t p @ Ts, args')
          end
      | synT markup (String s :: symbs, args) =
          let val (Ts, args') = synT markup (symbs, args);
          in (markup (Pretty.str s) :: Ts, args') end
      | synT markup (Space s :: symbs, args) =
          let val (Ts, args') = synT markup (symbs, args);
          in (Pretty.str s :: Ts, args') end
      | synT markup (Block (i, bsymbs) :: symbs, args) =
          let
            val (bTs, args') = synT markup (bsymbs, args);
            val (Ts, args'') = synT markup (symbs, args');
            val T =
              if i < 0 then Pretty.unbreakable (Pretty.block bTs)
              else Pretty.blk (i, bTs);
          in (T :: Ts, args'') end
      | synT markup (Break i :: symbs, args) =
          let
            val (Ts, args') = synT markup (symbs, args);
            val T = if i < 0 then Pretty.fbrk else Pretty.brk i;
          in (T :: Ts, args') end

    and parT markup (pr, args, p, p': int) = #1 (synT markup
          (if p > p' orelse
            (! show_brackets andalso p' <> Syn_Ext.max_pri andalso not (is_chain pr))
            then [Block (1, Space "(" :: pr @ [Space ")"])]
            else pr, args))

    and atomT a = a |> Lexicon.unmark
     {case_class = fn c => Pretty.mark (Markup.tclass c) (Pretty.str (extern_class c)),
      case_type = fn c => Pretty.mark (Markup.tycon c) (Pretty.str (extern_type c)),
      case_const = fn c => Pretty.mark (Markup.const c) (Pretty.str (extern_const c)),
      case_fixed = fn x => the (token_trans "_free" x),
      case_default = Pretty.str}

    and prefixT (_, a, [], _) = [atomT a]
      | prefixT (c, _, args, p) = astT (appT (c, args), p)

    and splitT 0 ([x], ys) = (x, ys)
      | splitT 0 (rev_xs, ys) = (Ast.Appl (rev rev_xs), ys)
      | splitT n (rev_xs, y :: ys) = splitT (n - 1) (y :: rev_xs, ys)

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;
        val markup = a |> Lexicon.unmark
         {case_class = Pretty.mark o Markup.tclass,
          case_type = Pretty.mark o Markup.tycon,
          case_const = Pretty.mark o Markup.const,
          case_fixed = Pretty.mark o Markup.fixed,
          case_default = K I};

        (*find matching table entry, or print as prefix / postfix*)
        fun prnt ([], []) = prefixT tup
          | prnt ([], tb :: tbs) = prnt (Symtab.lookup_list tb a, tbs)
          | prnt ((pr, n, p') :: prnps, tbs) =
              if nargs = n then parT markup (pr, args, p, p')
              else if nargs > n andalso not type_mode then
                astT (appT (splitT n ([c], args)), p)
              else prnt (prnps, tbs);
      in
        (case tokentrT a args of
          SOME prt => [prt]
        | NONE => astT (apply_trans ctxt (trf a) args, p) handle Match => prnt ([], tabs))
      end

    and tokentrT a [Ast.Variable x] = token_trans a x
      | tokentrT _ _ = NONE

    and astT (c as Ast.Constant a, p) = combT (c, a, [], p)
      | astT (Ast.Variable x, _) = [Pretty.str x]
      | astT (Ast.Appl ((c as Ast.Constant a) :: (args as _ :: _)), p) = combT (c, a, args, p)
      | astT (Ast.Appl (f :: (args as _ :: _)), p) = astT (appT (f, args), p)
      | astT (ast as Ast.Appl _, _) = raise Ast.AST ("pretty: malformed ast", [ast]);
  in astT (ast0, p0) end;


(* pretty_term_ast *)

fun pretty_term_ast extern ctxt curried prtabs trf tokentrf ast =
  pretty extern ctxt (mode_tabs prtabs (print_mode_value ()))
    trf tokentrf false curried ast 0;


(* pretty_typ_ast *)

fun pretty_typ_ast {extern_class, extern_type} ctxt _ prtabs trf tokentrf ast =
  pretty {extern_class = extern_class, extern_type = extern_type, extern_const = I}
    ctxt (mode_tabs prtabs (print_mode_value ()))
    trf tokentrf true false ast 0;

end;
