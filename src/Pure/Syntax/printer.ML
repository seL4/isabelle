(*  Title:      Pure/Syntax/printer.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Pretty printing of asts, terms, types and print (ast) translation.
*)

signature BASIC_PRINTER =
sig
  val show_brackets: bool Config.T
  val show_types: bool Config.T
  val show_sorts: bool Config.T
  val show_markup: bool Config.T
  val show_consts_markup: bool Config.T
  val show_structs: bool Config.T
  val show_question_marks: bool Config.T
  val pretty_priority: int Config.T
end;

signature PRINTER =
sig
  include BASIC_PRINTER
  val show_markup_default: bool Unsynchronized.ref
  val show_type_emphasis: bool Config.T
  val type_emphasis: Proof.context -> typ -> bool
  type prtabs
  datatype assoc = No_Assoc | Left_Assoc | Right_Assoc
  val get_prefix: prtabs -> Symtab.key -> string option
  val get_binder: prtabs -> Symtab.key -> string option
  val get_infix: prtabs -> string -> {assoc: assoc, delim: string, pri: int} option
  val empty_prtabs: prtabs
  val update_prtabs: string -> Syntax_Ext.xprod list -> prtabs -> prtabs
  val remove_prtabs: string -> Syntax_Ext.xprod list -> prtabs -> prtabs
  val merge_prtabs: prtabs -> prtabs -> prtabs
  val pretty_term_ast: bool -> Proof.context -> prtabs ->
    (string -> Proof.context -> Ast.ast list -> Ast.ast) ->
    (string -> Ast.ast list -> Pretty.T option) ->
    ((string -> Markup.T list) * (string -> string)) ->
    Ast.ast -> Pretty.T list
  val pretty_typ_ast: Proof.context -> prtabs ->
    (string -> Proof.context -> Ast.ast list -> Ast.ast) ->
    (string -> Ast.ast list -> Pretty.T option) ->
    ((string -> Markup.T list) * (string -> string)) ->
    Ast.ast -> Pretty.T list
end;

structure Printer: PRINTER =
struct

(** options for printing **)

val show_brackets = Config.declare_option_bool ("show_brackets", \<^here>);
val show_types = Config.declare_option_bool ("show_types", \<^here>);
val show_sorts = Config.declare_option_bool ("show_sorts", \<^here>);
val show_markup_default = Unsynchronized.ref false;
val show_markup = Config.declare_bool ("show_markup", \<^here>) (fn _ => ! show_markup_default);
val show_consts_markup = Config.declare_bool ("show_consts_markup", \<^here>) (K false);
val show_structs = Config.declare_bool ("show_structs", \<^here>) (K false);
val show_question_marks = Config.declare_option_bool ("show_question_marks", \<^here>);
val show_type_emphasis = Config.declare_bool ("show_type_emphasis", \<^here>) (K true);

fun type_emphasis ctxt T =
  T <> dummyT andalso
    (Config.get ctxt show_types orelse Config.get ctxt show_markup orelse
      Config.get ctxt show_type_emphasis andalso not (is_Type T));



(** type prtabs **)

datatype symb =
  Arg of int |
  Arg_Type of int |
  String of Markup.T list * string |
  Break of int |
  Block of Syntax_Ext.block * symb list;

type prtabs = (string * ((symb list * int * int) list) Symtab.table) list;

fun mode_tab (prtabs: prtabs) mode = the_default Symtab.empty (AList.lookup (op =) prtabs mode);
fun mode_tabs (prtabs: prtabs) modes = map_filter (AList.lookup (op =) prtabs) (modes @ [""]);

fun lookup_default prtabs = Symtab.lookup_list (mode_tab prtabs "");


(* approximative syntax *)

datatype assoc = No_Assoc | Left_Assoc | Right_Assoc;

local

fun is_arg (Arg _) = true
  | is_arg (Arg_Type _) = true
  | is_arg _ = false;

fun is_space str = forall_string (fn s => s = " ") str;

fun clean symbs = symbs |> maps
  (fn Block (_, body) => clean body
    | symb as String (_, s) => if is_space s then [] else [symb]
    | symb => if is_arg symb then [symb] else []);

in

fun get_prefix prtabs c =
  lookup_default prtabs c
  |> get_first (fn (symbs, _, _) =>
      (case clean symbs of
        String (_, d) :: rest => if forall is_arg rest then SOME d else NONE
      | _ => NONE));

fun get_binder prtabs c =
  lookup_default prtabs (Mixfix.binder_name c)
  |> get_first (fn (symbs, _, _) =>
      (case clean symbs of
        String (_, d) :: _ => SOME d
      | _ => NONE));

fun get_infix prtabs c =
  lookup_default prtabs c
  |> map_filter (fn (symbs, _, p) =>
      (case clean symbs of
        [Arg p1, String (_, d), Arg p2] => SOME (p1, p2, d, p)
      | [Arg_Type p1, String (_, d), Arg_Type p2] => SOME (p1, p2, d, p)
      | _ => NONE))
  |> get_first (fn (p1, p2, d, p) =>
      if p1 = p + 1 andalso p2 = p + 1 then SOME {assoc = No_Assoc, delim = d, pri = p}
      else if p1 = p andalso p2 = p + 1 then SOME {assoc = Left_Assoc, delim = d, pri = p}
      else if p1 = p + 1 andalso p2 = p then SOME {assoc = Right_Assoc, delim = d, pri = p}
      else NONE);

end;


(* xprod_to_fmt *)

fun make_string s = String ([], s);
fun make_literal s = String (Lexicon.literal_markup s, s);

fun make_arg (s, p) =
  (if s = "type" then Arg_Type else Arg)
  (if Lexicon.is_terminal s then 1000 else p);

fun xprod_to_fmt (Syntax_Ext.XProd (_, _, "", _)) = NONE
  | xprod_to_fmt (Syntax_Ext.XProd (_, xsymbs, const, pri)) =
      let
        fun make_symbs (Syntax_Ext.Delim s :: xsyms) = make_symbs xsyms |>> cons (make_literal s)
          | make_symbs (Syntax_Ext.Argument a :: xsyms) = make_symbs xsyms |>> cons (make_arg a)
          | make_symbs (Syntax_Ext.Space s :: xsyms) = make_symbs xsyms |>> cons (make_string s)
          | make_symbs (Syntax_Ext.Bg block :: xsyms) =
              let
                val (bsyms, xsyms') = make_symbs xsyms;
                val (syms, xsyms'') = make_symbs xsyms';
              in (Block (block, bsyms) :: syms, xsyms'') end
          | make_symbs (Syntax_Ext.Brk i :: xsyms) = make_symbs xsyms |>> cons (Break i)
          | make_symbs (Syntax_Ext.En :: xsyms) = ([], xsyms)
          | make_symbs [] = ([], []);

        fun count_args (Arg _ :: syms) = Integer.add 1 #> count_args syms
          | count_args (Arg_Type _ :: syms) = Integer.add 1 #> count_args syms
          | count_args (String _ :: syms) = count_args syms
          | count_args (Break _ :: syms) = count_args syms
          | count_args (Block (_, bsyms) :: syms) = count_args syms #> count_args bsyms
          | count_args [] = I;
      in
        (case make_symbs xsymbs of
          (symbs, []) => SOME (const, (symbs, count_args symbs 0, pri))
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
    val fmts = map_filter (fn xprod as Syntax_Ext.XProd (_, _, c, _) =>
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

val pretty_type_mode = Config.declare_bool ("Syntax.pretty_type_mode", \<^here>) (K false);
val pretty_curried = Config.declare_bool ("Syntax.pretty_curried", \<^here>) (K false);
val pretty_priority = Config.declare_int ("Syntax.pretty_priority", \<^here>) (K 0);

local

fun split_args 0 [x] ys = (x, ys)
  | split_args 0 rev_xs ys = (Ast.Appl (rev rev_xs), ys)
  | split_args n rev_xs (y :: ys) = split_args (n - 1) (y :: rev_xs) ys;

val par_block = Syntax_Ext.block_indent 1;
val par_bg = make_literal "(";
val par_en = make_literal ")";

in

fun pretty ctxt tabs trf markup_trans (markup, extern) =
  let
    val type_mode = Config.get ctxt pretty_type_mode;
    val curried = Config.get ctxt pretty_curried;
    val show_brackets = Config.get ctxt show_brackets;

    val application =
      if type_mode then Syntax_Trans.tappl_ast_tr'
      else if curried then Syntax_Trans.applC_ast_tr'
      else Syntax_Trans.appl_ast_tr';

    fun constrain_trans (Ast.Appl [Ast.Constant (a as "_constrain"), ast, ty]) =
          markup_trans a [ast, ty]
      | constrain_trans _ = NONE;

    fun main _ (Ast.Variable x) = [Ast.pretty_var x]
      | main p (cc as Ast.Appl [Ast.Constant "_constrain", c as Ast.Constant a, _]) =
          combination p c a [] (SOME cc)
      | main p (c as Ast.Constant a) =
          combination p c a [] NONE
      | main p
          (Ast.Appl ((cc as Ast.Appl [Ast.Constant "_constrain", c as Ast.Constant a, _]) ::
            (args as _ :: _))) =
          combination p c a args (SOME cc)
      | main p (Ast.Appl ((c as Ast.Constant a) :: (args as _ :: _))) =
          combination p c a args NONE
      | main p (Ast.Appl (f :: (args as _ :: _))) = main p (application (f, args))
      | main _ (ast as Ast.Appl _) = raise Ast.AST ("pretty: malformed ast", [ast])

    and main_type p ast =
      if type_mode then main p ast
      else
        (ctxt
          |> Config.put pretty_type_mode true
          |> Config.put pretty_priority p
          |> pretty) tabs trf markup_trans (markup, extern) ast

    and combination p c a args constraint =
      (case translation p a args of
        SOME prts => prts
      | NONE =>
          (*find matching table entry, or print as prefix / postfix*)
          let
            val nargs = length args;
            val entry =
              tabs |> get_first (fn tab =>
                Symtab.lookup_list tab a |> find_first (fn (_, n, _) =>
                  nargs = n orelse nargs > n andalso not type_mode));
          in
            (case entry of
              NONE =>
                if nargs = 0 then
                  (case Option.mapPartial constrain_trans constraint of
                    SOME prt => [prt]
                  | NONE => [Pretty.marks_str (markup a, extern a)])
                else main p (application (the_default c constraint, args))
            | SOME (symbs, n, q) =>
                if nargs = n then parens p q a (symbs, args)
                else main p (application (split_args n [c] args)))
          end)

    and translation p a args =
      (case markup_trans a args of
        SOME prt => SOME [prt]
      | NONE => Option.map (main p) (SOME (trf a ctxt args) handle Match => NONE))

    and parens p q a (symbs, args) =
      let
        val symbs' =
          if p > q orelse (show_brackets andalso q <> 1000 andalso not (is_chain symbs))
          then [Block (par_block, par_bg :: symbs @ [par_en])] else symbs;
      in #1 (syntax (markup a) (symbs', args)) end

    and syntax _ ([], args) = ([], args)
      | syntax m (Arg p :: symbs, arg :: args) =
          let val (prts, args') = syntax m (symbs, args);
          in (main p arg @ prts, args') end
      | syntax m (Arg_Type p :: symbs, arg :: args) =
          let val (prts, args') = syntax m (symbs, args);
          in (main_type p arg @ prts, args') end
      | syntax m (String (literal_markup, s) :: symbs, args) =
          let
            val (prts, args') = syntax m (symbs, args);
            val m' = if null literal_markup then [] else m @ literal_markup
          in (Pretty.marks_str (m', s) :: prts, args') end
      | syntax m (Block (block, bsymbs) :: symbs, args) =
          let
            val (body, args') = syntax m (bsymbs, args);
            val (prts, args'') = syntax m (symbs, args');
          in (Syntax_Ext.pretty_block block body :: prts, args'') end
      | syntax m (Break i :: symbs, args) =
          let val (prts, args') = syntax m (symbs, args)
          in ((if i < 0 then Pretty.fbrk else Pretty.brk i) :: prts, args') end;

  in main (Config.get ctxt pretty_priority) end;

end;


(* pretty_term_ast *)

fun pretty_term_ast curried ctxt prtabs trf markup_trans markup_extern ast =
  let val ctxt' = ctxt
    |> Config.put pretty_type_mode false
    |> Config.put pretty_curried curried
  in pretty ctxt' (mode_tabs prtabs (print_mode_value ())) trf markup_trans markup_extern ast end;


(* pretty_typ_ast *)

fun pretty_typ_ast ctxt prtabs trf markup_trans markup_extern ast =
  let val ctxt' = ctxt
    |> Config.put pretty_type_mode true
    |> Config.put pretty_curried false
  in pretty ctxt' (mode_tabs prtabs (print_mode_value ())) trf markup_trans markup_extern ast end;

end;

structure Basic_Printer: BASIC_PRINTER = Printer;
open Basic_Printer;

