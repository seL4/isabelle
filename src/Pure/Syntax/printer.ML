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
  TypArg of int |
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
  | is_arg (TypArg _) = true
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
      | [TypArg p1, String (_, d), TypArg p2] => SOME (p1, p2, d, p)
      | _ => NONE))
  |> get_first (fn (p1, p2, d, p) =>
      if p1 = p + 1 andalso p2 = p + 1 then SOME {assoc = No_Assoc, delim = d, pri = p}
      else if p1 = p andalso p2 = p + 1 then SOME {assoc = Left_Assoc, delim = d, pri = p}
      else if p1 = p + 1 andalso p2 = p then SOME {assoc = Right_Assoc, delim = d, pri = p}
      else NONE);

end;


(* xprod_to_fmt *)

local

fun make_arg (s, p) =
  (if s = "type" then TypArg else Arg)
  (if Lexicon.is_terminal s then 1000 else p);

fun make_string s = String ([], s);
fun make_literal s = String (Lexicon.literal_markup s, s);

in

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
          | count_args (TypArg _ :: syms) = Integer.add 1 #> count_args syms
          | count_args (String _ :: syms) = count_args syms
          | count_args (Break _ :: syms) = count_args syms
          | count_args (Block (_, bsyms) :: syms) = count_args syms #> count_args bsyms
          | count_args [] = I;
      in
        (case make_symbs xsymbs of
          (symbs, []) => SOME (const, (symbs, count_args symbs 0, pri))
        | _ => raise Fail "Unbalanced pretty-printing blocks")
      end;

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

fun pretty ctxt tabs trf markup_trans markup_extern ast0 =
  let
    val type_mode = Config.get ctxt pretty_type_mode;
    val curried = Config.get ctxt pretty_curried;
    val show_brackets = Config.get ctxt show_brackets;

    (*default applications: prefix / postfix*)
    val appT =
      if type_mode then Syntax_Trans.tappl_ast_tr'
      else if curried then Syntax_Trans.applC_ast_tr'
      else Syntax_Trans.appl_ast_tr';

    fun synT _ ([], args) = ([], args)
      | synT m (Arg p :: symbs, t :: args) =
          let val (Ts, args') = synT m (symbs, args);
          in (astT (t, p) @ Ts, args') end
      | synT m (TypArg p :: symbs, t :: args) =
          let
            val (Ts, args') = synT m (symbs, args);
          in
            if type_mode then (astT (t, p) @ Ts, args')
            else
              let val ctxt' = ctxt
                |> Config.put pretty_type_mode true
                |> Config.put pretty_priority p
              in (pretty ctxt' tabs trf markup_trans markup_extern t @ Ts, args') end
          end
      | synT m (String (literal_markup, s) :: symbs, args) =
          let
            val (Ts, args') = synT m (symbs, args);
            val T = Pretty.marks_str (if null literal_markup then [] else m @ literal_markup, s);
          in (T :: Ts, args') end
      | synT m (Block ({markup, consistent, unbreakable, indent}, bsymbs) :: symbs, args) =
          let
            val (bTs, args') = synT m (bsymbs, args);
            val (Ts, args'') = synT m (symbs, args');
            val T =
              Pretty.markup_blocks {markup = markup, consistent = consistent, indent = indent} bTs
              |> unbreakable ? Pretty.unbreakable;
          in (T :: Ts, args'') end
      | synT m (Break i :: symbs, args) =
          let
            val (Ts, args') = synT m (symbs, args);
            val T = if i < 0 then Pretty.fbrk else Pretty.brk i;
          in (T :: Ts, args') end

    and parT m (pr, args, p, p': int) = #1 (synT m
          (if p > p' orelse (show_brackets andalso p' <> 1000 andalso not (is_chain pr)) then
            [Block (Syntax_Ext.block_indent 1, String ([], "(") :: pr @ [String ([], ")")])]
           else pr, args))

    and atomT a = Pretty.marks_str (#1 markup_extern a, #2 markup_extern a)

    and prefixT (_, a, [], _) = [atomT a]
      | prefixT (c, _, args, p) = astT (appT (c, args), p)

    and splitT 0 ([x], ys) = (x, ys)
      | splitT 0 (rev_xs, ys) = (Ast.Appl (rev rev_xs), ys)
      | splitT n (rev_xs, y :: ys) = splitT (n - 1) (y :: rev_xs, ys)

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;

        (*find matching table entry, or print as prefix / postfix*)
        fun prnt ([], []) = prefixT tup
          | prnt ([], tb :: tbs) = prnt (Symtab.lookup_list tb a, tbs)
          | prnt ((pr, n, p') :: prnps, tbs) =
              if nargs = n then parT (#1 markup_extern a) (pr, args, p, p')
              else if nargs > n andalso not type_mode then
                astT (appT (splitT n ([c], args)), p)
              else prnt (prnps, tbs);
      in
        (case markup_trans a args of
          SOME prt => [prt]
        | NONE => astT (trf a ctxt args, p) handle Match => prnt ([], tabs))
      end

    and astT (c as Ast.Constant a, p) = combT (c, a, [], p)
      | astT (ast as Ast.Variable _, _) = [Ast.pretty_ast ast]
      | astT (Ast.Appl ((c as Ast.Constant a) :: (args as _ :: _)), p) = combT (c, a, args, p)
      | astT (Ast.Appl (f :: (args as _ :: _)), p) = astT (appT (f, args), p)
      | astT (ast as Ast.Appl _, _) = raise Ast.AST ("pretty: malformed ast", [ast]);
  in astT (ast0, Config.get ctxt pretty_priority) end;


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

