(*  Title:      Pure/Syntax/printer.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Pretty printing of asts, terms, types and print (ast) translation.
*)

signature PRINTER0 =
sig
  val show_brackets: bool ref
  val show_sorts: bool ref
  val show_types: bool ref
  val show_no_free_types: bool ref
  val print_mode: string list ref
end;

signature PRINTER =
sig
  include PRINTER0
  val term_to_ast: (string -> (typ -> term list -> term) option) -> term -> Ast.ast
  val typ_to_ast: (string -> (typ -> term list -> term) option) -> typ -> Ast.ast
  type prtabs
  val prmodes_of: prtabs -> string list
  val empty_prtabs: prtabs
  val extend_prtabs: prtabs -> string -> SynExt.xprod list -> prtabs
  val merge_prtabs: prtabs -> prtabs -> prtabs
  val pretty_term_ast: bool -> prtabs
    -> (string -> (Ast.ast list -> Ast.ast) option) -> Ast.ast -> Pretty.T
  val pretty_typ_ast: bool -> prtabs
    -> (string -> (Ast.ast list -> Ast.ast) option) -> Ast.ast -> Pretty.T
end;

structure Printer: PRINTER =
struct

open Lexicon Ast SynExt TypeExt SynTrans;


(** options for printing **)

val show_types = ref false;
val show_sorts = ref false;
val show_brackets = ref false;
val show_no_free_types = ref false;
val print_mode = ref ([]:string list);



(** convert term or typ to ast **)

fun apply_trans name a f args =
  (f args handle
    Match => raise Match
  | exn => (writeln ("Error in " ^ name ^ " for " ^ quote a); raise exn));


fun ast_of_term trf show_types show_sorts tm =
  let
    val no_freeTs = ! show_no_free_types;

    fun prune_typs (t_seen as (Const _, _)) = t_seen
      | prune_typs (t as Free (x, ty), seen) =
          if ty = dummyT then (t, seen)
          else if no_freeTs orelse t mem seen then (free x, seen)
          else (t, t :: seen)
      | prune_typs (t as Var (xi, ty), seen) =
          if ty = dummyT then (t, seen)
          else if no_freeTs orelse t mem seen then (var xi, seen)
          else (t, t :: seen)
      | prune_typs (t_seen as (Bound _, _)) = t_seen
      | prune_typs (Abs (x, ty, t), seen) =
          let val (t', seen') = prune_typs (t, seen);
          in (Abs (x, ty, t'), seen') end
      | prune_typs (t1 $ t2, seen) =
          let
            val (t1', seen') = prune_typs (t1, seen);
            val (t2', seen'') = prune_typs (t2, seen');
          in
            (t1' $ t2', seen'')
          end;


    fun ast_of (Const (a, T)) = trans a T []
      | ast_of (Free (x, ty)) = constrain x (free x) ty
      | ast_of (Var (xi, ty)) = constrain (string_of_vname xi) (var xi) ty
      | ast_of (Bound i) = Variable ("B." ^ string_of_int i)
      | ast_of (t as Abs _) = ast_of (abs_tr' t)
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, T), args) => trans a T args
          | (f, args) => Appl (map ast_of (f :: args)))

    and trans a T args =
      (case trf a of
        Some f => ast_of (apply_trans "print translation" a (uncurry f) (T, args))
      | None => raise Match)
          handle Match => mk_appl (Constant a) (map ast_of args)

    and constrain x t ty =
      if show_types andalso ty <> dummyT then
        ast_of (const constrainC $ t $ term_of_typ show_sorts ty)
      else Variable x;
  in
    if show_types then
      ast_of (#1 (prune_typs (prop_tr' show_sorts tm, [])))
    else ast_of (prop_tr' show_sorts tm)
  end;


(* term_to_ast *)

fun term_to_ast trf tm =
  ast_of_term trf (! show_types orelse ! show_sorts) (! show_sorts) tm;


(* typ_to_ast *)

fun typ_to_ast trf ty =
  ast_of_term trf false false (term_of_typ (! show_sorts) ty);



(** type prtabs **)

datatype symb =
  Arg of int |
  TypArg of int |
  String of string |
  Break of int |
  Block of int * symb list;

type prtabs = (string * ((symb list * int * int) list) Symtab.table) list;

fun prmodes_of prtabs = filter_out (equal "") (map fst prtabs);

(*find tab for mode*)
fun get_tab prtabs mode =
  if_none (assoc (prtabs, mode)) Symtab.null;

(*collect tabs for mode hierarchy (default "")*)
fun tabs_of prtabs modes =
  mapfilter (fn mode => assoc (prtabs, mode)) (modes @ [""]);

(*find formats in tab hierarchy*)
fun get_fmts [] _ = []
  | get_fmts (tab :: tabs) a = Symtab.lookup_multi (tab, a) @ get_fmts tabs a;


(* xprods_to_fmts *)

fun xprod_to_fmt (XProd (_, _, "", _)) = None
  | xprod_to_fmt (XProd (_, xsymbs, const, pri)) =
      let
        fun cons_str s (String s' :: syms) = String (s ^ s') :: syms
          | cons_str s syms = String s :: syms;

        fun arg (s, p) =
          (if s = "type" then TypArg else Arg)
          (if is_terminal s then max_pri else p);

        fun xsyms_to_syms (Delim s :: xsyms) =
              apfst (cons_str s) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Argument s_p :: xsyms) =
              apfst (cons (arg s_p)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Space s :: xsyms) =
              apfst (cons_str s) (xsyms_to_syms xsyms)
          | xsyms_to_syms (Bg i :: xsyms) =
              let
                val (bsyms, xsyms') = xsyms_to_syms xsyms;
                val (syms, xsyms'') = xsyms_to_syms xsyms';
              in
                (Block (i, bsyms) :: syms, xsyms'')
              end
          | xsyms_to_syms (Brk i :: xsyms) =
              apfst (cons (Break i)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (En :: xsyms) = ([], xsyms)
          | xsyms_to_syms [] = ([], []);

        fun nargs (Arg _ :: syms) = nargs syms + 1
          | nargs (TypArg _ :: syms) = nargs syms + 1
          | nargs (String _ :: syms) = nargs syms
          | nargs (Break _ :: syms) = nargs syms
          | nargs (Block (_, bsyms) :: syms) = nargs syms + nargs bsyms
          | nargs [] = 0;
      in
        (case xsyms_to_syms xsymbs of
          (symbs, []) => Some (const, (symbs, nargs symbs, pri))
        | _ => sys_error "xprod_to_fmt: unbalanced blocks")
      end;

fun xprods_to_fmts xprods = mapfilter xprod_to_fmt xprods;


(* empty, extend, merge prtabs *)

val empty_prtabs = [];

fun extend_prtabs prtabs mode xprods =
  let
    val fmts = xprods_to_fmts xprods;
    val tab = get_tab prtabs mode;
    val new_tab = generic_extend (op =) Symtab.dest_multi Symtab.make_multi tab fmts;
  in overwrite (prtabs, (mode, new_tab)) end;

fun merge_prtabs prtabs1 prtabs2 =
  let
    val modes = distinct (map fst (prtabs1 @ prtabs2));
    fun merge mode =
      (mode,
        generic_merge (op =) Symtab.dest_multi Symtab.make_multi
          (get_tab prtabs1 mode) (get_tab prtabs2 mode));
  in
    map merge modes
  end;



(** pretty term or typ asts **)

fun is_chain [Block (_, pr)] = is_chain pr
  | is_chain [Arg _] = true
  | is_chain _  = false;

fun pretty tabs trf type_mode curried ast0 p0 =
  let
    val trans = apply_trans "print ast translation";

    (*default applications: prefix / postfix*)
    val appT =
      if type_mode then tappl_ast_tr'
      else if curried then applC_ast_tr'
      else appl_ast_tr';

    fun synT ([], args) = ([], args)
      | synT (Arg p :: symbs, t :: args) =
          let val (Ts, args') = synT (symbs, args);
          in (astT (t, p) @ Ts, args') end
      | synT (TypArg p :: symbs, t :: args) =
          let
            val (Ts, args') = synT (symbs, args);
          in
            if type_mode then (astT (t, p) @ Ts, args')
            else (pretty tabs trf true curried t p @ Ts, args')
          end
      | synT (String s :: symbs, args) =
          let val (Ts, args') = synT (symbs, args);
          in (Pretty.str s :: Ts, args') end
      | synT (Block (i, bsymbs) :: symbs, args) =
          let
            val (bTs, args') = synT (bsymbs, args);
            val (Ts, args'') = synT (symbs, args');
          in (Pretty.blk (i, bTs) :: Ts, args'') end
      | synT (Break i :: symbs, args) =
          let val (Ts, args') = synT (symbs, args);
          in ((if i < 0 then Pretty.fbrk else Pretty.brk i) :: Ts, args') end
      | synT (_ :: _, []) = sys_error "synT"

    and parT (pr, args, p, p': int) = #1 (synT
          (if p > p' orelse
            (! show_brackets andalso p' <> max_pri andalso not (is_chain pr))
            then [Block (1, String "(" :: pr @ [String ")"])]
            else pr, args))

    and prefixT (_, a, [], _) = [Pretty.str a]
      | prefixT (c, _, args, p) =
          if c = Constant "_appl" orelse c = Constant "_applC" then
            error "Syntax insufficient for printing prefix applications!"
          else astT (appT (c, args), p)

    and splitT 0 ([x], ys) = (x, ys)
      | splitT 0 (rev_xs, ys) = (Appl (rev rev_xs), ys)
      | splitT n (rev_xs, y :: ys) = splitT (n - 1) (y :: rev_xs, ys)
      | splitT _ _ = sys_error "splitT"

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;

        (*find matching table entry, or print as prefix/postfix*)
        fun prnt [] = prefixT tup
          | prnt ((pr, n, p') :: prnps) =
              if nargs = n then parT (pr, args, p, p')
              else if nargs > n andalso not type_mode then
                astT (appT (splitT n ([c], args)), p)
              else prnt prnps;
      in
        (*try translation function first*)
        (case trf a of
          None => prnt (get_fmts tabs a)
        | Some f => (astT (trans a f args, p) handle Match => prnt (get_fmts tabs a)))
      end

    and astT (c as Constant a, p) = combT (c, a, [], p)
      | astT (Variable x, _) = [Pretty.str x]
      | astT (Appl ((c as Constant a) :: (args as _ :: _)), p) =
          combT (c, a, args, p)
      | astT (Appl (f :: (args as _ :: _)), p) = astT (appT (f, args), p)
      | astT (ast as Appl _, _) = raise_ast "pretty: malformed ast" [ast];
  in
    astT (ast0, p0)
  end;


(* pretty_term_ast *)

fun pretty_term_ast curried prtabs trf ast =
  Pretty.blk (0, pretty (tabs_of prtabs (! print_mode)) trf false curried ast 0);


(* pretty_typ_ast *)

fun pretty_typ_ast _ prtabs trf ast =
  Pretty.blk (0, pretty (tabs_of prtabs (! print_mode)) trf true false ast 0);


end;
