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
end;

signature PRINTER =
sig
  include PRINTER0
  structure Symtab: SYMTAB
  structure SynExt: SYN_EXT
  local open SynExt SynExt.Ast in
    val term_to_ast: (string -> (term list -> term) option) -> term -> ast
    val typ_to_ast: (string -> (term list -> term) option) -> typ -> ast
    type prtab
    val empty_prtab: prtab
    val extend_prtab: prtab -> xprod list -> prtab
    val merge_prtabs: prtab -> prtab -> prtab
    val pretty_term_ast: prtab -> (string -> (ast list -> ast) option)
      -> ast -> Pretty.T
    val pretty_typ_ast: prtab -> (string -> (ast list -> ast) option)
      -> ast -> Pretty.T
  end
end;

functor PrinterFun(structure Symtab: SYMTAB and TypeExt: TYPE_EXT
  and SynTrans: SYN_TRANS sharing TypeExt.SynExt = SynTrans.Parser.SynExt)
  : PRINTER =
struct

structure Symtab = Symtab;
structure SynExt = TypeExt.SynExt;
open SynTrans.Parser.Lexicon SynExt.Ast SynExt TypeExt SynTrans;


(** options for printing **)

val show_types = ref false;
val show_sorts = ref false;
val show_brackets = ref false;
val show_no_free_types = ref false;



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


    fun ast_of (Const (a, _)) = trans a []
      | ast_of (Free (x, ty)) = constrain x (free x) ty
      | ast_of (Var (xi, ty)) = constrain (string_of_vname xi) (var xi) ty
      | ast_of (Bound i) = Variable ("B." ^ string_of_int i)
      | ast_of (t as Abs _) = ast_of (abs_tr' t)
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, _), args) => trans a args
          | (f, args) => Appl (map ast_of (f :: args)))

    and trans a args =
      (case trf a of
        Some f => ast_of (apply_trans "print translation" a f args)
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
  ast_of_term trf (! show_types) (! show_sorts) tm;


(* typ_to_ast *)

fun typ_to_ast trf ty =
  ast_of_term trf false false (term_of_typ (! show_sorts) ty);



(** type prtab **)

datatype symb =
  Arg of int |
  TypArg of int |
  String of string |
  Break of int |
  Block of int * symb list;

type prtab = (symb list * int * int) Symtab.table;


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

fun xprods_to_fmts xprods =
  gen_distinct eq_fst (mapfilter xprod_to_fmt xprods);


(* empty, extend, merge prtabs *)

fun err_dup_fmts cs =
  error ("Duplicate formats in printer table for " ^ commas_quote cs);

val empty_prtab = Symtab.null;

fun extend_prtab tab xprods =
  Symtab.extend (op =) (tab, xprods_to_fmts xprods)
    handle Symtab.DUPS cs => err_dup_fmts cs;

fun merge_prtabs tab1 tab2 =
  Symtab.merge (op =) (tab1, tab2)
    handle Symtab.DUPS cs => err_dup_fmts cs;



(** pretty term or typ asts **)

fun chain [Block (_, pr)] = chain pr
  | chain [Arg _] = true
  | chain _  = false;

fun pretty prtab trf type_mode ast0 p0 =
  let
    val trans = apply_trans "print ast translation";

    val appT = if type_mode then tappl_ast_tr' else appl_ast_tr';

    fun synT ([], args) = ([], args)
      | synT (Arg p :: symbs, t :: args) =
          let val (Ts, args') = synT (symbs, args);
          in (astT (t, p) @ Ts, args') end
      | synT (TypArg p :: symbs, t :: args) =
          let
            val (Ts, args') = synT (symbs, args);
          in
            if type_mode then (astT (t, p) @ Ts, args')
            else (pretty prtab trf true t p @ Ts, args')
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
            (! show_brackets andalso p' <> max_pri andalso not (chain pr))
            then [Block (1, String "(" :: pr @ [String ")"])]
            else pr, args))

    and prefixT (_, a, [], _) = [Pretty.str a]
      | prefixT (c, _, args, p) = astT (appT (c, args), p)

    and splitT 0 ([x], ys) = (x, ys)
      | splitT 0 (rev_xs, ys) = (Appl (rev rev_xs), ys)
      | splitT n (rev_xs, y :: ys) = splitT (n - 1) (y :: rev_xs, ys)
      | splitT _ _ = sys_error "splitT"

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;

        fun prnt (pr, n, p') =
          if nargs = n then parT (pr, args, p, p')
          else if nargs < n orelse type_mode then prefixT tup
          else astT (appT (splitT n ([c], args)), p);
      in
        (case (trf a, Symtab.lookup (prtab, a)) of
          (None, None) => prefixT tup
        | (None, Some prnp) => prnt prnp
        | (Some f, None) =>
            (astT (trans a f args, p) handle Match => prefixT tup)
        | (Some f, Some prnp) =>
            (astT (trans a f args, p) handle Match => prnt prnp))
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

fun pretty_term_ast prtab trf ast =
  Pretty.blk (0, pretty prtab trf false ast 0);


(* pretty_typ_ast *)

fun pretty_typ_ast prtab trf ast =
  Pretty.blk (0, pretty prtab trf true ast 0);


end;

