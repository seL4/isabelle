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
  val empty_prtabs: prtabs
  val extend_prtabs: prtabs -> string -> SynExt.xprod list -> prtabs
  val merge_prtabs: prtabs -> prtabs -> prtabs
  val pretty_term_ast: bool -> prtabs
    -> (string -> (Ast.ast list -> Ast.ast) option)
    -> (string -> (string -> string * int) option) -> Ast.ast -> Pretty.T
  val pretty_typ_ast: bool -> prtabs
    -> (string -> (Ast.ast list -> Ast.ast) option)
    -> (string -> (string -> string * int) option) -> Ast.ast -> Pretty.T
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



(** misc utils **)

(* apply print (ast) translation function *)

fun apply_trans name a f args =
  (f args handle
    Match => raise Match
  | exn => (writeln ("Error in " ^ name ^ " for " ^ quote a); raise exn));


(* simple_ast_of *)

fun simple_ast_of (Const (c, _)) = Constant c
  | simple_ast_of (Free (x, _)) = Variable x
  | simple_ast_of (Var (xi, _)) = Variable (string_of_vname xi)
  | simple_ast_of (t as _ $ _) =
      let val (f, args) = strip_comb t in
        mk_appl (simple_ast_of f) (map simple_ast_of args)
      end
  | simple_ast_of (Bound i) = Variable ("B." ^ string_of_int i)
  | simple_ast_of (Abs _) = sys_error "simple_ast_of: Abs";



(** typ_to_ast **)

fun ast_of_termT trf tm =
  let
    fun ast_of (t as Const ("_class", _) $ Free _) = simple_ast_of t
      | ast_of (t as Const ("_tfree", _) $ Free _) = simple_ast_of t
      | ast_of (t as Const ("_tvar", _) $ Var _) = simple_ast_of t
      | ast_of (Const (a, _)) = trans a []
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, _), args) => trans a args
          | (f, args) => Appl (map ast_of (f :: args)))
      | ast_of t = raise_term "ast_of_termT: bad term encoding of type" [t]
    and trans a args =
      (case trf a of
        Some f => ast_of (apply_trans "print translation" a (uncurry f) (dummyT, args))
      | None => raise Match)
          handle Match => mk_appl (Constant a) (map ast_of args);
  in
    ast_of tm
  end;

fun typ_to_ast trf T = ast_of_termT trf (term_of_typ (! show_sorts) T);



(** term_to_ast **)

fun mark_freevars (t $ u) = mark_freevars t $ mark_freevars u
  | mark_freevars (Abs (x, T, t)) = Abs (x, T, mark_freevars t)
  | mark_freevars (t as Free _) = const "_free" $ t
  | mark_freevars (t as Var _) = const "_var" $ t
  | mark_freevars a = a;

fun ast_of_term trf no_freeTs show_types show_sorts tm =
  let
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

    fun ast_of tm =
      (case strip_comb tm of
        (t as Abs _, ts) => mk_appl (ast_of (abs_tr' t)) (map ast_of ts)
      | ((c as Const ("_free", _)), Free (x, T) :: ts) =>
          mk_appl (constrain (c $ free x) T) (map ast_of ts)
      | ((c as Const ("_bound", _)), Free (x, T) :: ts) =>
          mk_appl (constrain (c $ free x) T) (map ast_of ts)
      | ((c as Const ("_var", _)), Var (xi, T) :: ts) =>
          mk_appl (constrain (c $ var xi) T) (map ast_of ts)
      | (Const (c, T), ts) => trans c T ts
      | (t, ts) => mk_appl (simple_ast_of t) (map ast_of ts))

    and trans a T args =
      (case trf a of
        Some f => ast_of (apply_trans "print translation" a (uncurry f) (T, args))
      | None => raise Match)
          handle Match => mk_appl (Constant a) (map ast_of args)

    and constrain t T =
      if show_types andalso T <> dummyT then
        Appl [Constant constrainC, simple_ast_of t,
          ast_of_termT trf (term_of_typ show_sorts T)]
      else simple_ast_of t
  in
    tm
    |> prop_tr' show_sorts
    |> (if show_types then #1 o prune_typs o rpair [] else I)
    |> mark_freevars
    |> ast_of
  end;

fun term_to_ast trf tm =
  ast_of_term trf (! show_no_free_types) (! show_types orelse ! show_sorts)
    (! show_sorts) tm;



(** type prtabs **)

datatype symb =
  Arg of int |
  TypArg of int |
  String of string |
  Break of int |
  Block of int * symb list;

type prtabs = (string * ((symb list * int * int) list) Symtab.table) list;

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

fun pretty tabs trf tokentrf type_mode curried ast0 p0 =
  let
    val trans = apply_trans "print ast translation";

    fun token_trans c [Variable x] =
          (case tokentrf c of
            None => None
          | Some f => Some (f x))
      | token_trans _ _ = None;

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
            else (pretty tabs trf tokentrf true curried t p @ Ts, args')
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

        (*find matching table entry, or print as prefix / postfix*)
        fun prnt [] = prefixT tup
          | prnt ((pr, n, p') :: prnps) =
              if nargs = n then parT (pr, args, p, p')
              else if nargs > n andalso not type_mode then
                astT (appT (splitT n ([c], args)), p)
              else prnt prnps;
      in
        (case token_trans a args of     (*try token translation function*)
          Some (s, len) => [Pretty.strlen s len]
        | None =>
            (case trf a of              (*try print translation function*)
              Some f => (astT (trans a f args, p) handle Match => prnt (get_fmts tabs a))
            | None => prnt (get_fmts tabs a)))
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

fun pretty_term_ast curried prtabs trf tokentrf ast =
  Pretty.blk (0, pretty (tabs_of prtabs (! print_mode))
    trf tokentrf false curried ast 0);


(* pretty_typ_ast *)

fun pretty_typ_ast _ prtabs trf tokentrf ast =
  Pretty.blk (0, pretty (tabs_of prtabs (! print_mode))
    trf tokentrf true false ast 0);

end;
