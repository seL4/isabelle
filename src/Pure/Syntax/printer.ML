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
  val term_to_ast: (string -> (bool -> typ -> term list -> term) list) -> term -> Ast.ast
  val typ_to_ast: (string -> (bool -> typ -> term list -> term) list) -> typ -> Ast.ast
  val sort_to_ast: (string -> (bool -> typ -> term list -> term) list) -> sort -> Ast.ast
  type prtabs
  val empty_prtabs: prtabs
  val extend_prtabs: prtabs -> string -> SynExt.xprod list -> prtabs
  val merge_prtabs: prtabs -> prtabs -> prtabs
  val pretty_term_ast: bool -> prtabs
    -> (string -> (Ast.ast list -> Ast.ast) list)
    -> (string -> (string -> string * real) option) -> Ast.ast -> Pretty.T
  val pretty_typ_ast: bool -> prtabs
    -> (string -> (Ast.ast list -> Ast.ast) list)
    -> (string -> (string -> string * real) option) -> Ast.ast -> Pretty.T
end;

structure Printer: PRINTER =
struct


(** options for printing **)

val show_types = ref false;
val show_sorts = ref false;
val show_brackets = ref false;
val show_no_free_types = ref false;



(** misc utils **)

(* apply print (ast) translation function *)

fun apply_first [] x = raise Match
  | apply_first (f :: fs) x = f x handle Match => apply_first fs x;

fun apply_trans name a fs args =
  (apply_first fs args handle
    Match => raise Match
  | exn => (priority ("Error in " ^ name ^ " for " ^ quote a); raise exn));

fun apply_typed x y fs = map (fn f => f x y) fs;


(* simple_ast_of *)

fun simple_ast_of (Const (c, _)) = Ast.Constant c
  | simple_ast_of (Free (x, _)) = Ast.Variable x
  | simple_ast_of (Var (xi, _)) = Ast.Variable (Lexicon.string_of_vname xi)
  | simple_ast_of (t as _ $ _) =
      let val (f, args) = strip_comb t in
        Ast.mk_appl (simple_ast_of f) (map simple_ast_of args)
      end
  | simple_ast_of (Bound i) = Ast.Variable ("B." ^ string_of_int i)
  | simple_ast_of (Abs _) = sys_error "simple_ast_of: Abs";



(** sort_to_ast, typ_to_ast **)

fun ast_of_termT trf tm =
  let
    fun ast_of (t as Const ("_class", _) $ Free _) = simple_ast_of t
      | ast_of (t as Const ("_tfree", _) $ Free _) = simple_ast_of t
      | ast_of (t as Const ("_tvar", _) $ Var _) = simple_ast_of t
      | ast_of (Const (a, _)) = trans a []
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, _), args) => trans a args
          | (f, args) => Ast.Appl (map ast_of (f :: args)))
      | ast_of t = simple_ast_of t
    and trans a args =
      ast_of (apply_trans "print translation" a (apply_typed false dummyT (trf a)) args)
        handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args);
  in ast_of tm end;

fun sort_to_ast trf S = ast_of_termT trf (TypeExt.term_of_sort S);
fun typ_to_ast trf T = ast_of_termT trf (TypeExt.term_of_typ (! show_sorts) T);



(** term_to_ast **)

fun mark_freevars ((t as Const (c, _)) $ u) =
      if c mem_string TokenTrans.standard_token_markers then (t $ u)
      else t $ mark_freevars u
  | mark_freevars (t $ u) = mark_freevars t $ mark_freevars u
  | mark_freevars (Abs (x, T, t)) = Abs (x, T, mark_freevars t)
  | mark_freevars (t as Free _) = Lexicon.const "_free" $ t
  | mark_freevars (t as Var (xi, T)) =
      if xi = SynExt.dddot_indexname then Const ("_DDDOT", T)
      else Lexicon.const "_var" $ t
  | mark_freevars a = a;

fun ast_of_term trf no_freeTs show_types show_sorts tm =
  let
    fun prune_typs (t_seen as (Const _, _)) = t_seen
      | prune_typs (t as Free (x, ty), seen) =
          if ty = dummyT then (t, seen)
          else if no_freeTs orelse t mem seen then (Lexicon.free x, seen)
          else (t, t :: seen)
      | prune_typs (t as Var (xi, ty), seen) =
          if ty = dummyT then (t, seen)
          else if no_freeTs orelse t mem seen then (Lexicon.var xi, seen)
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
        (t as Abs _, ts) => Ast.mk_appl (ast_of (SynTrans.abs_tr' t)) (map ast_of ts)
      | ((c as Const ("_free", _)), Free (x, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.free x) T) (map ast_of ts)
      | ((c as Const ("_bound", _)), Free (x, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.free x) T) (map ast_of ts)
      | ((c as Const ("_var", _)), Var (xi, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.var xi) T) (map ast_of ts)
      | (Const (c, T), ts) => trans c T ts
      | (t, ts) => Ast.mk_appl (simple_ast_of t) (map ast_of ts))

    and trans a T args =
      ast_of (apply_trans "print translation" a (apply_typed show_sorts T (trf a)) args)
        handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args)

    and constrain t T =
      if show_types andalso T <> dummyT then
        Ast.Appl [Ast.Constant SynExt.constrainC, simple_ast_of t,
          ast_of_termT trf (TypeExt.term_of_typ show_sorts T)]
      else simple_ast_of t
  in
    tm
    |> SynTrans.prop_tr'
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
  if_none (assoc (prtabs, mode)) Symtab.empty;

(*collect tabs for mode hierarchy (default "")*)
fun tabs_of prtabs modes =
  mapfilter (fn mode => assoc (prtabs, mode)) (modes @ [""]);


(* xprod_to_fmt *)

fun xprod_to_fmt (SynExt.XProd (_, _, "", _)) = None
  | xprod_to_fmt (SynExt.XProd (_, xsymbs, const, pri)) =
      let
        fun cons_str s (String s' :: syms) = String (s ^ s') :: syms
          | cons_str s syms = String s :: syms;

        fun arg (s, p) =
          (if s = "type" then TypArg else Arg)
          (if Lexicon.is_terminal s then SynExt.max_pri else p);

        fun xsyms_to_syms (SynExt.Delim s :: xsyms) =
              apfst (cons_str s) (xsyms_to_syms xsyms)
          | xsyms_to_syms (SynExt.Argument s_p :: xsyms) =
              apfst (cons (arg s_p)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (SynExt.Space s :: xsyms) =
              apfst (cons_str s) (xsyms_to_syms xsyms)
          | xsyms_to_syms (SynExt.Bg i :: xsyms) =
              let
                val (bsyms, xsyms') = xsyms_to_syms xsyms;
                val (syms, xsyms'') = xsyms_to_syms xsyms';
              in
                (Block (i, bsyms) :: syms, xsyms'')
              end
          | xsyms_to_syms (SynExt.Brk i :: xsyms) =
              apfst (cons (Break i)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (SynExt.En :: xsyms) = ([], xsyms)
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


(* empty, extend, merge prtabs *)

val empty_prtabs = [];

fun extend_prtabs prtabs mode xprods =
  let
    val fmts = mapfilter xprod_to_fmt xprods;
    val tab = get_tab prtabs mode;
    val new_tab = foldr Symtab.update_multi (rev fmts, tab);
  in overwrite (prtabs, (mode, new_tab)) end;

fun merge_prtabs prtabs1 prtabs2 =
  let
    val modes = distinct (map fst (prtabs1 @ prtabs2));
    fun merge m = (m, Symtab.merge_multi' (op =) (get_tab prtabs1 m, get_tab prtabs2 m));
  in map merge modes end;



(** pretty term or typ asts **)

fun is_chain [Block (_, pr)] = is_chain pr
  | is_chain [Arg _] = true
  | is_chain _  = false;

fun pretty tabs trf tokentrf type_mode curried ast0 p0 =
  let
    val trans = apply_trans "print ast translation";

    fun token_trans c [Ast.Variable x] =
          (case tokentrf c of
            None => None
          | Some f => Some (f x))
      | token_trans _ _ = None;

    (*default applications: prefix / postfix*)
    val appT =
      if type_mode then TypeExt.tappl_ast_tr'
      else if curried then SynTrans.applC_ast_tr'
      else SynTrans.appl_ast_tr';

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
            (! show_brackets andalso p' <> SynExt.max_pri andalso not (is_chain pr))
            then [Block (1, String "(" :: pr @ [String ")"])]
            else pr, args))

    and prefixT (_, a, [], _) = [Pretty.str a]
      | prefixT (c, _, args, p) =
          if c = Ast.Constant "_appl" orelse c = Ast.Constant "_applC" then
            [Pretty.str "*** INSUFFICIENT SYNTAX FOR PREFIX APPLICATION ***"]
          else astT (appT (c, args), p)

    and splitT 0 ([x], ys) = (x, ys)
      | splitT 0 (rev_xs, ys) = (Ast.Appl (rev rev_xs), ys)
      | splitT n (rev_xs, y :: ys) = splitT (n - 1) (y :: rev_xs, ys)
      | splitT _ _ = sys_error "splitT"

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;

        (*find matching table entry, or print as prefix / postfix*)
        fun prnt ([], []) = prefixT tup
          | prnt ([], tb :: tbs) = prnt (Symtab.lookup_multi (tb, a), tbs)
          | prnt ((pr, n, p') :: prnps, tbs) =
              if nargs = n then parT (pr, args, p, p')
              else if nargs > n andalso not type_mode then
                astT (appT (splitT n ([c], args)), p)
              else prnt (prnps, tbs);
      in
        (case token_trans a args of     (*try token translation function*)
          Some s_len => [Pretty.raw_str s_len]
        | None =>			(*try print translation functions*)
            astT (trans a (trf a) args, p) handle Match => prnt ([], tabs))
      end

    and astT (c as Ast.Constant a, p) = combT (c, a, [], p)
      | astT (Ast.Variable x, _) = [Pretty.str x]
      | astT (Ast.Appl ((c as Ast.Constant a) :: (args as _ :: _)), p) = combT (c, a, args, p)
      | astT (Ast.Appl (f :: (args as _ :: _)), p) = astT (appT (f, args), p)
      | astT (ast as Ast.Appl _, _) = raise Ast.AST ("pretty: malformed ast", [ast]);
  in astT (ast0, p0) end;


(* pretty_term_ast *)

fun pretty_term_ast curried prtabs trf tokentrf ast =
  Pretty.blk (0, pretty (tabs_of prtabs (! print_mode))
    trf tokentrf false curried ast 0);


(* pretty_typ_ast *)

fun pretty_typ_ast _ prtabs trf tokentrf ast =
  Pretty.blk (0, pretty (tabs_of prtabs (! print_mode))
    trf tokentrf true false ast 0);

end;
