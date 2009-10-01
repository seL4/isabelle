(*  Title:      Pure/Syntax/printer.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Pretty printing of asts, terms, types and print (ast) translation.
*)

signature PRINTER0 =
sig
  val show_brackets: bool Unsynchronized.ref
  val show_sorts: bool Unsynchronized.ref
  val show_types: bool Unsynchronized.ref
  val show_no_free_types: bool Unsynchronized.ref
  val show_all_types: bool Unsynchronized.ref
  val pp_show_brackets: Pretty.pp -> Pretty.pp
end;

signature PRINTER =
sig
  include PRINTER0
  val term_to_ast: Proof.context ->
    (string -> (Proof.context -> bool -> typ -> term list -> term) list) -> term -> Ast.ast
  val typ_to_ast: Proof.context ->
    (string -> (Proof.context -> bool -> typ -> term list -> term) list) -> typ -> Ast.ast
  val sort_to_ast: Proof.context ->
    (string -> (Proof.context -> bool -> typ -> term list -> term) list) -> sort -> Ast.ast
  type prtabs
  val empty_prtabs: prtabs
  val update_prtabs: string -> SynExt.xprod list -> prtabs -> prtabs
  val remove_prtabs: string -> SynExt.xprod list -> prtabs -> prtabs
  val merge_prtabs: prtabs -> prtabs -> prtabs
  val pretty_term_ast: (string -> xstring) -> Proof.context -> bool -> prtabs
    -> (string -> (Proof.context -> Ast.ast list -> Ast.ast) list)
    -> (string -> (Proof.context -> string -> Pretty.T) option) -> Ast.ast -> Pretty.T list
  val pretty_typ_ast: Proof.context -> bool -> prtabs
    -> (string -> (Proof.context -> Ast.ast list -> Ast.ast) list)
    -> (string -> (Proof.context -> string -> Pretty.T) option) -> Ast.ast -> Pretty.T list
end;

structure Printer: PRINTER =
struct


(** options for printing **)

val show_types = Unsynchronized.ref false;
val show_sorts = Unsynchronized.ref false;
val show_brackets = Unsynchronized.ref false;
val show_no_free_types = Unsynchronized.ref false;
val show_all_types = Unsynchronized.ref false;

fun pp_show_brackets pp = Pretty.pp (setmp show_brackets true (Pretty.term pp),
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

fun simple_ast_of (Const (c, _)) = Ast.Constant c
  | simple_ast_of (Free (x, _)) = Ast.Variable x
  | simple_ast_of (Var (xi, _)) = Ast.Variable (Term.string_of_vname xi)
  | simple_ast_of (t as _ $ _) =
      let val (f, args) = strip_comb t in
        Ast.mk_appl (simple_ast_of f) (map simple_ast_of args)
      end
  | simple_ast_of (Bound i) = Ast.Variable ("B." ^ string_of_int i)
  | simple_ast_of (Abs _) = sys_error "simple_ast_of: Abs";



(** sort_to_ast, typ_to_ast **)

fun ast_of_termT ctxt trf tm =
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
      ast_of (apply_trans ctxt (apply_typed false dummyT (trf a)) args)
        handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args);
  in ast_of tm end;

fun sort_to_ast ctxt trf S = ast_of_termT ctxt trf (TypeExt.term_of_sort S);
fun typ_to_ast ctxt trf T = ast_of_termT ctxt trf (TypeExt.term_of_typ (! show_sorts) T);



(** term_to_ast **)

fun mark_freevars ((t as Const (c, _)) $ u) =
      if member (op =) SynExt.standard_token_markers c then (t $ u)
      else t $ mark_freevars u
  | mark_freevars (t $ u) = mark_freevars t $ mark_freevars u
  | mark_freevars (Abs (x, T, t)) = Abs (x, T, mark_freevars t)
  | mark_freevars (t as Free _) = Lexicon.const "_free" $ t
  | mark_freevars (t as Var (xi, T)) =
      if xi = SynExt.dddot_indexname then Const ("_DDDOT", T)
      else Lexicon.const "_var" $ t
  | mark_freevars a = a;

fun ast_of_term ctxt trf show_all_types no_freeTs show_types show_sorts tm =
  let
    fun prune_typs (t_seen as (Const _, _)) = t_seen
      | prune_typs (t as Free (x, ty), seen) =
          if ty = dummyT then (t, seen)
          else if no_freeTs orelse member (op aconv) seen t then (Lexicon.free x, seen)
          else (t, t :: seen)
      | prune_typs (t as Var (xi, ty), seen) =
          if ty = dummyT then (t, seen)
          else if no_freeTs orelse member (op aconv) seen t then (Lexicon.var xi, seen)
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
      | ((c as Const ("_var", _)), Var (xi, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.var xi) T) (map ast_of ts)
      | ((c as Const ("_bound", _)), Free (x, T) :: ts) =>
          Ast.mk_appl (constrain (c $ Lexicon.free x) T) (map ast_of ts)
      | (Const ("_idtdummy", T), ts) =>
          Ast.mk_appl (constrain (Lexicon.const "_idtdummy") T) (map ast_of ts)
      | (c' as Const (c, T), ts) =>
          if show_all_types
          then Ast.mk_appl (constrain c' T) (map ast_of ts)
          else trans c T ts
      | (t, ts) => Ast.mk_appl (simple_ast_of t) (map ast_of ts))

    and trans a T args =
      ast_of (apply_trans ctxt (apply_typed show_sorts T (trf a)) args)
        handle Match => Ast.mk_appl (Ast.Constant a) (map ast_of args)

    and constrain t T =
      if show_types andalso T <> dummyT then
        Ast.Appl [Ast.Constant SynExt.constrainC, simple_ast_of t,
          ast_of_termT ctxt trf (TypeExt.term_of_typ show_sorts T)]
      else simple_ast_of t
  in
    tm
    |> SynTrans.prop_tr'
    |> (if show_types then #1 o prune_typs o rpair [] else I)
    |> mark_freevars
    |> ast_of
  end;

fun term_to_ast ctxt trf tm =
  ast_of_term ctxt trf (! show_all_types) (! show_no_free_types)
    (! show_types orelse ! show_sorts orelse ! show_all_types) (! show_sorts) tm;



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

fun xprod_to_fmt (SynExt.XProd (_, _, "", _)) = NONE
  | xprod_to_fmt (SynExt.XProd (_, xsymbs, const, pri)) =
      let
        fun arg (s, p) =
          (if s = "type" then TypArg else Arg)
          (if Lexicon.is_terminal s then SynExt.max_pri else p);

        fun xsyms_to_syms (SynExt.Delim s :: xsyms) =
              apfst (cons (String s)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (SynExt.Argument s_p :: xsyms) =
              apfst (cons (arg s_p)) (xsyms_to_syms xsyms)
          | xsyms_to_syms (SynExt.Space s :: xsyms) =
              apfst (cons (Space s)) (xsyms_to_syms xsyms)
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
          | nargs (Space _ :: syms) = nargs syms
          | nargs (Break _ :: syms) = nargs syms
          | nargs (Block (_, bsyms) :: syms) = nargs syms + nargs bsyms
          | nargs [] = 0;
      in
        (case xsyms_to_syms xsymbs of
          (symbs, []) => SOME (const, (symbs, nargs symbs, pri))
        | _ => sys_error "xprod_to_fmt: unbalanced blocks")
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
    val fmts = map_filter (fn xprod as SynExt.XProd (_, _, c, _) =>
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

fun pretty extern_const ctxt tabs trf tokentrf type_mode curried ast0 p0 =
  let
    fun token_trans a x =
      (case tokentrf a of
        NONE =>
          if member (op =) SynExt.standard_token_classes a
          then SOME (Pretty.str x) else NONE
      | SOME f => SOME (f ctxt x));

    (*default applications: prefix / postfix*)
    val appT =
      if type_mode then TypeExt.tappl_ast_tr'
      else if curried then SynTrans.applC_ast_tr'
      else SynTrans.appl_ast_tr';

    fun synT _ ([], args) = ([], args)
      | synT markup (Arg p :: symbs, t :: args) =
          let val (Ts, args') = synT markup (symbs, args);
          in (astT (t, p) @ Ts, args') end
      | synT markup (TypArg p :: symbs, t :: args) =
          let
            val (Ts, args') = synT markup (symbs, args);
          in
            if type_mode then (astT (t, p) @ Ts, args')
            else (pretty I ctxt tabs trf tokentrf true curried t p @ Ts, args')
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
      | synT _ (_ :: _, []) = sys_error "synT"

    and parT markup (pr, args, p, p': int) = #1 (synT markup
          (if p > p' orelse
            (! show_brackets andalso p' <> SynExt.max_pri andalso not (is_chain pr))
            then [Block (1, Space "(" :: pr @ [Space ")"])]
            else pr, args))

    and atomT a =
      (case try (unprefix Lexicon.constN) a of
        SOME c => Pretty.mark (Markup.const c) (Pretty.str (extern_const c))
      | NONE =>
          (case try (unprefix Lexicon.fixedN) a of
            SOME x => the (token_trans "_free" x)
          | NONE => Pretty.str a))

    and prefixT (_, a, [], _) = [atomT a]
      | prefixT (c, _, args, p) = astT (appT (c, args), p)

    and splitT 0 ([x], ys) = (x, ys)
      | splitT 0 (rev_xs, ys) = (Ast.Appl (rev rev_xs), ys)
      | splitT n (rev_xs, y :: ys) = splitT (n - 1) (y :: rev_xs, ys)
      | splitT _ _ = sys_error "splitT"

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;
        val markup = Pretty.mark
          (Markup.const (unprefix Lexicon.constN a) handle Fail _ =>
            (Markup.fixed (unprefix Lexicon.fixedN a)))
          handle Fail _ => I;

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

fun pretty_term_ast extern_const ctxt curried prtabs trf tokentrf ast =
  pretty extern_const ctxt (mode_tabs prtabs (print_mode_value ()))
    trf tokentrf false curried ast 0;


(* pretty_typ_ast *)

fun pretty_typ_ast ctxt _ prtabs trf tokentrf ast =
  pretty I ctxt (mode_tabs prtabs (print_mode_value ()))
    trf tokentrf true false ast 0;

end;
