(*  Title:      Pure/Syntax/printer
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

signature PRINTER0 =
sig
  val show_types: bool ref
  val show_sorts: bool ref
end;

signature PRINTER =
sig
  include PRINTER0
  structure Symtab: SYMTAB
  structure XGram: XGRAM
  structure Pretty: PRETTY
  local open XGram XGram.Ast in
    val pretty_ast: ast -> Pretty.T
    val pretty_rule: (ast * ast) -> Pretty.T
    val term_to_ast: (string -> (term list -> term) option) -> term -> ast
    val typ_to_ast: (string -> (term list -> term) option) -> typ -> ast
    type tab
    val mk_print_tab: (string prod list) -> (ast list -> ast) Symtab.table -> tab
    val pretty_term_ast: tab -> ast -> Pretty.T
    val pretty_typ_ast: tab -> ast -> Pretty.T
  end
end;

functor PrinterFun(structure Symtab: SYMTAB and Lexicon: LEXICON
  and TypeExt: TYPE_EXT and SExtension: SEXTENSION and Pretty: PRETTY
  sharing TypeExt.Extension = SExtension.Extension) (*: PRINTER *) =  (* FIXME *)
struct

structure Symtab = Symtab;
structure Extension = TypeExt.Extension;
structure XGram = Extension.XGram;
structure Pretty = Pretty;
open XGram XGram.Ast Lexicon TypeExt Extension SExtension;


(** options for printing **)

val show_types = ref false;
val show_sorts = ref false;



(** simple prettying **)

(* pretty_ast *)

fun pretty_ast (Constant a) = Pretty.str (quote a)
  | pretty_ast (Variable x) = Pretty.str x
  | pretty_ast (Appl asts) =
      Pretty.blk
        (2, (Pretty.str "(") ::
          (separate (Pretty.brk 1) (map pretty_ast asts)) @ [Pretty.str ")"]);


(* pretty_rule *)

fun pretty_rule (lhs, rhs) =
  Pretty.blk
    (2, [pretty_ast lhs, Pretty.str "  ->", Pretty.brk 2, pretty_ast rhs]);



(** convert term/typ to ast **)   (* FIXME check *)

fun apply_trans a f args =
  ((f args) handle
    Match => raise Match
  | exn => (writeln ("Error in translation for " ^ quote a); raise exn));


fun ast_of_term trf show_types show_sorts tm =
  let
    val aprop_const = Const (apropC, dummyT);

    fun fix_aprop (tm as Const _) = tm
      | fix_aprop (tm as Free (x, ty)) =
          if ty = propT then aprop_const $ Free (x, dummyT) else tm
      | fix_aprop (tm as Var (xi, ty)) =
          if ty = propT then aprop_const $ Var (xi, dummyT) else tm
      | fix_aprop (tm as Bound _) = tm
      | fix_aprop (Abs (x, ty, t)) = Abs (x, ty, fix_aprop t)
      | fix_aprop (t1 $ t2) = fix_aprop t1 $ fix_aprop t2;


    fun prune_typs (t_seen as (Const _, _)) = t_seen
      | prune_typs (t as Free (x, ty), seen) =
          if ty = dummyT then (t, seen)
          else if t mem seen then (Free (x, dummyT), seen)
          else (t, t :: seen)
      | prune_typs (t as Var (xi, ty), seen) =
          if ty = dummyT then (t, seen)
          else if t mem seen then (Var (xi, dummyT), seen)
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
      | ast_of (Free (x, ty)) = constrain x (Free (x, dummyT)) ty
      | ast_of (Var (xi, ty)) = constrain (string_of_vname xi) (Var (xi, dummyT)) ty
      | ast_of (Bound i) = Variable ("B." ^ string_of_int i)
      | ast_of (t as Abs _) = ast_of (abs_tr' t)
      | ast_of (t as _ $ _) =
          (case strip_comb t of
            (Const (a, _), args) => trans a args
          | (f, args) => Appl (map ast_of (f :: args)))

    and trans a args =
      (case trf a of
        Some f => ast_of (apply_trans a f args)
      | None => raise Match)
          handle Match => mk_appl (Constant a) (map ast_of args)

    and constrain x t ty =
      if show_types andalso ty <> dummyT then
        ast_of (Const (constrainC, dummyT) $ t $ term_of_typ show_sorts ty)
      else Variable x;
  in
    if show_types then ast_of (fst (prune_typs (fix_aprop tm, [])))
    else ast_of (fix_aprop tm)
  end;


(* term_to_ast *)

fun term_to_ast trf tm =
  ast_of_term trf (! show_types) (! show_sorts) tm;


(* typ_to_ast *)

fun typ_to_ast trf ty =
  ast_of_term trf false false (term_of_typ (! show_sorts) ty);



(** type tab **)

datatype symb =
  Arg of int |
  TypArg of int |
  String of string |
  Break of int |
  Block of int * symb list;

datatype format =
  Prnt of symb list * int * int |
  Trns of ast list -> ast |
  TorP of (ast list -> ast) * (symb list * int * int);

type tab = format Symtab.table;



(** mk_print_tab **)

fun mk_print_tab prods ast_trans =
  let
    fun nargs (Arg _ :: symbs) = nargs symbs + 1
      | nargs (TypArg _ :: symbs) = nargs symbs + 1
      | nargs (String _ :: symbs) = nargs symbs
      | nargs (Break _ :: symbs) = nargs symbs
      | nargs (Block (_, bsymbs) :: symbs) = nargs symbs + nargs bsymbs
      | nargs [] = 0;

    fun merge (s, String s' :: l) = String (s ^ s') :: l
      | merge (s, l) = String s :: l;

    fun mk_prnp sy opn p =
      let
        val constr = (opn = constrainC orelse opn = constrainIdtC);

        fun syn2pr (Terminal s :: sy) =
              let val (symbs, sy') = syn2pr sy
              in (merge (s, symbs), sy') end
          | syn2pr (Space s :: sy) =
              let val (symbs, sy') = syn2pr sy
              in (merge (s, symbs), sy') end
          | syn2pr (Nonterminal (s, p) :: sy) =
              let
                val (symbs, sy') = syn2pr sy;
                val symb =
                  (if constr andalso s = "type" then TypArg else Arg)
                    (if is_terminal s then 0 else p);
              in (symb :: symbs, sy') end
          | syn2pr (Bg i :: sy) =
              let
                val (bsymbs, sy') = syn2pr sy;
                val (symbs, sy'') = syn2pr sy';
              in (Block (i, bsymbs) :: symbs, sy'') end
          | syn2pr (Brk i :: sy) =
              let val (symbs, sy') = syn2pr sy
              in (Break i :: symbs, sy') end
          | syn2pr (En :: sy) = ([], sy)
          | syn2pr [] = ([], []);

        val (pr, _) = syn2pr sy;
      in
        (pr, nargs pr, p)
      end;

    fun add_prod (Prod (_, _, "", _), tab) = tab
      | add_prod (Prod (_, sy, opn, p), tab) =
          (case Symtab.lookup (tab, opn) of
            None => Symtab.update ((opn, Prnt (mk_prnp sy opn p)), tab)
          | Some (Prnt _) => tab
          | Some (Trns f) => Symtab.update ((opn, TorP (f, mk_prnp sy opn p)), tab)
          | Some (TorP _) => tab);

    fun add_tr (tab, (opn, f)) = Symtab.update_new ((opn, Trns f), tab);
  in
    Symtab.balance
      (foldr add_prod
        (prods, foldl add_tr (Symtab.null, Symtab.alist_of ast_trans)))
  end;



(** pretty term/typ asts **)  (* FIXME check *)

(*assumes a syntax derived from Pure*)

fun pretty tab appT ast0 p0 =
  let
    fun synT ([], args) = ([], args)
      | synT (Arg p :: symbs, t :: args) =
          let val (Ts, args') = synT (symbs, args)
          in (astT (t, p) @ Ts, args') end
      | synT (TypArg p :: symbs, t :: args) =
          let val (Ts, args') = synT (symbs, args)
          in (pretty tab tappl_ast_tr' t p @ Ts, args') end
      | synT (String s :: symbs, args) =
          let val (Ts, args') = synT (symbs, args)
          in (Pretty.str s :: Ts, args') end
      | synT (Block (i, bsymbs) :: symbs, args) =
          let
            val (bTs, args') = synT (bsymbs, args);
            val (Ts, args'') = synT (symbs, args');
          in (Pretty.blk (i, bTs) :: Ts, args'') end
      | synT (Break i :: symbs, args) =
          let val (Ts, args') = synT (symbs, args)
          in (Pretty.brk i :: Ts, args') end
      | synT (_ :: _, []) = error "synT"

    and parT (pr, args, p, p': int) =
      if p > p' then fst (synT ([Block(1, String"(" :: pr @ [String")"])], args))
      else fst (synT (pr, args))

    and prefixT (_, a, [], _) = [Pretty.str a]
      | prefixT (c, _, args, p) = astT (appT (c, args), p)

    and combT (tup as (c, a, args, p)) =
      let
        val nargs = length args;
        fun prnt (pr, n, p') =
          if n = nargs then parT (pr, args, p, p')
          else if n > nargs then prefixT tup
          else astT (appT (c, args), p);     (* FIXME ??? *)
      in
        case Symtab.lookup (tab, a) of
          None => prefixT tup
        | Some (Prnt prnp) => prnt prnp
        | Some (Trns f) =>
            (astT (apply_trans a f args, p) handle Match => prefixT tup)
        | Some (TorP (f, prnp)) =>
            (astT (apply_trans a f args, p) handle Match => prnt prnp)
      end

    and astT (c as Constant a, p) = combT (c, a, [], p)
      | astT (Variable x, _) = [Pretty.str x]
      | astT (Appl ((c as Constant a) :: args), p) = combT (c, a, args, p)
      | astT (Appl (f :: (args as _ :: _)), p) = astT (appT (f, args), p)
      | astT (ast as (Appl _), _) = raise_ast "pretty: malformed ast" [ast];
  in
    astT (ast0, p0)
  end;


(* pretty_term_ast *)

fun pretty_term_ast tab ast =
  Pretty.blk (0, pretty tab appl_ast_tr' ast 0);


(* pretty_typ_ast *)

fun pretty_typ_ast tab ast =
  Pretty.blk (0, pretty tab tappl_ast_tr' ast 0);


end;

