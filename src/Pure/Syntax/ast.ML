(*  Title:      Pure/Syntax/ast.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Abstract syntax trees, translation rules, matching and normalization of asts.
*)

signature AST0 =
  sig
  datatype ast =
    Constant of string |
    Variable of string |
    Appl of ast list
  exception AST of string * ast list
  end;

signature AST1 =
  sig
  include AST0
  val mk_appl: ast -> ast list -> ast
  val str_of_ast: ast -> string
  val pretty_ast: ast -> Pretty.T
  val pretty_rule: ast * ast -> Pretty.T
  val pprint_ast: ast -> pprint_args -> unit
  val fold_ast: string -> ast list -> ast
  val fold_ast_p: string -> ast list * ast -> ast
  val unfold_ast: string -> ast -> ast list
  val unfold_ast_p: string -> ast -> ast list * ast
  val trace_ast: bool ref
  val stat_ast: bool ref
  end;

signature AST =
  sig
  include AST1
  val head_of_rule: ast * ast -> string
  val rule_error: ast * ast -> string option
  val normalize: bool -> bool -> (string -> (ast * ast) list) -> ast -> ast
  val normalize_ast: (string -> (ast * ast) list) -> ast -> ast
  end;

structure Ast : AST =
struct

(** abstract syntax trees **)

(*asts come in two flavours:
   - ordinary asts representing terms and typs: Variables are (often) treated
     like Constants;
   - patterns used as lhs and rhs in rules: Variables are placeholders for
     proper asts*)

datatype ast =
  Constant of string |    (*"not", "_abs", "fun"*)
  Variable of string |    (*x, ?x, 'a, ?'a*)
  Appl of ast list;       (*(f x y z), ("fun" 'a 'b), ("_abs" x t)*)


(*the list of subasts of an Appl node has to contain at least 2 elements, i.e.
  there are no empty asts or nullary applications; use mk_appl for convenience*)

fun mk_appl f [] = f
  | mk_appl f args = Appl (f :: args);


(*exception for system errors involving asts*)

exception AST of string * ast list;



(** print asts in a LISP-like style **)

(* str_of_ast *)

fun str_of_ast (Constant a) = quote a
  | str_of_ast (Variable x) = x
  | str_of_ast (Appl asts) = "(" ^ (space_implode " " (map str_of_ast asts)) ^ ")";


(* pretty_ast *)

fun pretty_ast (Constant a) = Pretty.str (quote a)
  | pretty_ast (Variable x) = Pretty.str x
  | pretty_ast (Appl asts) =
      Pretty.enclose "(" ")" (Pretty.breaks (map pretty_ast asts));


(* pprint_ast *)

val pprint_ast = Pretty.pprint o pretty_ast;


(* pretty_rule *)

fun pretty_rule (lhs, rhs) =
  Pretty.block [pretty_ast lhs, Pretty.str "  ->", Pretty.brk 2, pretty_ast rhs];


(* head_of_ast, head_of_rule *)

fun head_of_ast (Constant a) = a
  | head_of_ast (Appl (Constant a :: _)) = a
  | head_of_ast _ = "";

fun head_of_rule (lhs, _) = head_of_ast lhs;



(** check translation rules **)

(*a wellformed rule (lhs, rhs): (ast * ast) obeys the following conditions:
   - the lhs has unique vars,
   - vars of rhs is subset of vars of lhs*)

fun rule_error (rule as (lhs, rhs)) =
  let
    fun vars_of (Constant _) = []
      | vars_of (Variable x) = [x]
      | vars_of (Appl asts) = flat (map vars_of asts);

    fun unique (x :: xs) = not (x mem xs) andalso unique xs
      | unique [] = true;

    val lvars = vars_of lhs;
    val rvars = vars_of rhs;
  in
    if not (unique lvars) then Some "duplicate vars in lhs"
    else if not (rvars subset lvars) then Some "rhs contains extra variables"
    else None
  end;



(** ast translation utilities **)

(* fold asts *)

fun fold_ast _ [] = raise Match
  | fold_ast _ [y] = y
  | fold_ast c (x :: xs) = Appl [Constant c, x, fold_ast c xs];

fun fold_ast_p c = foldr (fn (x, xs) => Appl [Constant c, x, xs]);


(* unfold asts *)

fun unfold_ast c (y as Appl [Constant c', x, xs]) =
      if c = c' then x :: (unfold_ast c xs) else [y]
  | unfold_ast _ y = [y];

fun unfold_ast_p c (y as Appl [Constant c', x, xs]) =
      if c = c' then apfst (cons x) (unfold_ast_p c xs)
      else ([], y)
  | unfold_ast_p _ y = ([], y);


(** normalization of asts **)

(* tracing options *)

val trace_ast = ref false;
val stat_ast = ref false;


(* match *)

fun match ast pat =
  let
    exception NO_MATCH;

    fun mtch (Constant a) (Constant b) env =
          if a = b then env else raise NO_MATCH
      | mtch (Variable a) (Constant b) env =
          if a = b then env else raise NO_MATCH
      | mtch ast (Variable x) env = Symtab.update ((x, ast), env)
      | mtch (Appl asts) (Appl pats) env = mtch_lst asts pats env
      | mtch _ _ _ = raise NO_MATCH
    and mtch_lst (ast :: asts) (pat :: pats) env =
          mtch_lst asts pats (mtch ast pat env)
      | mtch_lst [] [] env = env
      | mtch_lst _ _ _ = raise NO_MATCH;

    val (head, args) =
      (case (ast, pat) of
        (Appl asts, Appl pats) =>
          let val a = length asts and p = length pats in
            if a > p then (Appl (take (p, asts)), drop (p, asts))
            else (ast, [])
          end
      | _ => (ast, []));
  in
    Some (mtch head pat Symtab.empty, args) handle NO_MATCH => None
  end;


(* normalize *)

(*the normalizer works yoyo-like: top-down, bottom-up, top-down, ...*)

fun normalize trace stat get_rules pre_ast =
  let
    val passes = ref 0;
    val failed_matches = ref 0;
    val changes = ref 0;

    fun subst _ (ast as Constant _) = ast
      | subst env (Variable x) = the (Symtab.lookup (env, x))
      | subst env (Appl asts) = Appl (map (subst env) asts);

    fun try_rules ((lhs, rhs) :: pats) ast =
          (case match ast lhs of
            Some (env, args) =>
              (inc changes; Some (mk_appl (subst env rhs) args))
          | None => (inc failed_matches; try_rules pats ast))
      | try_rules [] _ = None;
    val try_headless_rules = try_rules (get_rules "");

    fun try ast a =
      (case try_rules (get_rules a) ast of
        None => try_headless_rules ast
      | some => some);

    fun rewrite (ast as Constant a) = try ast a
      | rewrite (ast as Variable a) = try ast a
      | rewrite (ast as Appl (Constant a :: _)) = try ast a
      | rewrite (ast as Appl (Variable a :: _)) = try ast a
      | rewrite ast = try_headless_rules ast;

    fun rewrote old_ast new_ast =
      if trace then
        writeln ("rewrote: " ^ str_of_ast old_ast ^ "  ->  " ^ str_of_ast new_ast)
      else ();

    fun norm_root ast =
      (case rewrite ast of
        Some new_ast => (rewrote ast new_ast; norm_root new_ast)
      | None => ast);

    fun norm ast =
      (case norm_root ast of
        Appl sub_asts =>
          let
            val old_changes = ! changes;
            val new_ast = Appl (map norm sub_asts);
          in
            if old_changes = ! changes then new_ast else norm_root new_ast
          end
      | atomic_ast => atomic_ast);

    fun normal ast =
      let
        val old_changes = ! changes;
        val new_ast = norm ast;
      in
        inc passes;
        if old_changes = ! changes then new_ast else normal new_ast
      end;


    val _ = if trace then writeln ("pre: " ^ str_of_ast pre_ast) else ();

    val post_ast = normal pre_ast;
  in
    if trace orelse stat then
      writeln ("post: " ^ str_of_ast post_ast ^ "\nnormalize: " ^
        string_of_int (! passes) ^ " passes, " ^
        string_of_int (! changes) ^ " changes, " ^
        string_of_int (! failed_matches) ^ " matches failed")
    else ();
    post_ast
  end;


(* normalize_ast *)

fun normalize_ast get_rules ast =
  normalize (! trace_ast) (! stat_ast) get_rules ast;

end;

