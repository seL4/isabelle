(*  Title:      Pure/Syntax/ast.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Abstract syntax trees, translation rules, matching and normalization of asts.
*)

signature AST0 =
sig
  structure Pretty: PRETTY
  datatype ast =
    Constant of string |
    Variable of string |
    Appl of ast list
  val mk_appl: ast -> ast list -> ast
  exception AST of string * ast list
  val str_of_ast: ast -> string
  val pretty_ast: ast -> Pretty.T
  val pretty_rule: (ast * ast) -> Pretty.T
  val pprint_ast: ast -> pprint_args -> unit
  val trace_norm_ast: bool ref
  val stat_norm_ast: bool ref
end

signature AST =
sig
  include AST0
  val raise_ast: string -> ast list -> 'a
  val head_of_rule: ast * ast -> string
  val rule_error: ast * ast -> string option
  val fold_ast: string -> ast list -> ast
  val fold_ast_p: string -> ast list * ast -> ast
  val unfold_ast: string -> ast -> ast list
  val unfold_ast_p: string -> ast -> ast list * ast
  val normalize: bool -> bool -> (string -> (ast * ast) list) option -> ast -> ast
  val normalize_ast: (string -> (ast * ast) list) option -> ast -> ast
end;

functor AstFun(Pretty: PRETTY): AST =
struct

structure Pretty = Pretty;


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

fun raise_ast msg asts = raise AST (msg, asts);


(** print asts in a LISP-like style **)

(* str_of_ast *)

fun str_of_ast (Constant a) = quote a
  | str_of_ast (Variable x) = x
  | str_of_ast (Appl asts) = "(" ^ (space_implode " " (map str_of_ast asts)) ^ ")";


(* pretty_ast *)

fun pretty_ast (Constant a) = Pretty.str (quote a)
  | pretty_ast (Variable x) = Pretty.str x
  | pretty_ast (Appl asts) =
      Pretty.parents "(" ")" (Pretty.breaks (map pretty_ast asts));


(* pprint_ast *)

val pprint_ast = Pretty.pprint o pretty_ast;


(* pretty_rule *)

fun pretty_rule (lhs, rhs) =
  Pretty.block [pretty_ast lhs, Pretty.str "  ->", Pretty.brk 2, pretty_ast rhs];


(* head_of_ast, head_of_rule *)

fun head_of_ast (Constant a) = Some a
  | head_of_ast (Appl (Constant a :: _)) = Some a
  | head_of_ast _ = None;

fun head_of_rule (lhs, _) = the (head_of_ast lhs);



(** check translation rules **)

(*a wellformed rule (lhs, rhs): (ast * ast) obeys the following conditions:
   - the head of lhs is a constant,
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
    if is_none (head_of_ast lhs) then Some "lhs has no constant head"
    else if not (unique lvars) then Some "duplicate vars in lhs"
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

val trace_norm_ast = ref false;
val stat_norm_ast = ref false;


(* simple env *)

structure Env =
struct
  val empty = [];
  val add = op ::;
  val get = the o assoc;
end;


(* match *)

fun match ast pat =
  let
    exception NO_MATCH;

    fun mtch (Constant a, Constant b, env) =
          if a = b then env else raise NO_MATCH
      | mtch (Variable a, Constant b, env) =
          if a = b then env else raise NO_MATCH
      | mtch (ast, Variable x, env) = Env.add ((x, ast), env)
      | mtch (Appl asts, Appl pats, env) = mtch_lst (asts, pats, env)
      | mtch _ = raise NO_MATCH
    and mtch_lst (ast :: asts, pat :: pats, env) =
          mtch_lst (asts, pats, mtch (ast, pat, env))
      | mtch_lst ([], [], env) = env
      | mtch_lst _ = raise NO_MATCH;
  in
    Some (mtch (ast, pat, Env.empty)) handle NO_MATCH => None
  end;


(* normalize *)

(*the normalizer works yoyo-like: top-down, bottom-up, top-down, ...*)

fun normalize trace stat get_rules pre_ast =
  let
    val passes = ref 0;
    val lookups = ref 0;
    val failed_matches = ref 0;
    val changes = ref 0;

    fun subst _ (ast as Constant _) = ast
      | subst env (Variable x) = Env.get (env, x)
      | subst env (Appl asts) = Appl (map (subst env) asts);

    fun try_rules ast ((lhs, rhs) :: pats) =
          (case match ast lhs of
            Some env => (inc changes; Some (subst env rhs))
          | None => (inc failed_matches; try_rules ast pats))
      | try_rules _ [] = None;

    fun try ast a = (inc lookups; try_rules ast (the get_rules a));

    fun rewrite (ast as Constant a) = try ast a
      | rewrite (ast as Variable a) = try ast a
      | rewrite (ast as Appl (Constant a :: _)) = try ast a
      | rewrite (ast as Appl (Variable a :: _)) = try ast a
      | rewrite _ = None;

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

    val post_ast = if is_some get_rules then normal pre_ast else pre_ast;
  in
    if trace orelse stat then
      writeln ("post: " ^ str_of_ast post_ast ^ "\nnormalize: " ^
        string_of_int (! passes) ^ " passes, " ^
        string_of_int (! lookups) ^ " lookups, " ^
        string_of_int (! changes) ^ " changes, " ^
        string_of_int (! failed_matches) ^ " matches failed")
    else ();
    post_ast
  end;


(* normalize_ast *)

fun normalize_ast get_rules ast =
  normalize (! trace_norm_ast) (! stat_norm_ast) get_rules ast;


end;

