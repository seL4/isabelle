(*  Title:      Pure/Syntax/ast
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Abstract Syntax Trees, Syntax Rules and translation, matching, normalization
of asts.
*)

signature AST =
sig
  datatype ast =
    Constant of string |
    Variable of string |
    Appl of ast list
  val mk_appl: ast -> ast list -> ast
  exception AST of string * ast list
  val raise_ast: string -> ast list -> 'a
  val str_of_ast: ast -> string
  val head_of_rule: ast * ast -> string
  val rule_error: ast * ast -> string option
  val fold_ast: string -> ast list -> ast
  val fold_ast_p: string -> ast list * ast -> ast
  val unfold_ast: string -> ast -> ast list
  val unfold_ast_p: string -> ast -> ast list * ast
  val trace_norm: bool ref
  val stat_norm: bool ref
  val normalize: (string -> (ast * ast) list) option -> ast -> ast
end;

functor AstFun()(*: AST *) =  (* FIXME *)
struct


(** Abstract Syntax Trees **)

(*asts come in two flavours:
   - proper asts representing terms and types: Variables are treated like
     Constants;
   - patterns used as lhs and rhs in rules: Variables are placeholders for
     proper asts*)

datatype ast =
  Constant of string |    (* "not", "_%", "fun" *)
  Variable of string |    (* x, ?x, 'a, ?'a *)
  Appl of ast list;       (* (f x y z), ("fun" 'a 'b) *)


(*the list of subasts of an Appl node has to contain at least 2 elements, i.e.
  there are no empty asts or nullary applications; use mk_appl for convenience*)

fun mk_appl ast [] = ast
  | mk_appl ast asts = Appl (ast :: asts);


(*exception for system errors involving asts*)

exception AST of string * ast list;

fun raise_ast msg asts = raise (AST (msg, asts));


(* print asts in a LISP-like style *)

fun str_of_ast (Constant a) = quote a
  | str_of_ast (Variable x) = x
  | str_of_ast (Appl asts) = "(" ^ (space_implode " " (map str_of_ast asts)) ^ ")";


(* head_of_ast, head_of_rule *)

fun head_of_ast (Constant a) = Some a
  | head_of_ast (Appl (Constant a :: _)) = Some a
  | head_of_ast _ = None;

fun head_of_rule (lhs, _) = the (head_of_ast lhs);



(** check Syntax Rules **)

(*a wellformed rule (lhs, rhs): (ast * ast) has the following properties:
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



(** translation utilities **)

(* fold asts *)

fun fold_ast _ [] = raise Match
  | fold_ast _ [y] = y
  | fold_ast c (x :: xs) = Appl [Constant c, x, fold_ast c xs];

fun fold_ast_p c = foldr (fn (x, xs) => Appl [Constant c, x, xs]);


(* unfold asts *)

fun unfold_ast c (y as Appl [Constant c', x, xs]) =
      if c = c' then x :: (unfold_ast c xs) else [y]
  | unfold_ast _ y = [y];

fun cons_fst x (xs, y) = (x :: xs, y);

fun unfold_ast_p c (y as Appl [Constant c', x, xs]) =
      if c = c' then cons_fst x (unfold_ast_p c xs)
      else ([], y)
  | unfold_ast_p _ y = ([], y);



(** normalization of asts **)

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


(* normalize *)   (* FIXME clean *)

val trace_norm = ref false;
val stat_norm = ref false;

(*the normalizer works yoyo-like: top-down, bottom-up, top-down, ...*)

fun normalize get_rules pre_ast =
  let
    val passes = ref 0;
    val lookups = ref 0;
    val failed_matches = ref 0;
    val changes = ref 0;

    val trace = ! trace_norm;

    fun inc i = i := ! i + 1;

    fun subst _ (ast as (Constant _)) = ast
      | subst env (Variable x) = Env.get (env, x)
      | subst env (Appl asts) = Appl (map (subst env) asts);

    fun try_rules ast ((lhs, rhs) :: pats) =
          (case match ast lhs of
            Some env => (inc changes; Some (subst env rhs))
          | None => (inc failed_matches; try_rules ast pats))
      | try_rules ast [] = None;

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


    val () = if trace then writeln ("pre: " ^ str_of_ast pre_ast) else ();

    val post_ast = if is_some get_rules then normal pre_ast else pre_ast;
  in
    if trace orelse ! stat_norm then
      writeln ("post: " ^ str_of_ast post_ast ^ "\nnormalize: " ^
        string_of_int (! passes) ^ " passes, " ^
        string_of_int (! lookups) ^ " lookups, " ^
        string_of_int (! changes) ^ " changes, " ^
        string_of_int (! failed_matches) ^ " matches failed")
    else ();
    post_ast
  end;


end;

