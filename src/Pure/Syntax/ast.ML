(*  Title:      Pure/Syntax/ast.ML
    Author:     Markus Wenzel, TU Muenchen

Abstract syntax trees, translation rules, matching and normalization of asts.
*)

signature AST =
sig
  datatype ast =
    Constant of string |
    Variable of string |
    Appl of ast list
  val mk_appl: ast -> ast list -> ast
  exception AST of string * ast list
  val ast_ord: ast ord
  structure Table: TABLE
  structure Set: SET
  val pretty_var: string -> Pretty.T
  val pretty_ast: ast -> Pretty.T
  val pretty_rule: ast * ast -> Pretty.T
  val strip_positions: ast -> ast
  val rule_index: ast * ast -> string
  val rule_error: ast * ast -> string option
  val fold_ast: string -> ast list -> ast
  val fold_ast_p: string -> ast list * ast -> ast
  val unfold_ast: string -> ast -> ast list
  val unfold_ast_p: string -> ast -> ast list * ast
  val trace: bool Config.T
  val stats: bool Config.T
  val normalize: Proof.context -> (string -> (ast * ast) list) -> ast -> ast
end;

structure Ast: AST =
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


(* order *)

local

fun cons_nr (Constant _) = 0
  | cons_nr (Variable _) = 1
  | cons_nr (Appl _) = 2;

in

fun ast_ord asts =
  if pointer_eq asts then EQUAL
  else
    (case asts of
      (Constant a, Constant b) => fast_string_ord (a, b)
    | (Variable a, Variable b) => fast_string_ord (a, b)
    | (Appl a, Appl b) => list_ord ast_ord (a, b)
    | _ => int_ord (apply2 cons_nr asts));

end;

structure Table = Table(type key = ast val ord = ast_ord);
structure Set = Set(Table.Key);


(* print asts in a LISP-like style *)

fun pretty_var x =
  (case Term_Position.decode x of
    SOME pos => Term_Position.pretty pos
  | NONE => Pretty.str x);

fun pretty_ast (Constant a) = Pretty.quote (Pretty.str a)
  | pretty_ast (Variable x) = pretty_var x
  | pretty_ast (Appl asts) = Pretty.enclose "(" ")" (Pretty.breaks (map pretty_ast asts));

fun pretty_rule (lhs, rhs) =
  Pretty.block [pretty_ast lhs, Pretty.str " \<leadsto>", Pretty.brk 1, pretty_ast rhs];

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_ML o pretty_ast);


(* strip_positions *)

fun strip_positions (Appl ((t as Constant c) :: u :: (v as Variable x) :: asts)) =
      if member (op =) Term_Position.markers c andalso is_some (Term_Position.decode x)
      then mk_appl (strip_positions u) (map strip_positions asts)
      else Appl (map strip_positions (t :: u :: v :: asts))
  | strip_positions (Appl asts) = Appl (map strip_positions asts)
  | strip_positions ast = ast;


(* translation rules *)

fun rule_index (Constant a, _: ast) = a
  | rule_index (Appl (Constant a :: _), _) = a
  | rule_index _ = "";

fun rule_error (lhs, rhs) =
  let
    fun add_vars (Constant _) = I
      | add_vars (Variable x) = cons x
      | add_vars (Appl asts) = fold add_vars asts;

    val lvars = add_vars lhs [];
    val rvars = add_vars rhs [];
  in
    if has_duplicates (op =) lvars then SOME "duplicate vars in lhs"
    else if not (subset (op =) (rvars, lvars)) then SOME "rhs contains extra variables"
    else NONE
  end;


(* ast translation utilities *)

fun fold_ast _ [] = raise Match
  | fold_ast _ [y] = y
  | fold_ast c (x :: xs) = Appl [Constant c, x, fold_ast c xs];

fun fold_ast_p c = uncurry (fold_rev (fn x => fn xs => Appl [Constant c, x, xs]));


fun unfold_ast c (y as Appl [Appl [Constant "_constrain", Constant c', _], x, xs]) =
      if c = c' then x :: unfold_ast c xs else [y]
  | unfold_ast c (y as Appl [Constant c', x, xs]) =
      if c = c' then x :: unfold_ast c xs else [y]
  | unfold_ast _ y = [y];

fun unfold_ast_p c (y as Appl [Appl [Constant "_constrain", Constant c', _], x, xs]) =
      if c = c' then apfst (cons x) (unfold_ast_p c xs) else ([], y)
  | unfold_ast_p c (y as Appl [Constant c', x, xs]) =
      if c = c' then apfst (cons x) (unfold_ast_p c xs) else ([], y)
  | unfold_ast_p _ y = ([], y);



(** normalization of asts **)

(* match *)

local

exception NO_MATCH;

fun const_match (Constant a) b = a = b
  | const_match (Variable a) b = a = b
  | const_match (Appl [Constant "_constrain", ast, _]) b = const_match ast b
  | const_match _ _ = false;

fun match1 ast (Constant b) env = if const_match ast b then env else raise NO_MATCH
  | match1 ast (Variable x) env = Symtab.update (x, ast) env
  | match1 (Appl asts) (Appl pats) env = match2 asts pats env
  | match1 _ _ _ = raise NO_MATCH
and match2 (ast :: asts) (pat :: pats) env = match1 ast pat env |> match2 asts pats
  | match2 [] [] env = env
  | match2 _ _ _ = raise NO_MATCH;

in

fun match ast pat =
  let
    val (head, args) =
      (case (ast, pat) of
        (Appl asts, Appl pats) =>
          let val a = length asts and p = length pats in
            if a > p then (Appl (take p asts), drop p asts)
            else (ast, [])
          end
      | _ => (ast, []));
  in SOME (Symtab.build (match1 head pat), args) handle NO_MATCH => NONE end;

end;


(* normalize *)

val trace = Config.declare_bool ("syntax_ast_trace", \<^here>) (K false);
val stats = Config.declare_bool ("syntax_ast_stats", \<^here>) (K false);

local

fun subst _ (ast as Constant _) = ast
  | subst env (Variable x) = the (Symtab.lookup env x)
  | subst env (Appl asts) = Appl (map (subst env) asts);

fun head_name (Constant a) = SOME a
  | head_name (Variable a) = SOME a
  | head_name (Appl [Constant "_constrain", Constant a, _]) = SOME a
  | head_name (Appl (Appl [Constant "_constrain", Constant a, _] :: _)) = SOME a
  | head_name (Appl (Constant a :: _)) = SOME a
  | head_name (Appl (Variable a :: _)) = SOME a
  | head_name _ = NONE;

fun message head body =
  Pretty.string_of (Pretty.block [Pretty.str head, Pretty.brk 1, body]);

in

(*the normalizer works yoyo-like: top-down, bottom-up, top-down, ...*)
fun normalize ctxt get_rules pre_ast =
  let
    val trace = Config.get ctxt trace;
    val stats = Config.get ctxt stats;

    val passes = Unsynchronized.ref 0;
    val failed_matches = Unsynchronized.ref 0;
    val changes = Unsynchronized.ref 0;

    fun rewrite1 ((lhs, rhs) :: pats) ast =
          (case match ast lhs of
            SOME (env, args) =>
              (Unsynchronized.inc changes; SOME (mk_appl (subst env rhs) args))
          | NONE => (Unsynchronized.inc failed_matches; rewrite1 pats ast))
      | rewrite1 [] _ = NONE;

    fun rewrite2 (SOME a) ast =
          (case rewrite1 (get_rules a) ast of
            NONE => rewrite2 NONE ast
          | some => some)
      | rewrite2 NONE ast = rewrite1 (get_rules "") ast;

    fun rewrite ast = rewrite2 (head_name ast) ast;

    fun rewrote old_ast new_ast =
      if trace then tracing (message "rewrote:" (pretty_rule (old_ast, new_ast)))
      else ();

    fun norm1 ast =
      (case rewrite ast of
        SOME new_ast => (rewrote ast new_ast; norm1 new_ast)
      | NONE => ast);

    fun norm2 ast =
      (case norm1 ast of
        Appl sub_asts =>
          let
            val old_changes = ! changes;
            val new_ast = Appl (map norm2 sub_asts);
          in
            if old_changes = ! changes then new_ast else norm1 new_ast
          end
      | atomic_ast => atomic_ast);

    fun norm ast =
      let
        val old_changes = ! changes;
        val new_ast = norm2 ast;
      in
        Unsynchronized.inc passes;
        if old_changes = ! changes then new_ast else norm new_ast
      end;


    val _ = if trace then tracing (message "pre:" (pretty_ast pre_ast)) else ();
    val post_ast = norm pre_ast;
    val _ =
      if trace orelse stats then
        tracing (message "post:" (pretty_ast post_ast) ^ "\nnormalize: " ^
          string_of_int (! passes) ^ " passes, " ^
          string_of_int (! changes) ^ " changes, " ^
          string_of_int (! failed_matches) ^ " matches failed")
      else ();
  in post_ast end;

end;

end;
