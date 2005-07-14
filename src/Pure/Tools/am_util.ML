(*  Title:      Pure/Tools/am_util.ML
    ID:         $Id$
    Author:     Steven Obua
*)

signature AM_UTIL = sig

    type naming = string -> int

    exception Parse of string
    exception Tokenize

    (* takes a naming for the constants *)
    val read_rule : naming -> string -> AbstractMachine.pattern * AbstractMachine.term

    (* takes a naming for the constants and one for the free variables *)
    val read_term : naming -> naming -> string -> AbstractMachine.term

    val term_ord : AbstractMachine.term * AbstractMachine.term -> order

end

structure AM_Util : AM_UTIL =
struct

fun term_ord (AbstractMachine.Var x, AbstractMachine.Var y) = int_ord (x,y)
  | term_ord (AbstractMachine.Const c1, AbstractMachine.Const c2) = int_ord (c1, c2)
  | term_ord (AbstractMachine.App a1, AbstractMachine.App a2) =
      prod_ord term_ord term_ord (a1, a2)
  | term_ord (AbstractMachine.Abs m1, AbstractMachine.Abs m2) = term_ord (m1, m2)
  | term_ord (AbstractMachine.Const _, _) = LESS
  | term_ord (AbstractMachine.Var _, AbstractMachine.Const _ ) = GREATER
  | term_ord (AbstractMachine.Var _, _) = LESS
  | term_ord (AbstractMachine.App _, AbstractMachine.Abs _) = LESS
  | term_ord (AbstractMachine.App _, _) = GREATER
  | term_ord (AbstractMachine.Abs _, _) = LESS

type naming = string -> int

datatype token =
  TokenConst of string | TokenLeft | TokenRight | TokenVar of string |
  TokenLambda | TokenDot | TokenNone | TokenEq

exception Tokenize;

fun tokenize s =
    let
        val s = String.explode s
        fun str c = Char.toString c
        fun app s c = s^(str c)
        fun tz TokenNone [] = []
          | tz x [] = [x]
          | tz TokenNone (c::cs) =
            if Char.isSpace c then tz TokenNone cs
            else if Char.isLower c then (tz (TokenVar (str c)) cs)
            else if Char.isAlphaNum c then (tz (TokenConst (str c)) cs)
            else if c = #"%" then (TokenLambda :: (tz TokenNone cs))
            else if c = #"." then (TokenDot :: (tz TokenNone cs))
            else if c = #"(" then (TokenLeft :: (tz TokenNone cs))
            else if c = #")" then (TokenRight :: (tz TokenNone cs))
            else if c = #"=" then (TokenEq :: (tz TokenNone cs))
            else raise Tokenize
          | tz (TokenConst s) (c::cs) =
            if Char.isAlphaNum c then (tz (TokenConst (app s c)) cs)
            else (TokenConst s)::(tz TokenNone (c::cs))
          | tz (TokenVar s) (c::cs) =
            if Char.isAlphaNum c then (tz (TokenVar (app s c)) cs)
            else (TokenVar s)::(tz TokenNone (c::cs))
          | tz _ _ = raise Tokenize
    in
        tz TokenNone s
    end

exception Parse of string;

fun cons x xs =
  if List.exists (fn y => x = y) xs then raise (Parse ("variable occurs twice: "^x))
  else (x::xs)

fun parse_pattern f pvars ((TokenConst c)::ts) =
    let
        val (pvars, ts, plist) = parse_pattern_list f pvars ts
    in
        (pvars, ts, AbstractMachine.PConst (f c, plist))
    end
  | parse_pattern _ _ _ = raise (Parse "parse_pattern: constant expected")
and parse_pattern_single f pvars ((TokenVar x)::ts) = (cons x pvars, ts, AbstractMachine.PVar)
  | parse_pattern_single f pvars ((TokenConst c)::ts) = (pvars, ts, AbstractMachine.PConst (f c, []))
  | parse_pattern_single f pvars (TokenLeft::ts) =
    let
        val (pvars, ts, p) = parse_pattern f pvars ts
    in
        case ts of
            TokenRight::ts => (pvars, ts, p)
          | _ => raise (Parse "parse_pattern_single: closing bracket expected")
    end
  | parse_pattern_single _ _ _ = raise (Parse "parse_pattern_single: got stuck")
and parse_pattern_list f pvars (TokenEq::ts) = (pvars, TokenEq::ts, [])
  | parse_pattern_list f pvars (TokenRight::ts) = (pvars, TokenRight::ts, [])
  | parse_pattern_list f pvars ts =
    let
        val (pvars, ts, p) = parse_pattern_single f pvars ts
        val (pvars, ts, ps) = parse_pattern_list f pvars ts
    in
        (pvars, ts, p::ps)
    end

fun app_terms x (t::ts) = app_terms (AbstractMachine.App (x, t)) ts
  | app_terms x [] = x

fun parse_term_single f vars ((TokenConst c)::ts) = (ts, AbstractMachine.Const (f c))
  | parse_term_single f vars ((TokenVar v)::ts) = (ts, AbstractMachine.Var (vars v))
  | parse_term_single f vars (TokenLeft::ts) =
    let
        val (ts, term) = parse_term f vars ts
    in
        case ts of
            TokenRight::ts => (ts, term)
          | _ => raise Parse ("parse_term_single: closing bracket expected")
    end
  | parse_term_single f vars (TokenLambda::(TokenVar x)::TokenDot::ts) =
    let
        val (ts, term) = parse_term f (fn s => if s=x then 0 else (vars s)+1) ts
    in
        (ts, AbstractMachine.Abs term)
    end
  | parse_term_single _ _ _ = raise Parse ("parse_term_single: got stuck")
and parse_term_list f vars [] = ([], [])
  | parse_term_list f vars (TokenRight::ts) = (TokenRight::ts, [])
  | parse_term_list f vars ts =
    let
        val (ts, term) = parse_term_single f vars ts
        val (ts, terms) = parse_term_list f vars ts
    in
        (ts, term::terms)
    end
and parse_term f vars ts =
    let
        val (ts, terms) = parse_term_list f vars ts
    in
        case terms of
            [] => raise (Parse "parse_term: no term found")
          | (t::terms) => (ts, app_terms t terms)
    end

fun read_rule f s =
    let
        val t = tokenize s
        val (v, ts, pattern) = parse_pattern f [] t
        fun vars [] (x:string) = raise (Parse "read_rule.vars: variable not found")
          | vars (v::vs) x = if v = x then 0 else (vars vs x)+1
    in
        case ts of
            TokenEq::ts =>
            let
                val (ts, term) = parse_term f (vars v) ts
            in
                case ts of
                    [] => (pattern, term)
                  | _ => raise (Parse "read_rule: still tokens left, end expected")
            end
          | _ => raise (Parse ("read_rule: = expected"))
    end

fun read_term f g s =
    let
        val t = tokenize s
        val (ts, term) = parse_term f g t
    in
        case ts of
            [] => term
          | _ => raise (Parse ("read_term: still tokens left, end expected"))
    end

end
