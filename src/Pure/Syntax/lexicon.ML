(*  Title:      Lexicon
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1993  TU Muenchen

The Isabelle Lexer

Changes:
TODO:
  Lexicon -> lexicon, Token -> token
  end_token -> EndToken ?
*)

signature LEXICON0 =
sig
  val is_identifier: string -> bool
  val scan_varname: string list -> indexname * string list
  val string_of_vname: indexname -> string
end;

signature LEXICON =
sig
  type Lexicon
  datatype Token = Token of string
                 | IdentSy of string
                 | VarSy of string * int
                 | TFreeSy of string
                 | TVarSy of string * int
                 | end_token;
  val empty: Lexicon
  val extend: Lexicon * string list -> Lexicon
  val matching_tokens: Token * Token -> bool
  val mk_lexicon: string list -> Lexicon
  val name_of_token: Token -> string
  val predef_term: string -> Token
  val is_terminal: string -> bool
  val tokenize: Lexicon -> string -> Token list
  val token_to_string: Token -> string
  val valued_token: Token -> bool
  type 'b TokenMap
  val mkTokenMap: ('b * Token list) list -> 'b TokenMap
  val applyTokenMap: 'b TokenMap * Token -> 'b list
  include LEXICON0
end;

functor LexiconFun(Extension: EXTENSION): LEXICON =
struct

open Extension;


datatype Token = Token of string
               | IdentSy of string
               | VarSy of string * int
               | TFreeSy of string
               | TVarSy of string * int
               | end_token;
val no_token = "";

datatype dfa = Tip | Branch of string * string * dfa * dfa * dfa;

type Lexicon = dfa;

fun is_id(c::cs) = is_letter(c) andalso forall is_letdig cs
  | is_id([])    = false;

fun is_identifier s = is_id(explode s);

val empty = Tip;

fun extend1(dfa, s) =
    let fun add(Branch(c, a, less, eq, gr), cs as (d::ds)) =
              if c>d then Branch(c, a, add(less, cs), eq, gr) else
              if c<d then Branch(c, a, less, eq, add(gr, cs)) else
              Branch(c, if null ds then s else a, less, add(eq, ds), gr)
          | add(Tip, c::cs) =
              Branch(c, if null cs then s else no_token, Tip, add(Tip, cs), Tip)
          | add(dfa, []) = dfa

    in add(dfa, explode s) end;

val extend = foldl extend1;

fun mk_lexicon ss = extend(empty, ss);

fun next_dfa (Tip, _) = None
  | next_dfa (Branch(d, a, less, eq, gr), c) =
      if c<d then next_dfa(less, c) else
      if c>d then next_dfa(gr, c)   else Some(a, eq);

exception ID of string * string list;

val eof_id = "End of input - identifier expected.\n";

(*A string of letters, digits, or ' _ *)
fun xscan_ident exn =
let fun scan []  =  raise exn(eof_id, [])
      | scan(c::cs) =
        if  is_letter c
        then let val (ds, tail) = take_prefix is_letdig cs
             in  (implode(c::ds), tail)  end
        else raise exn("Identifier expected: ", c::cs)
in scan end;

(*Scan the offset of a Var, if present; otherwise ~1 *)
fun scan_offset cs = case cs of
    ("."::[]) => (~1, cs)
  | ("."::(ds as c::cs')) => if is_digit c then scan_int ds else (~1, cs)
  | _ => (~1, cs);

fun split_varname s =
    let val (rpost, rpref) = take_prefix is_digit (rev(explode s))
        val (i, _) = scan_int(rev rpost)
    in (implode(rev rpref), i) end;

fun xscan_varname exn cs : (string*int) * string list =
let val (a, ds) = xscan_ident exn cs;
    val (i, es) = scan_offset ds
in if i = ~1 then (split_varname a, es) else ((a, i), es) end;

fun scan_varname s = xscan_varname ID s
        handle ID(err, cs) => error(err^(implode cs));

fun tokenize (dfa) (s:string) : Token list =
let exception LEX_ERR;
    exception FAIL of string * string list;
    val lexerr = "Lexical error: ";

    fun tokenize1 (_:dfa, []:string list) : Token * string list =
          raise LEX_ERR
      | tokenize1(dfa, c::cs) =
          case next_dfa(dfa, c) of
            None => raise LEX_ERR
          | Some(a, dfa') =>
             if a=no_token then tokenize1(dfa', cs)
             else (tokenize1(dfa', cs) handle LEX_ERR =>
                   if is_identifier a andalso not(null cs) andalso
                      is_letdig(hd cs)
                   then raise LEX_ERR else (Token(a), cs));

    fun token(cs) = tokenize1(dfa, cs) handle LEX_ERR => raise FAIL(lexerr, cs);

    fun id([]) = raise FAIL(eof_id, [])
      | id(cs as c::cs') =
        if is_letter(c)
        then let val (id, cs'') = xscan_ident FAIL cs
             in (IdentSy(id), cs'') end
        else
        if c = "?"
        then case cs' of
                "'"::xs => let val ((a, i), ys) = xscan_varname FAIL xs
                           in (TVarSy("'"^a, i), ys) end
             | _ => let val ((a, i), ys) = xscan_varname FAIL cs'
                    in (VarSy(a, i), ys) end
        else
        if c = "'"
        then let val (a, cs'') = xscan_ident FAIL cs'
             in (TFreeSy("'" ^ a), cs'') end
        else raise FAIL(lexerr, cs);

    fun tknize([], ts) = rev(ts)
      | tknize(cs as c::cs', ts) =
        if is_blank(c) then tknize(cs', ts) else
        let val (t, cs'') =
                if c="?" then id(cs) handle FAIL _ => token(cs)
                else (token(cs) handle FAIL _ => id(cs))
        in tknize(cs'', t::ts) end

in tknize(explode s, []) handle FAIL(s, cs) => error(s^(implode cs)) end;

(*Variables have the form ?nameidx, or ?name.idx if "name" ends with a digit*)
fun string_of_vname (a, idx) = case rev(explode a) of
        []   => "?NULL_VARIABLE_NAME"
      | c::_ => "?" ^
                (if is_digit c then a ^ "." ^ string_of_int idx
                 else if idx = 0 then a
                 else a ^ string_of_int idx);

fun token_to_string (Token(s)) = s
  | token_to_string (IdentSy(s)) = s
  | token_to_string (VarSy v) = string_of_vname v
  | token_to_string (TFreeSy a) = a
  | token_to_string (TVarSy v) = string_of_vname v
  | token_to_string end_token = "\n";

(* MMW *)
fun name_of_token (Token s) = quote s
  | name_of_token (IdentSy _) = id
  | name_of_token (VarSy _) = var
  | name_of_token (TFreeSy _) = tfree
  | name_of_token (TVarSy _) = tvar;

fun matching_tokens(Token(i), Token(j)) = (i=j) |
    matching_tokens(IdentSy(_), IdentSy(_)) = true |
    matching_tokens(VarSy _, VarSy _) = true |
    matching_tokens(TFreeSy _, TFreeSy _) = true |
    matching_tokens(TVarSy _, TVarSy _) = true |
    matching_tokens(end_token, end_token) = true |
    matching_tokens(_, _) = false;

fun valued_token(end_token) = false
  | valued_token(Token _) = false
  | valued_token(IdentSy _) = true
  | valued_token(VarSy _) = true
  | valued_token(TFreeSy _) = true
  | valued_token(TVarSy _) = true;

(* MMW *)
fun predef_term name =
  if name = id then IdentSy name
  else if name = var then VarSy (name, 0)
  else if name = tfree then TFreeSy name
  else if name = tvar then TVarSy (name, 0)
  else end_token;

(* MMW *)
fun is_terminal s = s mem [id, var, tfree, tvar];



type 'b TokenMap = (Token * 'b list) list * 'b list;
val first_token = 0;

fun int_of_token(Token(tk)) = first_token |
    int_of_token(IdentSy _) = first_token - 1 |
    int_of_token(VarSy _) = first_token - 2 |
    int_of_token(TFreeSy _) = first_token - 3 |
    int_of_token(TVarSy _) = first_token - 4 |
    int_of_token(end_token) = first_token - 5;

fun lesstk(s, t) = int_of_token(s) < int_of_token(t) orelse
                  (case (s, t) of (Token(a), Token(b)) => a<b | _ => false);

fun mkTokenMap(atll) =
    let val aill = atll;
        val dom = sort lesstk (distinct(flat(map snd aill)));
        val mt = map fst (filter (null o snd) atll);
        fun mktm(i) =
            let fun add(l, (a, il)) = if i mem il then a::l else l
            in (i, foldl add ([], aill)) end;
    in (map mktm dom, mt) end;

fun find_al (i) =
    let fun find((j, al)::l) = if lesstk(i, j) then [] else
                              if matching_tokens(i, j) then al else find l |
            find [] = [];
    in find end;
fun applyTokenMap((l, mt), tk:Token) = mt@(find_al tk l);


end;

