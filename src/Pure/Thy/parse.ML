(*  Title: 	Pure/Thy/parse
    ID:         $Id$
    Author: 	Sonia Mahjoub / Tobias Nipkow
    Copyright   1992  TU Muenchen

The parser combinators.
Adapted from Larry Paulson's ML for the Working Programmer.
*)

(*Global infix declarations for the parsing primitives*)
infix 5 -- --$$ $$--;
infix 3 >>;
infix 0 ||;


signature PARSE = 
sig

type token
val $$     : string -> 
             (token * int) list -> string * (token * int)list 
val id     : (token * int) list -> string * (token * int)list 
val nat    : (token * int) list -> string * (token * int)list 
val stg    : (token * int) list -> string * (token * int)list 
val txt    : (token * int) list -> string * (token * int)list 
val >>     : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
val ||     : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b 
val --     : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 
             'a -> ('b * 'd) * 'e
val $$--   : string * ((token * int)list -> 'b * 'c) -> 
             (token * int) list -> 'b * 'c
val --$$   : ( 'a -> 'b * (token * int)list ) * string -> 
             'a -> 'b * (token * int)list 
val !!     : ((token * int) list -> 'a * (token * int) list ) 
             -> (token * int) list -> 'a * (token * int) list 
val empty  : 'a -> 'b list * 'a
val repeat : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val repeat1: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val list_of: ((token * int)list -> 'b * (token * int)list ) -> 
             (token * int)list  -> 'b list * (token * int)list 
val list_of1: ((token * int)list -> 'b * (token * int)list ) -> 
             (token * int)list  -> 'b list * (token * int)list 
val reader : ((token * int) list -> 'a * ('b * int) list )
              -> string list -> 'a

end;



functor ParseFUN (Lex: LEXICAL): PARSE =
struct

type token = Lex.token;

datatype synerr = Line of string * string * int | EOF of string;

exception SynError of synerr;

fun synerr(Line(s1, s2, n)) =
      error("Syntax error on line " ^ (string_of_int n) ^ ": " ^ s1 ^
            " expected and " ^ s2 ^ " was found")
  | synerr(EOF(s)) = error("Syntax error on last line: " ^ s ^
                           " expected and end-of-file was found"); 

fun string_of_token (Lex.Key b) = b
  | string_of_token (Lex.Id b)  = b
  | string_of_token (Lex.Nat b) = b
  | string_of_token (Lex.Txt b) = b
  | string_of_token (Lex.Stg b) = b;

fun line_err x = raise SynError(Line x);
fun eof_err s =  raise SynError(EOF s);

fun $$a ((Lex.Key b,n) :: toks) =
           if a = b then (a,toks) else line_err(a,b,n) 
  | $$a ((t,n) :: toks) = line_err (a,string_of_token t, n)
  | $$a _ = eof_err a;


fun id ((Lex.Id b,n) :: toks) = (b, toks)
  | id ((t,n) :: toks) = line_err ("identifier", string_of_token t, n)
  | id _ = eof_err "identifier";


fun nat ((Lex.Nat b,n) :: toks) = (b, toks)
  | nat ((t,n) :: toks) = 
	line_err ("natural number", string_of_token t, n)
  | nat _ = eof_err "natural number";


fun stg ((Lex.Stg b,n) :: toks) = (b, toks)
  | stg ((t,n) :: toks) = line_err("string", string_of_token t, n)
  | stg _ = eof_err"string";


fun txt ((Lex.Txt b,n) :: toks) = (b, toks)
  | txt ((t,n) :: toks) = line_err ("ML text", string_of_token t, n)
  | txt _ = eof_err "ML text";


fun ( ph >> f) toks = let val (x, toks2) = ph toks in (f x, toks2) end;

fun (ph1 || ph2) toks = ph1 toks handle SynError _ => ph2 toks;


fun (ph1 -- ph2) toks =
    let val (x, toks2) = ph1 toks
        val (y, toks3) = ph2 toks2
    in ((x,y), toks3) end;

fun (a $$-- ph)  =  $$a -- ph >> #2;

fun (ph --$$ a)  =  ph -- $$a >> #1;

fun !! ph toks = ph toks handle SynError s => synerr s;

fun empty toks = ([], toks);

fun repeat ph toks  = (   ph -- repeat ph >> (op::)
                       || empty ) toks; 

fun repeat1 ph  =  ph -- repeat ph >> (op::);

fun list_of1 ph =  ph -- repeat("," $$-- !! ph) >> (op::);
fun list_of ph  =  list_of1 ph || empty;

fun reader ph a = 
       ( case ph (Lex.scan a) of 
                (x,  []) => x
              | (_,(_, n)::_) => error
                ("Syntax error on line " ^ (string_of_int n) ^ ": " ^
                 "Extra characters in phrase")
       );
end;
