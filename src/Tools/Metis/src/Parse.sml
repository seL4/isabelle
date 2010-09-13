(* ========================================================================= *)
(* PARSING                                                                   *)
(* Copyright (c) 2001 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

structure Parse :> Parse =
struct

open Useful;

infixr 9 >>++
infixr 8 ++
infixr 7 >>
infixr 6 ||

(* ------------------------------------------------------------------------- *)
(* A "cannot parse" exception.                                               *)
(* ------------------------------------------------------------------------- *)

exception NoParse;

(* ------------------------------------------------------------------------- *)
(* Recursive descent parsing combinators.                                    *)
(* ------------------------------------------------------------------------- *)

val error : 'a -> 'b * 'a = fn _ => raise NoParse;

fun op ++ (parser1,parser2) input =
    let
      val (result1,input) = parser1 input
      val (result2,input) = parser2 input
    in
      ((result1,result2),input)
    end;

fun op >> (parser : 'a -> 'b * 'a, treatment) input =
    let
      val (result,input) = parser input
    in
      (treatment result, input)
    end;

fun op >>++ (parser,treatment) input =
    let
      val (result,input) = parser input
    in
      treatment result input
    end;

fun op || (parser1,parser2) input =
    parser1 input handle NoParse => parser2 input;

fun first [] _ = raise NoParse
  | first (parser :: parsers) input = (parser || first parsers) input;

fun mmany parser state input =
    let
      val (state,input) = parser state input
    in
      mmany parser state input
    end
    handle NoParse => (state,input);

fun many parser =
    let
      fun sparser l = parser >> (fn x => x :: l)
    in
      mmany sparser [] >> rev
    end;

fun atLeastOne p = (p ++ many p) >> op::;

fun nothing input = ((),input);

fun optional p = (p >> SOME) || (nothing >> K NONE);

(* ------------------------------------------------------------------------- *)
(* Stream-based parsers.                                                     *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) parser = 'a Stream.stream -> 'b * 'a Stream.stream

fun maybe p Stream.Nil = raise NoParse
  | maybe p (Stream.Cons (h,t)) =
    case p h of SOME r => (r, t ()) | NONE => raise NoParse;

fun finished Stream.Nil = ((), Stream.Nil)
  | finished (Stream.Cons _) = raise NoParse;

fun some p = maybe (fn x => if p x then SOME x else NONE);

fun any input = some (K true) input;

(* ------------------------------------------------------------------------- *)
(* Parsing whole streams.                                                    *)
(* ------------------------------------------------------------------------- *)

fun fromStream parser input =
    let
      val (res,_) = (parser ++ finished >> fst) input
    in
      res
    end;

fun fromList parser l = fromStream parser (Stream.fromList l);

fun everything parser =
    let
      fun parserOption input =
          SOME (parser input)
          handle e as NoParse => if Stream.null input then NONE else raise e

      fun parserList input =
          case parserOption input of
            NONE => Stream.Nil
          | SOME (result,input) =>
            Stream.append (Stream.fromList result) (fn () => parserList input)
    in
      parserList
    end;

(* ------------------------------------------------------------------------- *)
(* Parsing lines of text.                                                    *)
(* ------------------------------------------------------------------------- *)

fun initialize {lines} =
    let
      val lastLine = ref (~1,"","","")

      val chars =
          let
            fun saveLast line =
                let
                  val ref (n,_,l2,l3) = lastLine
                  val () = lastLine := (n + 1, l2, l3, line)
                in
                  explode line
                end
          in
            Stream.memoize (Stream.map saveLast lines)
          end

      fun parseErrorLocation () =
          let
            val ref (n,l1,l2,l3) = lastLine
          in
            (if n <= 0 then "at start"
             else "around line " ^ Int.toString n) ^
            chomp (":\n" ^ l1 ^ l2 ^ l3)
          end
    in
      {chars = chars,
       parseErrorLocation = parseErrorLocation}
    end;

fun exactChar (c : char) = some (equal c) >> K ();

fun exactCharList cs =
    case cs of
      [] => nothing
    | c :: cs => (exactChar c ++ exactCharList cs) >> snd;

fun exactString s = exactCharList (explode s);

fun escapeString {escape} =
    let
      fun isEscape c = mem c escape

      fun isNormal c =
          case c of
            #"\\" => false
          | #"\n" => false
          | #"\t" => false
          | _ => not (isEscape c)

      val escapeParser =
          (exactChar #"\\" >> K #"\\") ||
          (exactChar #"n" >> K #"\n") ||
          (exactChar #"t" >> K #"\t") ||
          some isEscape

      val charParser =
          ((exactChar #"\\" ++ escapeParser) >> snd) ||
          some isNormal
    in
      many charParser >> implode
    end;

local
  val isSpace = Char.isSpace;

  val space = some isSpace;
in
  val manySpace = many space >> K ();

  val atLeastOneSpace = atLeastOne space >> K ();
end;

fun fromString parser s = fromList parser (explode s);

(* ------------------------------------------------------------------------- *)
(* Infix operators.                                                          *)
(* ------------------------------------------------------------------------- *)

fun parseGenInfix update sof toks parse inp =
    let
      val (e,rest) = parse inp

      val continue =
          case rest of
            Stream.Nil => NONE
          | Stream.Cons (h_t as (h,_)) =>
            if StringSet.member h toks then SOME h_t else NONE
    in
      case continue of
        NONE => (sof e, rest)
      | SOME (h,t) => parseGenInfix update (update sof h e) toks parse (t ())
    end;

local
  fun add ({leftSpaces = _, token = t, rightSpaces = _}, s) = StringSet.add s t;

  fun parse leftAssoc toks con =
      let
        val update =
            if leftAssoc then (fn f => fn t => fn a => fn b => con (t, f a, b))
            else (fn f => fn t => fn a => fn b => f (con (t, a, b)))
      in
        parseGenInfix update I toks
      end;
in
  fun parseLayeredInfixes {tokens,leftAssoc} =
      let
        val toks = List.foldl add StringSet.empty tokens
      in
        parse leftAssoc toks
      end;
end;

fun parseInfixes ops =
    let
      val layeredOps = Print.layerInfixes ops

      val iparsers = List.map parseLayeredInfixes layeredOps
    in
      fn con => fn subparser => foldl (fn (p,sp) => p con sp) subparser iparsers
    end;

(* ------------------------------------------------------------------------- *)
(* Quotations.                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a quotation = 'a frag list;

fun parseQuotation printer parser quote =
  let
    fun expand (QUOTE q, s) = s ^ q
      | expand (ANTIQUOTE a, s) = s ^ printer a

    val string = foldl expand "" quote
  in
    parser string
  end;

end
