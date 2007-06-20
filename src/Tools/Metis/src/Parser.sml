(* ========================================================================= *)
(* PARSER COMBINATORS                                                        *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Parser :> Parser =
struct

infixr 9 >>++
infixr 8 ++
infixr 7 >>
infixr 6 ||

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Bug = Useful.Bug;

val trace = Useful.trace
and equal = Useful.equal
and I = Useful.I
and K = Useful.K
and C = Useful.C
and fst = Useful.fst
and snd = Useful.snd
and pair = Useful.pair
and curry = Useful.curry
and funpow = Useful.funpow
and mem = Useful.mem
and sortMap = Useful.sortMap;

(* ------------------------------------------------------------------------- *)
(* Pretty printing for built-in types                                        *)
(* ------------------------------------------------------------------------- *)

type ppstream = PP.ppstream

datatype breakStyle = Consistent | Inconsistent

type 'a pp = PP.ppstream -> 'a -> unit;

val lineLength = ref 75;

fun beginBlock pp Consistent = PP.begin_block pp PP.CONSISTENT
  | beginBlock pp Inconsistent = PP.begin_block pp PP.INCONSISTENT;

val endBlock = PP.end_block
and addString = PP.add_string
and addBreak = PP.add_break
and addNewline = PP.add_newline;

fun ppMap f ppA (ppstrm : PP.ppstream) x : unit = ppA ppstrm (f x);

fun ppBracket l r ppA pp a =
    let
      val ln = size l
    in
      beginBlock pp Inconsistent ln;
      if ln = 0 then () else addString pp l;
      ppA pp a;
      if r = "" then () else addString pp r;
      endBlock pp
    end;

fun ppSequence sep ppA pp =
    let
      fun ppX x = (addString pp sep; addBreak pp (1,0); ppA pp x)
    in
      fn [] => ()
       | h :: t =>
         (beginBlock pp Inconsistent 0;
          ppA pp h;
          app ppX t;
          endBlock pp)
    end;

fun ppBinop s ppA ppB pp (a,b) =
    (beginBlock pp Inconsistent 0;
      ppA pp a;
      if s = "" then () else addString pp s;
      addBreak pp (1,0);
      ppB pp b;
      endBlock pp);

fun ppTrinop ab bc ppA ppB ppC pp (a,b,c) =
    (beginBlock pp Inconsistent 0;
     ppA pp a;
     if ab = "" then () else addString pp ab;
     addBreak pp (1,0);
     ppB pp b;
     if bc = "" then () else addString pp bc;
     addBreak pp (1,0);
     ppC pp c;
     endBlock pp);

(* Pretty-printers for common types *)

fun ppString pp s =
    (beginBlock pp Inconsistent 0;
     addString pp s;
     endBlock pp);

val ppUnit = ppMap (fn () => "()") ppString;

val ppChar = ppMap str ppString;

val ppBool = ppMap (fn true => "true" | false => "false") ppString;

val ppInt = ppMap Int.toString ppString;

val ppReal = ppMap Real.toString ppString;

val ppOrder =
    let
      fun f LESS = "Less"
        | f EQUAL = "Equal"
        | f GREATER = "Greater"
    in
      ppMap f ppString
    end;

fun ppList ppA = ppBracket "[" "]" (ppSequence "," ppA);

fun ppOption _ pp NONE = ppString pp "-"
  | ppOption ppA pp (SOME a) = ppA pp a;

fun ppPair ppA ppB = ppBracket "(" ")" (ppBinop "," ppA ppB);

fun ppTriple ppA ppB ppC = ppBracket "(" ")" (ppTrinop "," "," ppA ppB ppC);

fun toString ppA a = PP.pp_to_string (!lineLength) ppA a;

fun fromString toS = ppMap toS ppString;

fun ppTrace ppX nameX x =
    trace (toString (ppBinop " =" ppString ppX) (nameX,x) ^ "\n");

(* ------------------------------------------------------------------------- *)
(* Generic.                                                                  *)
(* ------------------------------------------------------------------------- *)

exception NoParse;

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
(* Stream-based.                                                             *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) parser = 'a Stream.stream -> 'b * 'a Stream.stream

fun everything parser =
    let
      fun f input =
          let
            val (result,input) = parser input
          in
            Stream.append (Stream.fromList result) (fn () => f input)
          end
          handle NoParse =>
            if Stream.null input then Stream.NIL else raise NoParse
    in
      f
    end;

fun maybe p Stream.NIL = raise NoParse
  | maybe p (Stream.CONS (h,t)) =
    case p h of SOME r => (r, t ()) | NONE => raise NoParse;

fun finished Stream.NIL = ((), Stream.NIL)
  | finished (Stream.CONS _) = raise NoParse;

fun some p = maybe (fn x => if p x then SOME x else NONE);

fun any input = some (K true) input;

fun exact tok = some (fn item => item = tok);

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing for infix operators.                          *)
(* ------------------------------------------------------------------------- *)

type infixities = {token : string, precedence : int, leftAssoc : bool} list;

local
  fun unflatten ({token,precedence,leftAssoc}, ([],_)) =
      ([(leftAssoc, [token])], precedence)
    | unflatten ({token,precedence,leftAssoc}, ((a,l) :: dealt, p)) =
      if p = precedence then
        let
          val _ = leftAssoc = a orelse
                  raise Bug "infix parser/printer: mixed assocs"
        in
          ((a, token :: l) :: dealt, p)
        end
      else
        ((leftAssoc,[token]) :: (a,l) :: dealt, precedence);
in
  fun layerOps infixes =
      let
        val infixes = sortMap #precedence Int.compare infixes
        val (parsers,_) = foldl unflatten ([],0) infixes
      in
        parsers
      end;
end;

local
  fun chop (#" " :: chs) = let val (n,l) = chop chs in (n + 1, l) end
    | chop chs = (0,chs);

  fun nspaces n = funpow n (curry op^ " ") "";

  fun spacify tok =
      let
        val chs = explode tok
        val (r,chs) = chop (rev chs)
        val (l,chs) = chop (rev chs)
      in
        ((l,r), implode chs)
      end;

  fun lrspaces (l,r) =
      (if l = 0 then K () else C addString (nspaces l),
       if r = 0 then K () else C addBreak (r, 0));
in
  fun opSpaces s = let val (l_r,s) = spacify s in (lrspaces l_r, s) end;

  val opClean = snd o spacify;
end;

val infixTokens : infixities -> string list =
    List.map (fn {token,...} => opClean token);

fun parseGenInfix update sof toks parse inp =
    let
      val (e, rest) = parse inp
                      
      val continue =
          case rest of
            Stream.NIL => NONE
          | Stream.CONS (h, t) => if mem h toks then SOME (h, t) else NONE
    in
      case continue of
        NONE => (sof e, rest)
      | SOME (h,t) => parseGenInfix update (update sof h e) toks parse (t ())
    end;

fun parseLeftInfix toks con =
    parseGenInfix (fn f => fn t => fn a => fn b => con (t, f a, b)) I toks;

fun parseRightInfix toks con =
    parseGenInfix (fn f => fn t => fn a => fn b => f (con (t, a, b))) I toks;

fun parseInfixes ops =
    let
      fun layeredOp (x,y) = (x, List.map opClean y)

      val layeredOps = List.map layeredOp (layerOps ops)

      fun iparser (a,t) = (if a then parseLeftInfix else parseRightInfix) t

      val iparsers = List.map iparser layeredOps
    in
      fn con => fn subparser => foldl (fn (p,sp) => p con sp) subparser iparsers
    end;

fun ppGenInfix left toks =
    let
      val spc = List.map opSpaces toks
    in
      fn dest => fn ppSub =>
      let
        fun dest' tm =
            case dest tm of
              NONE => NONE
            | SOME (t, a, b) =>
              Option.map (pair (a,b)) (List.find (equal t o snd) spc)

        open PP

        fun ppGo pp (tmr as (tm,r)) =
            case dest' tm of
              NONE => ppSub pp tmr
            | SOME ((a,b),((lspc,rspc),tok)) =>
              ((if left then ppGo else ppSub) pp (a,true);
               lspc pp; addString pp tok; rspc pp;
               (if left then ppSub else ppGo) pp (b,r))
      in
        fn pp => fn tmr as (tm,_) =>
        case dest' tm of
          NONE => ppSub pp tmr
        | SOME _ => (beginBlock pp Inconsistent 0; ppGo pp tmr; endBlock pp)
      end
    end;

fun ppLeftInfix toks = ppGenInfix true toks;

fun ppRightInfix toks = ppGenInfix false toks;

fun ppInfixes ops =
    let
      val layeredOps = layerOps ops
                       
      val toks = List.concat (List.map (List.map opClean o snd) layeredOps)
                 
      fun iprinter (a,t) = (if a then ppLeftInfix else ppRightInfix) t
                           
      val iprinters = List.map iprinter layeredOps
    in
      fn dest => fn ppSub =>
      let
        fun printer sub = foldl (fn (ip,p) => ip dest p) sub iprinters

        fun isOp t = case dest t of SOME (x,_,_) => mem x toks | _ => false

        open PP

        fun subpr pp (tmr as (tm,_)) =
            if isOp tm then
              (beginBlock pp Inconsistent 1; addString pp "(";
               printer subpr pp (tm, false); addString pp ")"; endBlock pp)
            else ppSub pp tmr
      in
        fn pp => fn tmr =>
        (beginBlock pp Inconsistent 0; printer subpr pp tmr; endBlock pp)
      end
    end;

(* ------------------------------------------------------------------------- *)
(* Quotations                                                                *)
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
