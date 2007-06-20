(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Term :> Term =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun stripSuffix pred s =
    let
      fun f 0 = ""
        | f n =
          let
            val n' = n - 1
          in
            if pred (String.sub (s,n')) then f n'
            else String.substring (s,0,n)
          end
    in
      f (size s)
    end;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Name.name;

type functionName = Name.name;

type function = functionName * int;

type const = functionName;

datatype term =
    Var of Name.name
  | Fn of Name.name * term list;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

fun destVar (Var v) = v
  | destVar (Fn _) = raise Error "destVar";

val isVar = can destVar;

fun equalVar v (Var v') = v = v'
  | equalVar _ _ = false;

(* Functions *)

fun destFn (Fn f) = f
  | destFn (Var _) = raise Error "destFn";

val isFn = can destFn;

fun fnName tm = fst (destFn tm);

fun fnArguments tm = snd (destFn tm);

fun fnArity tm = length (fnArguments tm);

fun fnFunction tm = (fnName tm, fnArity tm);

local
  fun func fs [] = fs
    | func fs (Var _ :: tms) = func fs tms
    | func fs (Fn (n,l) :: tms) =
      func (NameAritySet.add fs (n, length l)) (l @ tms);
in
  fun functions tm = func NameAritySet.empty [tm];
end;

local
  fun func fs [] = fs
    | func fs (Var _ :: tms) = func fs tms
    | func fs (Fn (n,l) :: tms) = func (NameSet.add fs n) (l @ tms);
in
  fun functionNames tm = func NameSet.empty [tm];
end;

(* Constants *)

fun mkConst c = (Fn (c, []));

fun destConst (Fn (c, [])) = c
  | destConst _ = raise Error "destConst";

val isConst = can destConst;

(* Binary functions *)

fun mkBinop f (a,b) = Fn (f,[a,b]);

fun destBinop f (Fn (x,[a,b])) =
    if x = f then (a,b) else raise Error "Term.destBinop: wrong binop"
  | destBinop _ _ = raise Error "Term.destBinop: not a binop";

fun isBinop f = can (destBinop f);

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

local
  fun sz n [] = n
    | sz n (Var _ :: tms) = sz (n + 1) tms
    | sz n (Fn (_,args) :: tms) = sz (n + 1) (args @ tms);
in
  fun symbols tm = sz 0 [tm];
end;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp [] [] = EQUAL
    | cmp (Var _ :: _) (Fn _ :: _) = LESS
    | cmp (Fn _ :: _) (Var _ :: _) = GREATER
    | cmp (Var v1 :: tms1) (Var v2 :: tms2) =
      (case Name.compare (v1,v2) of
         LESS => LESS
       | EQUAL => cmp tms1 tms2
       | GREATER => GREATER)
    | cmp (Fn (f1,a1) :: tms1) (Fn (f2,a2) :: tms2) =
      (case Name.compare (f1,f2) of
         LESS => LESS
       | EQUAL =>
         (case Int.compare (length a1, length a2) of
            LESS => LESS
          | EQUAL => cmp (a1 @ tms1) (a2 @ tms2)
          | GREATER => GREATER)
       | GREATER => GREATER)
    | cmp _ _ = raise Bug "Term.compare";
in
  fun compare (tm1,tm2) = cmp [tm1] [tm2];
end;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list;

fun subterm tm [] = tm
  | subterm (Var _) (_ :: _) = raise Error "Term.subterm: Var"
  | subterm (Fn (_,tms)) (h :: t) =
    if h >= length tms then raise Error "Term.replace: Fn"
    else subterm (List.nth (tms,h)) t;

local
  fun subtms [] acc = acc
    | subtms ((path,tm) :: rest) acc =
      let
        fun f (n,arg) = (n :: path, arg)

        val acc = (rev path, tm) :: acc
      in
        case tm of
          Var _ => subtms rest acc
        | Fn (_,args) => subtms (map f (enumerate args) @ rest) acc
      end;
in
  fun subterms tm = subtms [([],tm)] [];
end;

fun replace tm ([],res) = if res = tm then tm else res
  | replace tm (h :: t, res) =
    case tm of
      Var _ => raise Error "Term.replace: Var"
    | Fn (func,tms) =>
      if h >= length tms then raise Error "Term.replace: Fn"
      else
        let
          val arg = List.nth (tms,h)
          val arg' = replace arg (t,res)
        in
          if Sharing.pointerEqual (arg',arg) then tm
          else Fn (func, updateNth (h,arg') tms)
        end;

fun find pred =
    let
      fun search [] = NONE
        | search ((path,tm) :: rest) =
          if pred tm then SOME (rev path)
          else
            case tm of
              Var _ => search rest
            | Fn (_,a) =>
              let
                val subtms = map (fn (i,t) => (i :: path, t)) (enumerate a)
              in
                search (subtms @ rest)
              end
    in
      fn tm => search [([],tm)]
    end;

val ppPath = Parser.ppList Parser.ppInt;

val pathToString = Parser.toString ppPath;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun free _ [] = false
    | free v (Var w :: tms) = v = w orelse free v tms
    | free v (Fn (_,args) :: tms) = free v (args @ tms);
in
  fun freeIn v tm = free v [tm];
end;

local
  fun free vs [] = vs
    | free vs (Var v :: tms) = free (NameSet.add vs v) tms
    | free vs (Fn (_,args) :: tms) = free vs (args @ tms);
in
  fun freeVars tm = free NameSet.empty [tm];
end;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  val prefix  = "_";

  fun numVar i = Var (mkPrefix prefix (Int.toString i));
in
  fun newVar () = numVar (newInt ());

  fun newVars n = map numVar (newInts n);
end;

fun variantPrime avoid =
    let
      fun f v = if NameSet.member v avoid then f (v ^ "'") else v
    in
      f
    end;

fun variantNum avoid v =
    if not (NameSet.member v avoid) then v
    else
      let
        val v = stripSuffix Char.isDigit v
                                                                    
        fun f n =
            let
              val v_n = v ^ Int.toString n
            in
              if NameSet.member v_n avoid then f (n + 1) else v_n
            end
      in
        f 0
      end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

fun isTypedVar (Var _) = true
  | isTypedVar (Fn (":", [Var _, _])) = true
  | isTypedVar (Fn _) = false;

local
  fun sz n [] = n
    | sz n (Var _ :: tms) = sz (n + 1) tms
    | sz n (Fn (":",[tm,_]) :: tms) = sz n (tm :: tms)
    | sz n (Fn (_,args) :: tms) = sz (n + 1) (args @ tms);
in
  fun typedSymbols tm = sz 0 [tm];
end;

local
  fun subtms [] acc = acc
    | subtms ((_, Var _) :: rest) acc = subtms rest acc
    | subtms ((_, Fn (":", [Var _, _])) :: rest) acc = subtms rest acc
    | subtms ((path, tm as Fn func) :: rest) acc =
      let
        fun f (n,arg) = (n :: path, arg)

        val acc = (rev path, tm) :: acc
      in
        case func of
          (":",[arg,_]) => subtms ((0 :: path, arg) :: rest) acc
        | (_,args) => subtms (map f (enumerate args) @ rest) acc
      end;
in
  fun nonVarTypedSubterms tm = subtms [([],tm)] [];
end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

fun mkComb (f,a) = Fn (".",[f,a]);

fun destComb (Fn (".",[f,a])) = (f,a)
  | destComb _ = raise Error "destComb";

val isComb = can destComb;

fun listMkComb (f,l) = foldl mkComb f l;

local
  fun strip tms (Fn (".",[f,a])) = strip (a :: tms) f
    | strip tms tm = (tm,tms);
in
  fun stripComb tm = strip [] tm;
end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

(* Operators parsed and printed infix *)

val infixes : Parser.infixities ref = ref
  [(* ML symbols *)
   {token = " / ", precedence = 7, leftAssoc = true},
   {token = " div ", precedence = 7, leftAssoc = true},
   {token = " mod ", precedence = 7, leftAssoc = true},
   {token = " * ", precedence = 7, leftAssoc = true},
   {token = " + ", precedence = 6, leftAssoc = true},
   {token = " - ", precedence = 6, leftAssoc = true},
   {token = " ^ ", precedence = 6, leftAssoc = true},
   {token = " @ ", precedence = 5, leftAssoc = false},
   {token = " :: ", precedence = 5, leftAssoc = false},
   {token = " = ", precedence = 4, leftAssoc = true},
   {token = " <> ", precedence = 4, leftAssoc = true},
   {token = " <= ", precedence = 4, leftAssoc = true},
   {token = " < ", precedence = 4, leftAssoc = true},
   {token = " >= ", precedence = 4, leftAssoc = true},
   {token = " > ", precedence = 4, leftAssoc = true},
   {token = " o ", precedence = 3, leftAssoc = true},
   {token = " -> ", precedence = 2, leftAssoc = false},  (* inferred prec *)
   {token = " : ", precedence = 1, leftAssoc = false},  (* inferred prec *)
   {token = ", ", precedence = 0, leftAssoc = false},  (* inferred prec *)

   (* Logical connectives *)
   {token = " /\\ ", precedence = ~1, leftAssoc = false},
   {token = " \\/ ", precedence = ~2, leftAssoc = false},
   {token = " ==> ", precedence = ~3, leftAssoc = false},
   {token = " <=> ", precedence = ~4, leftAssoc = false},

   (* Other symbols *)
   {token = " . ", precedence = 9, leftAssoc = true},  (* function app *)
   {token = " ** ", precedence = 8, leftAssoc = true},
   {token = " ++ ", precedence = 6, leftAssoc = true},
   {token = " -- ", precedence = 6, leftAssoc = true},
   {token = " == ", precedence = 4, leftAssoc = true}];

(* The negation symbol *)

val negation : Name.name ref = ref "~";

(* Binder symbols *)

val binders : Name.name list ref = ref ["\\","!","?","?!"];

(* Bracket symbols *)

val brackets : (Name.name * Name.name) list ref = ref [("[","]"),("{","}")];

(* Pretty printing *)

local
  open Parser;
in
  fun pp inputPpstrm inputTerm =
      let
        val quants = !binders
        and iOps = !infixes
        and neg = !negation
        and bracks = !brackets

        val bracks = map (fn (b1,b2) => (b1 ^ b2, b1, b2)) bracks

        val bTokens = map #2 bracks @ map #3 bracks

        val iTokens = infixTokens iOps

        fun destI (Fn (f,[a,b])) =
            if mem f iTokens then SOME (f,a,b) else NONE
          | destI _ = NONE

        val iPrinter = ppInfixes iOps destI

        val specialTokens = neg :: quants @ ["$","(",")"] @ bTokens @ iTokens

        fun vName bv s = NameSet.member s bv

        fun checkVarName bv s = if vName bv s then s else "$" ^ s

        fun varName bv = ppMap (checkVarName bv) ppString

        fun checkFunctionName bv s =
            if mem s specialTokens orelse vName bv s then "(" ^ s ^ ")" else s

        fun functionName bv = ppMap (checkFunctionName bv) ppString

        fun isI tm = Option.isSome (destI tm)

        fun stripNeg (tm as Fn (f,[a])) =
            if f <> neg then (0,tm)
            else let val (n,tm) = stripNeg a in (n + 1, tm) end
          | stripNeg tm = (0,tm)

        val destQuant =
            let
              fun dest q (Fn (q', [Var v, body])) =
                  if q <> q' then NONE
                  else
                    (case dest q body of
                       NONE => SOME (q,v,[],body)
                     | SOME (_,v',vs,body) => SOME (q, v, v' :: vs, body))
                | dest _ _ = NONE
            in
              fn tm => Useful.first (fn q => dest q tm) quants
            end

        fun isQuant tm = Option.isSome (destQuant tm)

        fun destBrack (Fn (b,[tm])) =
            (case List.find (fn (n,_,_) => n = b) bracks of
               NONE => NONE
             | SOME (_,b1,b2) => SOME (b1,tm,b2))
          | destBrack _ = NONE

        fun isBrack tm = Option.isSome (destBrack tm)
            
        fun functionArgument bv ppstrm tm =
            (addBreak ppstrm (1,0);
             if isBrack tm then customBracket bv ppstrm tm
             else if isVar tm orelse isConst tm then basic bv ppstrm tm
             else bracket bv ppstrm tm)

        and basic bv ppstrm (Var v) = varName bv ppstrm v
          | basic bv ppstrm (Fn (f,args)) =
            (beginBlock ppstrm Inconsistent 2;
             functionName bv ppstrm f;
             app (functionArgument bv ppstrm) args;
             endBlock ppstrm)

        and customBracket bv ppstrm tm =
            case destBrack tm of
              SOME (b1,tm,b2) => ppBracket b1 b2 (term bv) ppstrm tm
            | NONE => basic bv ppstrm tm

        and innerQuant bv ppstrm tm =
            case destQuant tm of
              NONE => term bv ppstrm tm
            | SOME (q,v,vs,tm) =>
              let
                val bv = NameSet.addList (NameSet.add bv v) vs
              in
                addString ppstrm q;
                varName bv ppstrm v;
                app (fn v => (addBreak ppstrm (1,0); varName bv ppstrm v)) vs;
                addString ppstrm ".";
                addBreak ppstrm (1,0);
                innerQuant bv ppstrm tm
              end

        and quantifier bv ppstrm tm =
            if not (isQuant tm) then customBracket bv ppstrm tm
            else
              (beginBlock ppstrm Inconsistent 2;
               innerQuant bv ppstrm tm;
               endBlock ppstrm)

        and molecule bv ppstrm (tm,r) =
            let
              val (n,tm) = stripNeg tm
            in
              beginBlock ppstrm Inconsistent n;
              funpow n (fn () => addString ppstrm neg) ();
              if isI tm orelse (r andalso isQuant tm) then bracket bv ppstrm tm
              else quantifier bv ppstrm tm;
              endBlock ppstrm
            end

        and term bv ppstrm tm = iPrinter (molecule bv) ppstrm (tm,false)

        and bracket bv ppstrm tm = ppBracket "(" ")" (term bv) ppstrm tm
  in
    term NameSet.empty
  end inputPpstrm inputTerm;
end;

fun toString tm = Parser.toString pp tm;

(* Parsing *)

local
  open Parser;

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  val isAlphaNum =
      let
        val alphaNumChars = explode "_'"
      in
        fn c => mem c alphaNumChars orelse Char.isAlphaNum c
      end;

  local
    val alphaNumToken = atLeastOne (some isAlphaNum) >> implode;

    val symbolToken =
        let
          fun isNeg c = str c = !negation
                        
          val symbolChars = explode "<>=-*+/\\?@|!$%&#^:;~"

          fun isSymbol c = mem c symbolChars

          fun isNonNegSymbol c = not (isNeg c) andalso isSymbol c
        in
          some isNeg >> str ||
          (some isNonNegSymbol ++ many (some isSymbol)) >> (implode o op::)
        end;

    val punctToken =
        let
          val punctChars = explode "()[]{}.,"

          fun isPunct c = mem c punctChars
        in
          some isPunct >> str
        end;

    val lexToken = alphaNumToken || symbolToken || punctToken;

    val space = many (some Char.isSpace);
  in
    val lexer = (space ++ lexToken ++ space) >> (fn (_,(tok,_)) => tok);
  end;

  fun termParser inputStream =
      let
        val quants = !binders
        and iOps = !infixes
        and neg = !negation
        and bracks = ("(",")") :: !brackets

        val bracks = map (fn (b1,b2) => (b1 ^ b2, b1, b2)) bracks

        val bTokens = map #2 bracks @ map #3 bracks

        fun possibleVarName "" = false
          | possibleVarName s = isAlphaNum (String.sub (s,0))

        fun vName bv s = NameSet.member s bv

        val iTokens = infixTokens iOps

        val iParser = parseInfixes iOps (fn (f,a,b) => Fn (f,[a,b]))

        val specialTokens = neg :: quants @ ["$"] @ bTokens @ iTokens

        fun varName bv =
            Parser.some (vName bv) ||
            (exact "$" ++ some possibleVarName) >> (fn (_,s) => s)

        fun fName bv s = not (mem s specialTokens) andalso not (vName bv s)

        fun functionName bv =
            Parser.some (fName bv) ||
            (exact "(" ++ any ++ exact ")") >> (fn (_,(s,_)) => s)

        fun basic bv tokens =
            let
              val var = varName bv >> Var

              val const = functionName bv >> (fn f => Fn (f,[]))

              fun bracket (ab,a,b) =
                  (exact a ++ term bv ++ exact b) >>
                  (fn (_,(tm,_)) => if ab = "()" then tm else Fn (ab,[tm]))

              fun quantifier q =
                  let
                    fun bind (v,t) = Fn (q, [Var v, t])
                  in
                    (exact q ++ atLeastOne (some possibleVarName) ++
                     exact ".") >>++
                    (fn (_,(vs,_)) =>
                        term (NameSet.addList bv vs) >>
                        (fn body => foldr bind body vs))
                  end
            in
              var ||
              const ||
              first (map bracket bracks) ||
              first (map quantifier quants)
            end tokens

        and molecule bv tokens =
            let
              val negations = many (exact neg) >> length

              val function =
                  (functionName bv ++ many (basic bv)) >> Fn || basic bv
            in
              (negations ++ function) >>
              (fn (n,tm) => funpow n (fn t => Fn (neg,[t])) tm)
            end tokens

        and term bv tokens = iParser (molecule bv) tokens
      in
        term NameSet.empty
      end inputStream;
in
  fun fromString input =
      let
        val chars = Stream.fromList (explode input)

        val tokens = everything (lexer >> singleton) chars

        val terms = everything (termParser >> singleton) tokens
      in
        case Stream.toList terms of
          [tm] => tm
        | _ => raise Error "Syntax.stringToTerm"
      end;
end;

local
  val antiquotedTermToString =
      Parser.toString (Parser.ppBracket "(" ")" pp);
in
  val parse = Parser.parseQuotation antiquotedTermToString fromString;
end;

end

structure TermOrdered =
struct type t = Term.term val compare = Term.compare end

structure TermSet = ElementSet (TermOrdered);

structure TermMap = KeyMap (TermOrdered);
