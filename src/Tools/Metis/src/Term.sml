(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* Copyright (c) 2001 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Term :> Term =
struct

open Useful;

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

fun equalVar v (Var v') = Name.equal v v'
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
    if Name.equal x f then (a,b) else raise Error "Term.destBinop: wrong binop"
  | destBinop _ _ = raise Error "Term.destBinop: not a binop";

fun isBinop f = can (destBinop f);

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

val VAR_SYMBOLS = 1;

val FN_SYMBOLS = 1;

local
  fun sz n [] = n
    | sz n (Var _ :: tms) = sz (n + VAR_SYMBOLS) tms
    | sz n (Fn (func,args) :: tms) = sz (n + FN_SYMBOLS) (args @ tms);
in
  fun symbols tm = sz 0 [tm];
end;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp [] [] = EQUAL
    | cmp (tm1 :: tms1) (tm2 :: tms2) =
      let
        val tm1_tm2 = (tm1,tm2)
      in
        if Portable.pointerEqual tm1_tm2 then cmp tms1 tms2
        else
          case tm1_tm2 of
            (Var v1, Var v2) =>
            (case Name.compare (v1,v2) of
               LESS => LESS
             | EQUAL => cmp tms1 tms2
             | GREATER => GREATER)
          | (Var _, Fn _) => LESS
          | (Fn _, Var _) => GREATER
          | (Fn (f1,a1), Fn (f2,a2)) =>
            (case Name.compare (f1,f2) of
               LESS => LESS
             | EQUAL =>
               (case Int.compare (length a1, length a2) of
                  LESS => LESS
                | EQUAL => cmp (a1 @ tms1) (a2 @ tms2)
                | GREATER => GREATER)
             | GREATER => GREATER)
      end
    | cmp _ _ = raise Bug "Term.compare";
in
  fun compare (tm1,tm2) = cmp [tm1] [tm2];
end;

fun equal tm1 tm2 = compare (tm1,tm2) = EQUAL;

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

        val acc = (List.rev path, tm) :: acc
      in
        case tm of
          Var _ => subtms rest acc
        | Fn (_,args) => subtms (List.map f (enumerate args) @ rest) acc
      end;
in
  fun subterms tm = subtms [([],tm)] [];
end;

fun replace tm ([],res) = if equal res tm then tm else res
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
          if Portable.pointerEqual (arg',arg) then tm
          else Fn (func, updateNth (h,arg') tms)
        end;

fun find pred =
    let
      fun search [] = NONE
        | search ((path,tm) :: rest) =
          if pred tm then SOME (List.rev path)
          else
            case tm of
              Var _ => search rest
            | Fn (_,a) =>
              let
                val subtms = List.map (fn (i,t) => (i :: path, t)) (enumerate a)
              in
                search (subtms @ rest)
              end
    in
      fn tm => search [([],tm)]
    end;

val ppPath = Print.ppList Print.ppInt;

val pathToString = Print.toString ppPath;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun free _ [] = false
    | free v (Var w :: tms) = Name.equal v w orelse free v tms
    | free v (Fn (_,args) :: tms) = free v (args @ tms);
in
  fun freeIn v tm = free v [tm];
end;

local
  fun free vs [] = vs
    | free vs (Var v :: tms) = free (NameSet.add vs v) tms
    | free vs (Fn (_,args) :: tms) = free vs (args @ tms);
in
  val freeVarsList = free NameSet.empty;

  fun freeVars tm = freeVarsList [tm];
end;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

fun newVar () = Var (Name.newName ());

fun newVars n = List.map Var (Name.newNames n);

local
  fun avoid av n = NameSet.member n av;
in
  fun variantPrime av = Name.variantPrime {avoid = avoid av};

  fun variantNum av = Name.variantNum {avoid = avoid av};
end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val hasTypeFunctionName = Name.fromString ":";

val hasTypeFunction = (hasTypeFunctionName,2);

fun destFnHasType ((f,a) : functionName * term list) =
    if not (Name.equal f hasTypeFunctionName) then
      raise Error "Term.destFnHasType"
    else
      case a of
        [tm,ty] => (tm,ty)
      | _ => raise Error "Term.destFnHasType";

val isFnHasType = can destFnHasType;

fun isTypedVar tm =
    case tm of
      Var _ => true
    | Fn func =>
      case total destFnHasType func of
        SOME (Var _, _) => true
      | _ => false;

local
  fun sz n [] = n
    | sz n (tm :: tms) =
      case tm of
        Var _ => sz (n + 1) tms
      | Fn func =>
        case total destFnHasType func of
          SOME (tm,_) => sz n (tm :: tms)
        | NONE =>
          let
            val (_,a) = func
          in
            sz (n + 1) (a @ tms)
          end;
in
  fun typedSymbols tm = sz 0 [tm];
end;

local
  fun subtms [] acc = acc
    | subtms ((path,tm) :: rest) acc =
      case tm of
        Var _ => subtms rest acc
      | Fn func =>
        case total destFnHasType func of
          SOME (t,_) =>
          (case t of
             Var _ => subtms rest acc
           | Fn _ =>
             let
               val acc = (List.rev path, tm) :: acc
               val rest = (0 :: path, t) :: rest
             in
               subtms rest acc
             end)
        | NONE =>
          let
            fun f (n,arg) = (n :: path, arg)

            val (_,args) = func

            val acc = (List.rev path, tm) :: acc

            val rest = List.map f (enumerate args) @ rest
          in
            subtms rest acc
          end;
in
  fun nonVarTypedSubterms tm = subtms [([],tm)] [];
end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

val appName = Name.fromString ".";

fun mkFnApp (fTm,aTm) = (appName, [fTm,aTm]);

fun mkApp f_a = Fn (mkFnApp f_a);

fun destFnApp ((f,a) : Name.name * term list) =
    if not (Name.equal f appName) then raise Error "Term.destFnApp"
    else
      case a of
        [fTm,aTm] => (fTm,aTm)
      | _ => raise Error "Term.destFnApp";

val isFnApp = can destFnApp;

fun destApp tm =
    case tm of
      Var _ => raise Error "Term.destApp"
    | Fn func => destFnApp func;

val isApp = can destApp;

fun listMkApp (f,l) = List.foldl mkApp f l;

local
  fun strip tms tm =
      case total destApp tm of
        SOME (f,a) => strip (a :: tms) f
      | NONE => (tm,tms);
in
  fun stripApp tm = strip [] tm;
end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

(* Operators parsed and printed infix *)

val infixes =
    (ref o Print.Infixes)
      [(* ML symbols *)
       {token = "/", precedence = 7, assoc = Print.LeftAssoc},
       {token = "div", precedence = 7, assoc = Print.LeftAssoc},
       {token = "mod", precedence = 7, assoc = Print.LeftAssoc},
       {token = "*", precedence = 7, assoc = Print.LeftAssoc},
       {token = "+", precedence = 6, assoc = Print.LeftAssoc},
       {token = "-", precedence = 6, assoc = Print.LeftAssoc},
       {token = "^", precedence = 6, assoc = Print.LeftAssoc},
       {token = "@", precedence = 5, assoc = Print.RightAssoc},
       {token = "::", precedence = 5, assoc = Print.RightAssoc},
       {token = "=", precedence = 4, assoc = Print.NonAssoc},
       {token = "<>", precedence = 4, assoc = Print.NonAssoc},
       {token = "<=", precedence = 4, assoc = Print.NonAssoc},
       {token = "<", precedence = 4, assoc = Print.NonAssoc},
       {token = ">=", precedence = 4, assoc = Print.NonAssoc},
       {token = ">", precedence = 4, assoc = Print.NonAssoc},
       {token = "o", precedence = 3, assoc = Print.LeftAssoc},
       {token = "->", precedence = 2, assoc = Print.RightAssoc},
       {token = ":", precedence = 1, assoc = Print.NonAssoc},
       {token = ",", precedence = 0, assoc = Print.RightAssoc},

       (* Logical connectives *)
       {token = "/\\", precedence = ~1, assoc = Print.RightAssoc},
       {token = "\\/", precedence = ~2, assoc = Print.RightAssoc},
       {token = "==>", precedence = ~3, assoc = Print.RightAssoc},
       {token = "<=>", precedence = ~4, assoc = Print.RightAssoc},

       (* Other symbols *)
       {token = ".", precedence = 9, assoc = Print.LeftAssoc},
       {token = "**", precedence = 8, assoc = Print.LeftAssoc},
       {token = "++", precedence = 6, assoc = Print.LeftAssoc},
       {token = "--", precedence = 6, assoc = Print.LeftAssoc},
       {token = "==", precedence = 4, assoc = Print.NonAssoc}];

(* The negation symbol *)

val negation : string ref = ref "~";

(* Binder symbols *)

val binders : string list ref = ref ["\\","!","?","?!"];

(* Bracket symbols *)

val brackets : (string * string) list ref = ref [("[","]"),("{","}")];

(* Pretty printing *)

fun pp inputTerm =
    let
      val quants = !binders
      and iOps = !infixes
      and neg = !negation
      and bracks = !brackets

      val bMap =
          let
            fun f (b1,b2) = (b1 ^ b2, b1, b2)
          in
            List.map f bracks
          end

      val bTokens = op@ (unzip bracks)

      val iTokens = Print.tokensInfixes iOps

      fun destI tm =
          case tm of
            Fn (f,[a,b]) =>
            let
              val f = Name.toString f
            in
              if StringSet.member f iTokens then SOME (f,a,b) else NONE
            end
          | _ => NONE

      fun isI tm = Option.isSome (destI tm)

      fun iToken (_,tok) =
          Print.program
            [(if tok = "," then Print.skip else Print.ppString " "),
             Print.ppString tok,
             Print.break];

      val iPrinter = Print.ppInfixes iOps destI iToken

      val specialTokens =
          StringSet.addList iTokens (neg :: quants @ ["$","(",")"] @ bTokens)

      fun vName bv s = StringSet.member s bv

      fun checkVarName bv n =
          let
            val s = Name.toString n
          in
            if vName bv s then s else "$" ^ s
          end

      fun varName bv = Print.ppMap (checkVarName bv) Print.ppString

      fun checkFunctionName bv n =
          let
            val s = Name.toString n
          in
            if StringSet.member s specialTokens orelse vName bv s then
              "(" ^ s ^ ")"
            else
              s
          end

      fun functionName bv = Print.ppMap (checkFunctionName bv) Print.ppString

      fun stripNeg tm =
          case tm of
            Fn (f,[a]) =>
            if Name.toString f <> neg then (0,tm)
            else let val (n,tm) = stripNeg a in (n + 1, tm) end
          | _ => (0,tm)

      val destQuant =
          let
            fun dest q (Fn (q', [Var v, body])) =
                if Name.toString q' <> q then NONE
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
          let
            val s = Name.toString b
          in
            case List.find (fn (n,_,_) => n = s) bMap of
              NONE => NONE
            | SOME (_,b1,b2) => SOME (b1,tm,b2)
          end
        | destBrack _ = NONE

      fun isBrack tm = Option.isSome (destBrack tm)

      fun functionArgument bv tm =
          Print.sequence
            Print.break
            (if isBrack tm then customBracket bv tm
             else if isVar tm orelse isConst tm then basic bv tm
             else bracket bv tm)

      and basic bv (Var v) = varName bv v
        | basic bv (Fn (f,args)) =
          Print.inconsistentBlock 2
            (functionName bv f :: List.map (functionArgument bv) args)

      and customBracket bv tm =
          case destBrack tm of
            SOME (b1,tm,b2) => Print.ppBracket b1 b2 (term bv) tm
          | NONE => basic bv tm

      and innerQuant bv tm =
          case destQuant tm of
            NONE => term bv tm
          | SOME (q,v,vs,tm) =>
            let
              val bv = StringSet.addList bv (List.map Name.toString (v :: vs))
            in
              Print.program
                [Print.ppString q,
                 varName bv v,
                 Print.program
                   (List.map (Print.sequence Print.break o varName bv) vs),
                 Print.ppString ".",
                 Print.break,
                 innerQuant bv tm]
            end

      and quantifier bv tm =
          if not (isQuant tm) then customBracket bv tm
          else Print.inconsistentBlock 2 [innerQuant bv tm]

      and molecule bv (tm,r) =
          let
            val (n,tm) = stripNeg tm
          in
            Print.inconsistentBlock n
              [Print.duplicate n (Print.ppString neg),
               if isI tm orelse (r andalso isQuant tm) then bracket bv tm
               else quantifier bv tm]
          end

      and term bv tm = iPrinter (molecule bv) (tm,false)

      and bracket bv tm = Print.ppBracket "(" ")" (term bv) tm
    in
      term StringSet.empty
    end inputTerm;

val toString = Print.toString pp;

(* Parsing *)

local
  open Parse;

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  val isAlphaNum =
      let
        val alphaNumChars = String.explode "_'"
      in
        fn c => mem c alphaNumChars orelse Char.isAlphaNum c
      end;

  local
    val alphaNumToken = atLeastOne (some isAlphaNum) >> String.implode;

    val symbolToken =
        let
          fun isNeg c = str c = !negation

          val symbolChars = String.explode "<>=-*+/\\?@|!$%&#^:;~"

          fun isSymbol c = mem c symbolChars

          fun isNonNegSymbol c = not (isNeg c) andalso isSymbol c
        in
          some isNeg >> str ||
          (some isNonNegSymbol ++ many (some isSymbol)) >>
          (String.implode o op::)
        end;

    val punctToken =
        let
          val punctChars = String.explode "()[]{}.,"

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

        val bracks = List.map (fn (b1,b2) => (b1 ^ b2, b1, b2)) bracks

        val bTokens = List.map #2 bracks @ List.map #3 bracks

        fun possibleVarName "" = false
          | possibleVarName s = isAlphaNum (String.sub (s,0))

        fun vName bv s = StringSet.member s bv

        val iTokens = Print.tokensInfixes iOps

        fun iMk (f,a,b) = Fn (Name.fromString f, [a,b])

        val iParser = parseInfixes iOps iMk any

        val specialTokens =
            StringSet.addList iTokens (neg :: quants @ ["$"] @ bTokens)

        fun varName bv =
            some (vName bv) ||
            (some (Useful.equal "$") ++ some possibleVarName) >> snd

        fun fName bv s =
            not (StringSet.member s specialTokens) andalso not (vName bv s)

        fun functionName bv =
            some (fName bv) ||
            (some (Useful.equal "(") ++ any ++ some (Useful.equal ")")) >>
            (fn (_,(s,_)) => s)

        fun basic bv tokens =
            let
              val var = varName bv >> (Var o Name.fromString)

              val const =
                  functionName bv >> (fn f => Fn (Name.fromString f, []))

              fun bracket (ab,a,b) =
                  (some (Useful.equal a) ++ term bv ++ some (Useful.equal b)) >>
                  (fn (_,(tm,_)) =>
                      if ab = "()" then tm else Fn (Name.fromString ab, [tm]))

              fun quantifier q =
                  let
                    fun bind (v,t) =
                        Fn (Name.fromString q, [Var (Name.fromString v), t])
                  in
                    (some (Useful.equal q) ++
                     atLeastOne (some possibleVarName) ++
                     some (Useful.equal ".")) >>++
                    (fn (_,(vs,_)) =>
                        term (StringSet.addList bv vs) >>
                        (fn body => List.foldr bind body vs))
                  end
            in
              var ||
              const ||
              first (List.map bracket bracks) ||
              first (List.map quantifier quants)
            end tokens

        and molecule bv tokens =
            let
              val negations = many (some (Useful.equal neg)) >> length

              val function =
                  (functionName bv ++ many (basic bv)) >>
                  (fn (f,args) => Fn (Name.fromString f, args)) ||
                  basic bv
            in
              (negations ++ function) >>
              (fn (n,tm) => funpow n (fn t => Fn (Name.fromString neg, [t])) tm)
            end tokens

        and term bv tokens = iParser (molecule bv) tokens
      in
        term StringSet.empty
      end inputStream;
in
  fun fromString input =
      let
        val chars = Stream.fromList (String.explode input)

        val tokens = everything (lexer >> singleton) chars

        val terms = everything (termParser >> singleton) tokens
      in
        case Stream.toList terms of
          [tm] => tm
        | _ => raise Error "Term.fromString"
      end;
end;

local
  val antiquotedTermToString =
      Print.toString (Print.ppBracket "(" ")" pp);
in
  val parse = Parse.parseQuotation antiquotedTermToString fromString;
end;

end

structure TermOrdered =
struct type t = Term.term val compare = Term.compare end

structure TermMap = KeyMap (TermOrdered);

structure TermSet = ElementSet (TermMap);
