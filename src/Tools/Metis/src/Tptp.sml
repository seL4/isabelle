(* ========================================================================= *)
(* THE TPTP PROBLEM FILE FORMAT (TPTP v2)                                    *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Tptp :> Tptp =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

val ROLE_NEGATED_CONJECTURE = "negated_conjecture"
and ROLE_CONJECTURE = "conjecture";

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun isHdTlString hp tp s =
    let
      fun ct 0 = true
        | ct i = tp (String.sub (s,i)) andalso ct (i - 1)

      val n = size s
    in
      n > 0 andalso hp (String.sub (s,0)) andalso ct (n - 1)
    end;

(* ------------------------------------------------------------------------- *)
(* Mapping TPTP functions and relations to different names.                  *)
(* ------------------------------------------------------------------------- *)

val functionMapping = ref
    [(* Mapping TPTP functions to infix symbols *)
     {name = "*", arity = 2, tptp = "multiply"},
     {name = "/", arity = 2, tptp = "divide"},
     {name = "+", arity = 2, tptp = "add"},
     {name = "-", arity = 2, tptp = "subtract"},
     {name = "::", arity = 2, tptp = "cons"},
     {name = ",", arity = 2, tptp = "pair"},
     (* Expanding HOL symbols to TPTP alphanumerics *)
     {name = ":", arity = 2, tptp = "has_type"},
     {name = ".", arity = 2, tptp = "apply"},
     {name = "<=", arity = 0, tptp = "less_equal"}];

val relationMapping = ref
    [(* Mapping TPTP relations to infix symbols *)
     {name = "=", arity = 2, tptp = "="},
     {name = "==", arity = 2, tptp = "equalish"},
     {name = "<=", arity = 2, tptp = "less_equal"},
     {name = "<", arity = 2, tptp = "less_than"},
     (* Expanding HOL symbols to TPTP alphanumerics *)
     {name = "{}", arity = 1, tptp = "bool"}];

fun mappingToTptp x =
    let
      fun mk ({name,arity,tptp},m) = NameArityMap.insert m ((name,arity),tptp)
    in
      foldl mk (NameArityMap.new ()) x
    end;

fun mappingFromTptp x =
    let
      fun mk ({name,arity,tptp},m) = NameArityMap.insert m ((tptp,arity),name)
    in
      foldl mk (NameArityMap.new ()) x
    end;

fun findMapping mapping (name_arity as (n,_)) =
    Option.getOpt (NameArityMap.peek mapping name_arity, n);

fun mapTerm functionMap =
    let
      val mapName = findMapping functionMap

      fun mapTm (tm as Term.Var _) = tm
        | mapTm (Term.Fn (f,a)) = Term.Fn (mapName (f, length a), map mapTm a)
    in
      mapTm
    end;

fun mapAtom {functionMap,relationMap} (p,a) =
    (findMapping relationMap (p, length a), map (mapTerm functionMap) a);

fun mapFof maps =
    let
      open Formula

      fun form True = True
        | form False = False
        | form (Atom a) = Atom (mapAtom maps a)
        | form (Not p) = Not (form p)
        | form (And (p,q)) = And (form p, form q)
        | form (Or (p,q)) = Or (form p, form q)
        | form (Imp (p,q)) = Imp (form p, form q)
        | form (Iff (p,q)) = Iff (form p, form q)
        | form (Forall (v,p)) = Forall (v, form p)
        | form (Exists (v,p)) = Exists (v, form p)
    in
      form
    end;

(* ------------------------------------------------------------------------- *)
(* Comments.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun mkComment "" = "%"
  | mkComment line = "% " ^ line;

fun destComment "" = ""
  | destComment l =
    let
      val _ = String.sub (l,0) = #"%" orelse raise Error "destComment"
      val n = if size l >= 2 andalso String.sub (l,1) = #" " then 2 else 1
    in
      String.extract (l,n,NONE)
    end;

val isComment = can destComment;

(* ------------------------------------------------------------------------- *)
(* TPTP literals.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype literal =
    Boolean of bool
  | Literal of Literal.literal;

fun negate (Boolean b) = (Boolean (not b))
  | negate (Literal l) = (Literal (Literal.negate l));

fun literalFunctions (Boolean _) = NameAritySet.empty
  | literalFunctions (Literal lit) = Literal.functions lit;

fun literalRelation (Boolean _) = NONE
  | literalRelation (Literal lit) = SOME (Literal.relation lit);

fun literalToFormula (Boolean true) = Formula.True
  | literalToFormula (Boolean false) = Formula.False
  | literalToFormula (Literal lit) = Literal.toFormula lit;

fun literalFromFormula Formula.True = Boolean true
  | literalFromFormula Formula.False = Boolean false
  | literalFromFormula fm = Literal (Literal.fromFormula fm);

fun literalFreeVars (Boolean _) = NameSet.empty
  | literalFreeVars (Literal lit) = Literal.freeVars lit;

fun literalSubst sub lit =
    case lit of
      Boolean _ => lit
    | Literal l => Literal (Literal.subst sub l);

fun mapLiteral maps lit =
    case lit of
      Boolean _ => lit
    | Literal (p,a) => Literal (p, mapAtom maps a);

fun destLiteral (Literal l) = l
  | destLiteral _ = raise Error "destLiteral";

(* ------------------------------------------------------------------------- *)
(* Printing formulas using TPTP syntax.                                      *)
(* ------------------------------------------------------------------------- *)

val ppVar = Parser.ppString;

local
  fun term pp (Term.Var v) = ppVar pp v
    | term pp (Term.Fn (c,[])) = Parser.addString pp c
    | term pp (Term.Fn (f,tms)) =
      (Parser.beginBlock pp Parser.Inconsistent 2;
       Parser.addString pp (f ^ "(");
       Parser.ppSequence "," term pp tms;
       Parser.addString pp ")";
       Parser.endBlock pp);
in
  fun ppTerm pp tm =
      (Parser.beginBlock pp Parser.Inconsistent 0;
       term pp tm;
       Parser.endBlock pp);
end;

fun ppAtom pp atm = ppTerm pp (Term.Fn atm);

local
  open Formula;

  fun fof pp (fm as And _) = assoc_binary pp ("&", stripConj fm)
    | fof pp (fm as Or _) = assoc_binary pp ("|", stripDisj fm)
    | fof pp (Imp a_b) = nonassoc_binary pp ("=>",a_b)
    | fof pp (Iff a_b) = nonassoc_binary pp ("<=>",a_b)
    | fof pp fm = unitary pp fm

  and nonassoc_binary pp (s,a_b) =
      Parser.ppBinop (" " ^ s) unitary unitary pp a_b

  and assoc_binary pp (s,l) = Parser.ppSequence (" " ^ s) unitary pp l

  and unitary pp fm =
      if isForall fm then quantified pp ("!", stripForall fm)
      else if isExists fm then quantified pp ("?", stripExists fm)
      else if atom pp fm then ()
      else if isNeg fm then
        let
          fun pr () = (Parser.addString pp "~"; Parser.addBreak pp (1,0))
          val (n,fm) = Formula.stripNeg fm
        in
          Parser.beginBlock pp Parser.Inconsistent 2;
          funpow n pr ();
          unitary pp fm;
          Parser.endBlock pp
        end
      else
        (Parser.beginBlock pp Parser.Inconsistent 1;
         Parser.addString pp "(";
         fof pp fm;
         Parser.addString pp ")";
         Parser.endBlock pp)

  and quantified pp (q,(vs,fm)) =
      (Parser.beginBlock pp Parser.Inconsistent 2;
       Parser.addString pp (q ^ " ");
       Parser.beginBlock pp Parser.Inconsistent (String.size q);
       Parser.addString pp "[";
       Parser.ppSequence "," ppVar pp vs;
       Parser.addString pp "] :";
       Parser.endBlock pp;
       Parser.addBreak pp (1,0);
       unitary pp fm;
       Parser.endBlock pp)
      
  and atom pp True = (Parser.addString pp "$true"; true)
    | atom pp False = (Parser.addString pp "$false"; true)
    | atom pp fm =
      case total destEq fm of
        SOME a_b => (Parser.ppBinop " =" ppTerm ppTerm pp a_b; true)
      | NONE =>
        case total destNeq fm of
          SOME a_b => (Parser.ppBinop " !=" ppTerm ppTerm pp a_b; true)
        | NONE => case fm of Atom atm => (ppAtom pp atm; true) | _ => false;
in
  fun ppFof pp fm =
      (Parser.beginBlock pp Parser.Inconsistent 0;
       fof pp fm;
       Parser.endBlock pp);
end;

(* ------------------------------------------------------------------------- *)
(* TPTP clauses.                                                             *)
(* ------------------------------------------------------------------------- *)

type clause = literal list;

val clauseFunctions =
    let
      fun funcs (lit,acc) = NameAritySet.union (literalFunctions lit) acc
    in
      foldl funcs NameAritySet.empty
    end;

val clauseRelations =
    let
      fun rels (lit,acc) =
          case literalRelation lit of
            NONE => acc
          | SOME r => NameAritySet.add acc r
    in
      foldl rels NameAritySet.empty
    end;

val clauseFreeVars =
    let
      fun fvs (lit,acc) = NameSet.union (literalFreeVars lit) acc
    in
      foldl fvs NameSet.empty
    end;

fun clauseSubst sub lits = map (literalSubst sub) lits;

fun mapClause maps lits = map (mapLiteral maps) lits;

fun clauseToFormula lits = Formula.listMkDisj (map literalToFormula lits);

fun clauseFromFormula fm = map literalFromFormula (Formula.stripDisj fm);

fun clauseFromLiteralSet cl =
    clauseFromFormula
      (Formula.listMkDisj (LiteralSet.transform Literal.toFormula cl));

fun clauseFromThm th = clauseFromLiteralSet (Thm.clause th);

val ppClause = Parser.ppMap clauseToFormula ppFof;

(* ------------------------------------------------------------------------- *)
(* TPTP formulas.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    CnfFormula of {name : string, role : string, clause : clause}
  | FofFormula of {name : string, role : string, formula : Formula.formula};

fun destCnfFormula (CnfFormula x) = x
  | destCnfFormula _ = raise Error "destCnfFormula";

val isCnfFormula = can destCnfFormula;

fun destFofFormula (FofFormula x) = x
  | destFofFormula _ = raise Error "destFofFormula";

val isFofFormula = can destFofFormula;

fun formulaFunctions (CnfFormula {clause,...}) = clauseFunctions clause
  | formulaFunctions (FofFormula {formula,...}) = Formula.functions formula;

fun formulaRelations (CnfFormula {clause,...}) = clauseRelations clause
  | formulaRelations (FofFormula {formula,...}) = Formula.relations formula;

fun formulaFreeVars (CnfFormula {clause,...}) = clauseFreeVars clause
  | formulaFreeVars (FofFormula {formula,...}) = Formula.freeVars formula;

fun mapFormula maps (CnfFormula {name,role,clause}) =
    CnfFormula {name = name, role = role, clause = mapClause maps clause}
  | mapFormula maps (FofFormula {name,role,formula}) =
    FofFormula {name = name, role = role, formula = mapFof maps formula};

val formulasFunctions =
    let
      fun funcs (fm,acc) = NameAritySet.union (formulaFunctions fm) acc
    in
      foldl funcs NameAritySet.empty
    end;

val formulasRelations =
    let
      fun rels (fm,acc) = NameAritySet.union (formulaRelations fm) acc
    in
      foldl rels NameAritySet.empty
    end;

fun formulaIsConjecture (CnfFormula {role,...}) = role = ROLE_NEGATED_CONJECTURE
  | formulaIsConjecture (FofFormula {role,...}) = role = ROLE_CONJECTURE;

local
  open Parser;

  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  datatype token =
      AlphaNum of string
    | Punct of char
    | Quote of string;

  fun isAlphaNum #"_" = true
    | isAlphaNum c = Char.isAlphaNum c;

  local
    val alphaNumToken = atLeastOne (some isAlphaNum) >> (AlphaNum o implode);

    val punctToken =
        let
          val punctChars = "<>=-*+/\\?@|!$%&#^:;~()[]{}.,"
        in
          some (Char.contains punctChars) >> Punct
        end;

    val quoteToken =
        let
          val escapeParser =
              exact #"'" >> singleton ||
              exact #"\\" >> singleton

          fun stopOn #"'" = true
            | stopOn #"\n" = true
            | stopOn _ = false

          val quotedParser =
              exact #"\\" ++ escapeParser >> op:: ||
              some (not o stopOn) >> singleton
        in
          exact #"'" ++ many quotedParser ++ exact #"'" >>
          (fn (_,(l,_)) => Quote (implode (List.concat l)))
        end;

    val lexToken = alphaNumToken || punctToken || quoteToken;

    val space = many (some Char.isSpace) >> K ();
  in
    val lexer = (space ++ lexToken ++ space) >> (fn ((),(tok,())) => tok);
  end;

  fun someAlphaNum p =
      maybe (fn AlphaNum s => if p s then SOME s else NONE | _ => NONE);

  fun alphaNumParser s = someAlphaNum (equal s) >> K ();

  fun isLower s = Char.isLower (String.sub (s,0));

  val lowerParser = someAlphaNum isLower;

  val upperParser = someAlphaNum (fn s => Char.isUpper (String.sub (s,0)));

  val stringParser = lowerParser || upperParser;

  val numberParser = someAlphaNum (List.all Char.isDigit o explode);

  fun somePunct p =
      maybe (fn Punct c => if p c then SOME c else NONE | _ => NONE);

  fun punctParser c = somePunct (equal c) >> K ();

  fun quoteParser p =
      let
        fun q s = if p s then s else "'" ^ s ^ "'"
      in
        maybe (fn Quote s => SOME (q s) | _ => NONE)
      end;

  local
    fun f [] = raise Bug "symbolParser"
      | f [x] = x
      | f (h :: t) = (h ++ f t) >> K ();
  in
    fun symbolParser s = f (map punctParser (explode s));
  end;

  val definedParser =
      punctParser #"$" ++ someAlphaNum (K true) >> (fn ((),s) => "$" ^ s);

  val systemParser =
      punctParser #"$" ++ punctParser #"$" ++ someAlphaNum (K true) >>
      (fn ((),((),s)) => "$$" ^ s);

  val nameParser = stringParser || numberParser || quoteParser (K false);

  val roleParser = lowerParser;

  local
    fun isProposition s = isHdTlString Char.isLower isAlphaNum s;
  in
    val propositionParser =
        someAlphaNum isProposition ||
        definedParser || systemParser || quoteParser isProposition;
  end;

  local
    fun isFunction s = isHdTlString Char.isLower isAlphaNum s;
  in
    val functionParser =
        someAlphaNum isFunction ||
        definedParser || systemParser || quoteParser isFunction;
  end;

  local
    fun isConstant s =
        isHdTlString Char.isLower isAlphaNum s orelse
        isHdTlString Char.isDigit Char.isDigit s;
  in
    val constantParser =
        someAlphaNum isConstant ||
        definedParser || systemParser || quoteParser isConstant;
  end;

  val varParser = upperParser;

  val varListParser =
      (punctParser #"[" ++ varParser ++
       many ((punctParser #"," ++ varParser) >> snd) ++
       punctParser #"]") >>
      (fn ((),(h,(t,()))) => h :: t);

  fun termParser input =
      ((functionArgumentsParser >> Term.Fn) ||
       nonFunctionArgumentsTermParser) input

  and functionArgumentsParser input =
      ((functionParser ++ punctParser #"(" ++ termParser ++
        many ((punctParser #"," ++ termParser) >> snd) ++
        punctParser #")") >>
       (fn (f,((),(t,(ts,())))) => (f, t :: ts))) input

  and nonFunctionArgumentsTermParser input =
      ((varParser >> Term.Var) ||
       (constantParser >> (fn n => Term.Fn (n,[])))) input

  val binaryAtomParser =
      ((punctParser #"=" ++ termParser) >>
       (fn ((),r) => fn l => Literal.mkEq (l,r))) ||
      ((symbolParser "!=" ++ termParser) >>
       (fn ((),r) => fn l => Literal.mkNeq (l,r)));

  val maybeBinaryAtomParser =
      optional binaryAtomParser >>
      (fn SOME f => (fn a => f (Term.Fn a))
        | NONE => (fn a => (true,a)));

  val literalAtomParser =
      ((functionArgumentsParser ++ maybeBinaryAtomParser) >>
       (fn (a,f) => f a)) ||
      ((nonFunctionArgumentsTermParser ++ binaryAtomParser) >>
       (fn (a,f) => f a)) ||
      (propositionParser >>
       (fn n => (true,(n,[]))));

  val atomParser =
      literalAtomParser >>
      (fn (pol,("$true",[])) => Boolean pol
        | (pol,("$false",[])) => Boolean (not pol)
        | (pol,("$equal",[a,b])) => Literal (pol, Atom.mkEq (a,b))
        | lit => Literal lit);

  val literalParser =
      ((punctParser #"~" ++ atomParser) >> (negate o snd)) ||
      atomParser;

  val disjunctionParser =
      (literalParser ++ many ((punctParser #"|" ++ literalParser) >> snd)) >>
      (fn (h,t) => h :: t);

  val clauseParser =
      ((punctParser #"(" ++ disjunctionParser ++ punctParser #")") >>
       (fn ((),(c,())) => c)) ||
      disjunctionParser;

(*
  An exact transcription of the fof_formula syntax from

    TPTP-v3.2.0/Documents/SyntaxBNF,

  fun fofFormulaParser input =
      (binaryFormulaParser || unitaryFormulaParser) input
  
  and binaryFormulaParser input =
      (nonAssocBinaryFormulaParser || assocBinaryFormulaParser) input

  and nonAssocBinaryFormulaParser input =
      ((unitaryFormulaParser ++ binaryConnectiveParser ++
        unitaryFormulaParser) >>
       (fn (f,(c,g)) => c (f,g))) input

  and binaryConnectiveParser input =
      ((symbolParser "<=>" >> K Formula.Iff) ||
       (symbolParser "=>" >> K Formula.Imp) ||
       (symbolParser "<=" >> K (fn (f,g) => Formula.Imp (g,f))) ||
       (symbolParser "<~>" >> K (Formula.Not o Formula.Iff)) ||
       (symbolParser "~|" >> K (Formula.Not o Formula.Or)) ||
       (symbolParser "~&" >> K (Formula.Not o Formula.And))) input

  and assocBinaryFormulaParser input =
      (orFormulaParser || andFormulaParser) input

  and orFormulaParser input =
      ((unitaryFormulaParser ++
        atLeastOne ((punctParser #"|" ++ unitaryFormulaParser) >> snd)) >>
       (fn (f,fs) => Formula.listMkDisj (f :: fs))) input

  and andFormulaParser input =
      ((unitaryFormulaParser ++
        atLeastOne ((punctParser #"&" ++ unitaryFormulaParser) >> snd)) >>
       (fn (f,fs) => Formula.listMkConj (f :: fs))) input

  and unitaryFormulaParser input =
      (quantifiedFormulaParser ||
       unaryFormulaParser ||
       ((punctParser #"(" ++ fofFormulaParser ++ punctParser #")") >>
        (fn ((),(f,())) => f)) ||
       (atomParser >>
        (fn Boolean b => Formula.mkBoolean b
          | Literal l => Literal.toFormula l))) input

  and quantifiedFormulaParser input =
      ((quantifierParser ++ varListParser ++ punctParser #":" ++
        unitaryFormulaParser) >>
       (fn (q,(v,((),f))) => q (v,f))) input

  and quantifierParser input =
      ((punctParser #"!" >> K Formula.listMkForall) ||
       (punctParser #"?" >> K Formula.listMkExists)) input

  and unaryFormulaParser input =
      ((unaryConnectiveParser ++ unitaryFormulaParser) >>
       (fn (c,f) => c f)) input

  and unaryConnectiveParser input =
      (punctParser #"~" >> K Formula.Not) input;
*)

(*
  This version is supposed to be equivalent to the spec version above,
  but uses closures to avoid reparsing prefixes.
*)

  fun fofFormulaParser input =
      ((unitaryFormulaParser ++ optional binaryFormulaParser) >>
       (fn (f,NONE) => f | (f, SOME t) => t f)) input
  
  and binaryFormulaParser input =
      (nonAssocBinaryFormulaParser || assocBinaryFormulaParser) input

  and nonAssocBinaryFormulaParser input =
      ((binaryConnectiveParser ++ unitaryFormulaParser) >>
       (fn (c,g) => fn f => c (f,g))) input

  and binaryConnectiveParser input =
      ((symbolParser "<=>" >> K Formula.Iff) ||
       (symbolParser "=>" >> K Formula.Imp) ||
       (symbolParser "<=" >> K (fn (f,g) => Formula.Imp (g,f))) ||
       (symbolParser "<~>" >> K (Formula.Not o Formula.Iff)) ||
       (symbolParser "~|" >> K (Formula.Not o Formula.Or)) ||
       (symbolParser "~&" >> K (Formula.Not o Formula.And))) input

  and assocBinaryFormulaParser input =
      (orFormulaParser || andFormulaParser) input

  and orFormulaParser input =
      (atLeastOne ((punctParser #"|" ++ unitaryFormulaParser) >> snd) >>
       (fn fs => fn f => Formula.listMkDisj (f :: fs))) input

  and andFormulaParser input =
      (atLeastOne ((punctParser #"&" ++ unitaryFormulaParser) >> snd) >>
       (fn fs => fn f => Formula.listMkConj (f :: fs))) input

  and unitaryFormulaParser input =
      (quantifiedFormulaParser ||
       unaryFormulaParser ||
       ((punctParser #"(" ++ fofFormulaParser ++ punctParser #")") >>
        (fn ((),(f,())) => f)) ||
       (atomParser >>
        (fn Boolean b => Formula.mkBoolean b
          | Literal l => Literal.toFormula l))) input

  and quantifiedFormulaParser input =
      ((quantifierParser ++ varListParser ++ punctParser #":" ++
        unitaryFormulaParser) >>
       (fn (q,(v,((),f))) => q (v,f))) input

  and quantifierParser input =
      ((punctParser #"!" >> K Formula.listMkForall) ||
       (punctParser #"?" >> K Formula.listMkExists)) input

  and unaryFormulaParser input =
      ((unaryConnectiveParser ++ unitaryFormulaParser) >>
       (fn (c,f) => c f)) input

  and unaryConnectiveParser input =
      (punctParser #"~" >> K Formula.Not) input;

  val cnfParser =
      (alphaNumParser "cnf" ++ punctParser #"(" ++
       nameParser ++ punctParser #"," ++
       roleParser ++ punctParser #"," ++
       clauseParser ++ punctParser #")" ++
       punctParser #".") >>
      (fn ((),((),(n,((),(r,((),(c,((),())))))))) =>
          CnfFormula {name = n, role = r, clause = c});

  val fofParser =
      (alphaNumParser "fof" ++ punctParser #"(" ++
       nameParser ++ punctParser #"," ++
       roleParser ++ punctParser #"," ++
       fofFormulaParser ++ punctParser #")" ++
       punctParser #".") >>
      (fn ((),((),(n,((),(r,((),(f,((),())))))))) =>
          FofFormula {name = n, role = r, formula = f});

  val formulaParser = cnfParser || fofParser;

  fun parseChars parser chars =
      let
        val tokens = Parser.everything (lexer >> singleton) chars
      in
        Parser.everything (parser >> singleton) tokens
      end;

  fun canParseString parser s =
      let
        val chars = Stream.fromString s
      in
        case Stream.toList (parseChars parser chars) of
          [_] => true
        | _ => false
      end
      handle NoParse => false;
in
  val parseFormula = parseChars formulaParser;

  val isTptpRelation = canParseString functionParser
  and isTptpProposition = canParseString propositionParser
  and isTptpFunction = canParseString functionParser
  and isTptpConstant = canParseString constantParser;
end;

fun formulaFromString s =
    case Stream.toList (parseFormula (Stream.fromList (explode s))) of
      [fm] => fm
    | _ => raise Parser.NoParse;

local
  local
    fun explodeAlpha s = List.filter Char.isAlpha (explode s);
  in
    fun normTptpName s n =
        case explodeAlpha n of
          [] => s
        | c :: cs => implode (Char.toLower c :: cs);

    fun normTptpVar s n =
        case explodeAlpha n of
          [] => s
        | c :: cs => implode (Char.toUpper c :: cs);
  end;

  fun normTptpFunc (n,0) = if isTptpConstant n then n else normTptpName "c" n
    | normTptpFunc (n,_) = if isTptpFunction n then n else normTptpName "f" n;

  fun normTptpRel (n,0) = if isTptpProposition n then n else normTptpName "p" n
    | normTptpRel (n,_) = if isTptpRelation n then n else normTptpName "r" n;

  fun mkMap set norm mapping =
      let
        val mapping = mappingToTptp mapping

        fun mk (n_r,(a,m)) =
            case NameArityMap.peek mapping n_r of
              SOME t => (a, NameArityMap.insert m (n_r,t))
            | NONE =>
              let
                val t = norm n_r
                val (n,_) = n_r
                val t = if t = n then n else Term.variantNum a t
              in
                (NameSet.add a t, NameArityMap.insert m (n_r,t))
              end

        val avoid =
            let
              fun mk ((n,r),s) =
                  let
                    val n = Option.getOpt (NameArityMap.peek mapping (n,r), n)
                  in
                    NameSet.add s n
                  end
            in
              NameAritySet.foldl mk NameSet.empty set
            end
      in
        snd (NameAritySet.foldl mk (avoid, NameArityMap.new ()) set)
      end;

  fun mkTptpVar a v = Term.variantNum a (normTptpVar "V" v);

  fun isTptpVar v = mkTptpVar NameSet.empty v = v;

  fun alphaFormula fm =
      let
        fun addVar v a s =
            let
              val v' = mkTptpVar a v
              val a = NameSet.add a v'
              and s = if v = v' then s else Subst.insert s (v, Term.Var v')
            in
              (v',(a,s))
            end

        fun initVar (v,(a,s)) = snd (addVar v a s)

        open Formula

        fun alpha _ _ True = True
          | alpha _ _ False = False
          | alpha _ s (Atom atm) = Atom (Atom.subst s atm)
          | alpha a s (Not p) = Not (alpha a s p)
          | alpha a s (And (p,q)) = And (alpha a s p, alpha a s q)
          | alpha a s (Or (p,q)) = Or (alpha a s p, alpha a s q)
          | alpha a s (Imp (p,q)) = Imp (alpha a s p, alpha a s q)
          | alpha a s (Iff (p,q)) = Iff (alpha a s p, alpha a s q)
          | alpha a s (Forall (v,p)) =
            let val (v,(a,s)) = addVar v a s in Forall (v, alpha a s p) end
          | alpha a s (Exists (v,p)) =
            let val (v,(a,s)) = addVar v a s in Exists (v, alpha a s p) end

        val fvs = formulaFreeVars fm
        val (avoid,fvs) = NameSet.partition isTptpVar fvs
        val (avoid,sub) = NameSet.foldl initVar (avoid,Subst.empty) fvs
(*TRACE5
        val () = Parser.ppTrace Subst.pp "Tptp.alpha: sub" sub
*)
      in
        case fm of
          CnfFormula {name,role,clause} =>
          CnfFormula {name = name, role = role, clause = clauseSubst sub clause}
        | FofFormula {name,role,formula} =>
          FofFormula {name = name, role = role, formula = alpha avoid sub formula}
      end;

  fun formulaToTptp maps fm = alphaFormula (mapFormula maps fm);
in
  fun formulasToTptp formulas =
      let
        val funcs = formulasFunctions formulas
        and rels = formulasRelations formulas
                   
        val functionMap = mkMap funcs normTptpFunc (!functionMapping)
        and relationMap = mkMap rels normTptpRel (!relationMapping)

        val maps = {functionMap = functionMap, relationMap = relationMap}
      in
        map (formulaToTptp maps) formulas
      end;
end;

fun formulasFromTptp formulas =
    let
      val functionMap = mappingFromTptp (!functionMapping)
      and relationMap = mappingFromTptp (!relationMapping)
                        
      val maps = {functionMap = functionMap, relationMap = relationMap}
    in
      map (mapFormula maps) formulas
    end;

local
  fun ppGen ppX pp (gen,name,role,x) =
      (Parser.beginBlock pp Parser.Inconsistent (size gen + 1);
       Parser.addString pp (gen ^ "(" ^ name ^ ",");
       Parser.addBreak pp (1,0);
       Parser.addString pp (role ^ ",");
       Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Consistent 1;
       Parser.addString pp "(";
       ppX pp x;
       Parser.addString pp ")";
       Parser.endBlock pp;
       Parser.addString pp ").";
       Parser.endBlock pp);
in
  fun ppFormula pp (CnfFormula {name,role,clause}) =
      ppGen ppClause pp ("cnf",name,role,clause)
    | ppFormula pp (FofFormula {name,role,formula}) =
      ppGen ppFof pp ("fof",name,role,formula);
end;

val formulaToString = Parser.toString ppFormula;

(* ------------------------------------------------------------------------- *)
(* TPTP problems.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype goal =
    Cnf of Problem.problem
  | Fof of Formula.formula;

type problem = {comments : string list, formulas : formula list};

local
  fun stripComments acc strm =
      case strm of
        Stream.NIL => (rev acc, Stream.NIL)
      | Stream.CONS (line,rest) =>
        case total destComment line of
          SOME s => stripComments (s :: acc) (rest ())
        | NONE => (rev acc, Stream.filter (not o isComment) strm);
in
  fun read {filename} =
      let
        val lines = Stream.fromTextFile {filename = filename}

        val lines = Stream.map chomp lines

        val (comments,lines) = stripComments [] lines

        val chars = Stream.concat (Stream.map Stream.fromString lines)

        val formulas = Stream.toList (parseFormula chars)

        val formulas = formulasFromTptp formulas
      in
        {comments = comments, formulas = formulas}
      end;
end;

(* Quick testing
installPP Term.pp;
installPP Formula.pp;
val () = Term.isVarName := (fn s => Char.isUpper (String.sub (s,0)));
val TPTP_DIR = "/Users/Joe/ptr/tptp/tptp/";
val num1 = read {filename = TPTP_DIR ^ "NUM/NUM001-1.tptp"};
val lcl9 = read {filename = TPTP_DIR ^ "LCL/LCL009-1.tptp"};
val set11 = read {filename = TPTP_DIR ^ "SET/SET011+3.tptp"};
val swc128 = read {filename = TPTP_DIR ^ "SWC/SWC128-1.tptp"};
*)

local
  fun mkCommentLine comment = mkComment comment ^ "\n";

  fun formulaStream [] () = Stream.NIL
    | formulaStream (h :: t) () =
      Stream.CONS ("\n" ^ formulaToString h, formulaStream t);
in
  fun write {filename} {comments,formulas} =
      Stream.toTextFile
        {filename = filename}
        (Stream.append
           (Stream.map mkCommentLine (Stream.fromList comments))
           (formulaStream (formulasToTptp formulas)));
end;

(* ------------------------------------------------------------------------- *)
(* Converting TPTP problems to goal formulas.                                *)
(* ------------------------------------------------------------------------- *)

fun isCnfProblem ({formulas,...} : problem) =
    let
      val cnf = List.exists isCnfFormula formulas
      and fof = List.exists isFofFormula formulas
    in
      case (cnf,fof) of
        (false,false) => raise Error "TPTP problem has no formulas"
      | (true,true) => raise Error "TPTP problem has both cnf and fof formulas"
      | (cnf,_) => cnf
    end;

fun hasConjecture ({formulas,...} : problem) =
    List.exists formulaIsConjecture formulas;

local
  fun cnfFormulaToClause (CnfFormula {clause,...}) =
      if mem (Boolean true) clause then NONE
      else
        let
          val lits = List.mapPartial (total destLiteral) clause
        in
          SOME (LiteralSet.fromList lits)
        end
    | cnfFormulaToClause (FofFormula _) = raise Bug "cnfFormulaToClause";

  fun fofFormulaToGoal (FofFormula {formula,role,...}, {axioms,goals}) =
      let
        val fm = Formula.generalize formula
      in
        if role = ROLE_CONJECTURE then
          {axioms = axioms, goals = fm :: goals}
        else
          {axioms = fm :: axioms, goals = goals}
      end
    | fofFormulaToGoal (CnfFormula _, _) = raise Bug "fofFormulaToGoal";
in
  fun toGoal (prob as {formulas,...}) =
      if isCnfProblem prob then
        Cnf (List.mapPartial cnfFormulaToClause formulas)
      else
        Fof
        let
          val axioms_goals = {axioms = [], goals = []}
          val axioms_goals = List.foldl fofFormulaToGoal axioms_goals formulas
        in
          case axioms_goals of
            {axioms, goals = []} =>
            Formula.Imp (Formula.listMkConj axioms, Formula.False)
          | {axioms = [], goals} => Formula.listMkConj goals
          | {axioms,goals} =>
            Formula.Imp (Formula.listMkConj axioms, Formula.listMkConj goals)
        end;
end;

local
  fun fromClause cl n =
      let
        val name = "clause_" ^ Int.toString n
        val role = ROLE_NEGATED_CONJECTURE
        val clause = clauseFromLiteralSet cl
      in
        (CnfFormula {name = name, role = role, clause = clause}, n + 1)
      end;
in
  fun fromProblem prob =
      let
        val comments = []
        and (formulas,_) = maps fromClause prob 0
      in
        {comments = comments, formulas = formulas}
      end;
end;

local
  fun refute cls =
      let
        val res = Resolution.new Resolution.default (map Thm.axiom cls)
      in
        case Resolution.loop res of
          Resolution.Contradiction _ => true
        | Resolution.Satisfiable _ => false
      end;
in
  fun prove filename =
      let
        val tptp = read filename
        val problems =
            case toGoal tptp of
              Cnf prob => [prob]
            | Fof goal => Problem.fromGoal goal
      in
        List.all refute problems
      end;
end;

(* ------------------------------------------------------------------------- *)
(* TSTP proofs.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun ppAtomInfo pp atm =
      case total Atom.destEq atm of
        SOME (a,b) => ppAtom pp ("$equal",[a,b])
      | NONE => ppAtom pp atm;

  fun ppLiteralInfo pp (pol,atm) =
      if pol then ppAtomInfo pp atm
      else
        (Parser.beginBlock pp Parser.Inconsistent 2;
         Parser.addString pp "~";
         Parser.addBreak pp (1,0);
         ppAtomInfo pp atm;
         Parser.endBlock pp);

  val ppAssumeInfo = Parser.ppBracket "(" ")" ppAtomInfo;

  val ppSubstInfo =
      Parser.ppMap
        Subst.toList
        (Parser.ppSequence ","
           (Parser.ppBracket "[" "]"
              (Parser.ppBinop "," ppVar (Parser.ppBracket "(" ")" ppTerm))));

  val ppResolveInfo = Parser.ppBracket "(" ")" ppAtomInfo;

  val ppReflInfo = Parser.ppBracket "(" ")" ppTerm;
        
  fun ppEqualityInfo pp (lit,path,res) =
      (Parser.ppBracket "(" ")" ppLiteralInfo pp lit;
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Term.ppPath pp path;
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBracket "(" ")" ppTerm pp res);

  fun ppInfInfo pp inf =
      case inf of
        Proof.Axiom _ => raise Bug "ppInfInfo"
      | Proof.Assume atm => ppAssumeInfo pp atm
      | Proof.Subst (sub,_) => ppSubstInfo pp sub
      | Proof.Resolve (res,_,_) => ppResolveInfo pp res
      | Proof.Refl tm => ppReflInfo pp tm
      | Proof.Equality x => ppEqualityInfo pp x;
in
  fun ppProof p prf =
      let
        fun thmString n = Int.toString n
                          
        val prf = enumerate prf

        fun ppThm p th =
            let
              val cl = Thm.clause th

              fun pred (_,(th',_)) = LiteralSet.equal (Thm.clause th') cl
            in
              case List.find pred prf of
                NONE => Parser.addString p "(?)"
              | SOME (n,_) => Parser.addString p (thmString n)
            end

        fun ppInf p inf =
            let
              val name = Thm.inferenceTypeToString (Proof.inferenceType inf)
              val name = String.map Char.toLower name
            in
              Parser.addString p (name ^ ",");
              Parser.addBreak p (1,0);
              Parser.ppBracket "[" "]" ppInfInfo p inf;
              case Proof.parents inf of
                [] => ()
              | ths =>
                (Parser.addString p ",";
                 Parser.addBreak p (1,0);
                 Parser.ppList ppThm p ths)
            end
              
        fun ppTaut p inf =
            (Parser.addString p "tautology,";
             Parser.addBreak p (1,0);
             Parser.ppBracket "[" "]" ppInf p inf)
             
        fun ppStepInfo p (n,(th,inf)) =
            let
              val is_axiom = case inf of Proof.Axiom _ => true | _ => false
              val name = thmString n
              val role =
                  if is_axiom then "axiom"
                  else if Thm.isContradiction th then "theorem"
                  else "plain"
              val cl = clauseFromThm th
            in
              Parser.addString p (name ^ ",");
              Parser.addBreak p (1,0);
              Parser.addString p (role ^ ",");
              Parser.addBreak p (1,0);
              Parser.ppBracket "(" ")" ppClause p cl;
              if is_axiom then ()
              else
                let
                  val is_tautology = null (Proof.parents inf)
                in
                  Parser.addString p ",";
                  Parser.addBreak p (1,0);
                  if is_tautology then
                    Parser.ppBracket "introduced(" ")" ppTaut p inf
                  else
                    Parser.ppBracket "inference(" ")" ppInf p inf
                end
            end

        fun ppStep p step =
            (Parser.ppBracket "cnf(" ")" ppStepInfo p step;
             Parser.addString p ".";
             Parser.addNewline p)
      in
        Parser.beginBlock p Parser.Consistent 0;
        app (ppStep p) prf;
        Parser.endBlock p
      end
(*DEBUG
      handle Error err => raise Bug ("Tptp.ppProof: shouldn't fail:\n" ^ err);
*)
end;

val proofToString = Parser.toString ppProof;

end
