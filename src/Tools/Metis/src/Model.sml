(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* Copyright (c) 2003 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Model :> Model =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

val maxSpace = 1000;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val multInt =
    case Int.maxInt of
      NONE => (fn x => fn y => SOME (x * y))
    | SOME m =>
      let
        val m = Real.floor (Math.sqrt (Real.fromInt m))
      in
        fn x => fn y => if x <= m andalso y <= m then SOME (x * y) else NONE
      end;

local
  fun iexp x y acc =
      if y mod 2 = 0 then iexp' x y acc
      else
        case multInt acc x of
          SOME acc => iexp' x y acc
        | NONE => NONE

  and iexp' x y acc =
      if y = 1 then SOME acc
      else
        let
          val y = y div 2
        in
          case multInt x x of
            SOME x => iexp x y acc
          | NONE => NONE
        end;
in
  fun expInt x y =
      if y <= 1 then
        if y = 0 then SOME 1
        else if y = 1 then SOME x
        else raise Bug "expInt: negative exponent"
      else if x <= 1 then
        if 0 <= x then SOME x
        else raise Bug "expInt: negative exponand"
      else iexp x y 1;
end;

fun boolToInt true = 1
  | boolToInt false = 0;

fun intToBool 1 = true
  | intToBool 0 = false
  | intToBool _ = raise Bug "Model.intToBool";

fun minMaxInterval i j = interval i (1 + j - i);

(* ------------------------------------------------------------------------- *)
(* Model size.                                                               *)
(* ------------------------------------------------------------------------- *)

type size = {size : int};

(* ------------------------------------------------------------------------- *)
(* A model of size N has integer elements 0...N-1.                           *)
(* ------------------------------------------------------------------------- *)

type element = int;

val zeroElement = 0;

fun incrementElement {size = N} i =
    let
      val i = i + 1
    in
      if i = N then NONE else SOME i
    end;

fun elementListSpace {size = N} arity =
    case expInt N arity of
      NONE => NONE
    | s as SOME m => if m <= maxSpace then s else NONE;

fun elementListIndex {size = N} =
    let
      fun f acc elts =
          case elts of
            [] => acc
          | elt :: elts => f (N * acc + elt) elts
    in
      f 0
    end;

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* ------------------------------------------------------------------------- *)

type fixedFunction = size -> element list -> element option;

type fixedRelation = size -> element list -> bool option;

datatype fixed =
    Fixed of
      {functions : fixedFunction NameArityMap.map,
       relations : fixedRelation NameArityMap.map};

val uselessFixedFunction : fixedFunction = K (K NONE);

val uselessFixedRelation : fixedRelation = K (K NONE);

val emptyFunctions : fixedFunction NameArityMap.map = NameArityMap.new ();

val emptyRelations : fixedRelation NameArityMap.map = NameArityMap.new ();

fun fixed0 f sz elts =
    case elts of
      [] => f sz
    | _ => raise Bug "Model.fixed0: wrong arity";

fun fixed1 f sz elts =
    case elts of
      [x] => f sz x
    | _ => raise Bug "Model.fixed1: wrong arity";

fun fixed2 f sz elts =
    case elts of
      [x,y] => f sz x y
    | _ => raise Bug "Model.fixed2: wrong arity";

val emptyFixed =
    let
      val fns = emptyFunctions
      and rels = emptyRelations
    in
      Fixed
        {functions = fns,
         relations = rels}
    end;

fun peekFunctionFixed fix name_arity =
    let
      val Fixed {functions = fns, ...} = fix
    in
      NameArityMap.peek fns name_arity
    end;

fun peekRelationFixed fix name_arity =
    let
      val Fixed {relations = rels, ...} = fix
    in
      NameArityMap.peek rels name_arity
    end;

fun getFunctionFixed fix name_arity =
    case peekFunctionFixed fix name_arity of
      SOME f => f
    | NONE => uselessFixedFunction;

fun getRelationFixed fix name_arity =
    case peekRelationFixed fix name_arity of
      SOME rel => rel
    | NONE => uselessFixedRelation;

fun insertFunctionFixed fix name_arity_fn =
    let
      val Fixed {functions = fns, relations = rels} = fix

      val fns = NameArityMap.insert fns name_arity_fn
    in
      Fixed
        {functions = fns,
         relations = rels}
    end;

fun insertRelationFixed fix name_arity_rel =
    let
      val Fixed {functions = fns, relations = rels} = fix

      val rels = NameArityMap.insert rels name_arity_rel
    in
      Fixed
        {functions = fns,
         relations = rels}
    end;

local
  fun union _ = raise Bug "Model.unionFixed: nameArity clash";
in
  fun unionFixed fix1 fix2 =
      let
        val Fixed {functions = fns1, relations = rels1} = fix1
        and Fixed {functions = fns2, relations = rels2} = fix2

        val fns = NameArityMap.union union fns1 fns2

        val rels = NameArityMap.union union rels1 rels2
      in
        Fixed
          {functions = fns,
           relations = rels}
      end;
end;

val unionListFixed =
    let
      fun union (fix,acc) = unionFixed acc fix
    in
      List.foldl union emptyFixed
    end;

local
  fun hasTypeFn _ elts =
      case elts of
        [x,_] => SOME x
      | _ => raise Bug "Model.hasTypeFn: wrong arity";

  fun eqRel _ elts =
      case elts of
        [x,y] => SOME (x = y)
      | _ => raise Bug "Model.eqRel: wrong arity";
in
  val basicFixed =
      let
        val fns = NameArityMap.singleton (Term.hasTypeFunction,hasTypeFn)

        val rels = NameArityMap.singleton (Atom.eqRelation,eqRel)
      in
        Fixed
          {functions = fns,
           relations = rels}
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Renaming fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

type fixedMap =
     {functionMap : Name.name NameArityMap.map,
      relationMap : Name.name NameArityMap.map};

fun mapFixed fixMap fix =
    let
      val {functionMap = fnMap, relationMap = relMap} = fixMap
      and Fixed {functions = fns, relations = rels} = fix

      val fns = NameArityMap.compose fnMap fns

      val rels = NameArityMap.compose relMap rels
    in
      Fixed
        {functions = fns,
         relations = rels}
    end;

local
  fun mkEntry tag (na,n) = (tag,na,n);

  fun mkList tag m = List.map (mkEntry tag) (NameArityMap.toList m);

  fun ppEntry (tag,source_arity,target) =
      Print.inconsistentBlock 2
        [Print.ppString tag,
         Print.break,
         NameArity.pp source_arity,
         Print.ppString " ->",
         Print.break,
         Name.pp target];
in
  fun ppFixedMap fixMap =
      let
        val {functionMap = fnMap, relationMap = relMap} = fixMap
      in
        case mkList "function" fnMap @ mkList "relation" relMap of
          [] => Print.skip
        | entry :: entries =>
          Print.consistentBlock 0
            (ppEntry entry ::
             List.map (Print.sequence Print.newline o ppEntry) entries)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Standard fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

(* Projections *)

val projectionMin = 1
and projectionMax = 9;

val projectionList = minMaxInterval projectionMin projectionMax;

fun projectionName i =
    let
      val _ = projectionMin <= i orelse
              raise Bug "Model.projectionName: less than projectionMin"

      val _ = i <= projectionMax orelse
              raise Bug "Model.projectionName: greater than projectionMax"
    in
      Name.fromString ("project" ^ Int.toString i)
    end;

fun projectionFn i _ elts = SOME (List.nth (elts, i - 1));

fun arityProjectionFixed arity =
    let
      fun mkProj i = ((projectionName i, arity), projectionFn i)

      fun addProj i acc =
          if i > arity then acc
          else addProj (i + 1) (NameArityMap.insert acc (mkProj i))

      val fns = addProj projectionMin emptyFunctions

      val rels = emptyRelations
    in
      Fixed
        {functions = fns,
         relations = rels}
    end;

val projectionFixed =
    unionListFixed (List.map arityProjectionFixed projectionList);

(* Arithmetic *)

val numeralMin = ~100
and numeralMax = 100;

val numeralList = minMaxInterval numeralMin numeralMax;

fun numeralName i =
    let
      val _ = numeralMin <= i orelse
              raise Bug "Model.numeralName: less than numeralMin"

      val _ = i <= numeralMax orelse
              raise Bug "Model.numeralName: greater than numeralMax"

      val s = if i < 0 then "negative" ^ Int.toString (~i) else Int.toString i
    in
      Name.fromString s
    end;

val addName = Name.fromString "+"
and divName = Name.fromString "div"
and dividesName = Name.fromString "divides"
and evenName = Name.fromString "even"
and expName = Name.fromString "exp"
and geName = Name.fromString ">="
and gtName = Name.fromString ">"
and isZeroName = Name.fromString "isZero"
and leName = Name.fromString "<="
and ltName = Name.fromString "<"
and modName = Name.fromString "mod"
and multName = Name.fromString "*"
and negName = Name.fromString "~"
and oddName = Name.fromString "odd"
and preName = Name.fromString "pre"
and subName = Name.fromString "-"
and sucName = Name.fromString "suc";

local
  (* Support *)

  fun modN {size = N} x = x mod N;

  fun oneN sz = modN sz 1;

  fun multN sz (x,y) = modN sz (x * y);

  (* Functions *)

  fun numeralFn i sz = SOME (modN sz i);

  fun addFn sz x y = SOME (modN sz (x + y));

  fun divFn {size = N} x y =
      let
        val y = if y = 0 then N else y
      in
        SOME (x div y)
      end;

  fun expFn sz x y = SOME (exp (multN sz) x y (oneN sz));

  fun modFn {size = N} x y =
      let
        val y = if y = 0 then N else y
      in
        SOME (x mod y)
      end;

  fun multFn sz x y = SOME (multN sz (x,y));

  fun negFn {size = N} x = SOME (if x = 0 then 0 else N - x);

  fun preFn {size = N} x = SOME (if x = 0 then N - 1 else x - 1);

  fun subFn {size = N} x y = SOME (if x < y then N + x - y else x - y);

  fun sucFn {size = N} x = SOME (if x = N - 1 then 0 else x + 1);

  (* Relations *)

  fun dividesRel _ x y = SOME (divides x y);

  fun evenRel _ x = SOME (x mod 2 = 0);

  fun geRel _ x y = SOME (x >= y);

  fun gtRel _ x y = SOME (x > y);

  fun isZeroRel _ x = SOME (x = 0);

  fun leRel _ x y = SOME (x <= y);

  fun ltRel _ x y = SOME (x < y);

  fun oddRel _ x = SOME (x mod 2 = 1);
in
  val modularFixed =
      let
        val fns =
            NameArityMap.fromList
              (List.map (fn i => ((numeralName i,0), fixed0 (numeralFn i)))
                 numeralList @
               [((addName,2), fixed2 addFn),
                ((divName,2), fixed2 divFn),
                ((expName,2), fixed2 expFn),
                ((modName,2), fixed2 modFn),
                ((multName,2), fixed2 multFn),
                ((negName,1), fixed1 negFn),
                ((preName,1), fixed1 preFn),
                ((subName,2), fixed2 subFn),
                ((sucName,1), fixed1 sucFn)])

        val rels =
            NameArityMap.fromList
              [((dividesName,2), fixed2 dividesRel),
               ((evenName,1), fixed1 evenRel),
               ((geName,2), fixed2 geRel),
               ((gtName,2), fixed2 gtRel),
               ((isZeroName,1), fixed1 isZeroRel),
               ((leName,2), fixed2 leRel),
               ((ltName,2), fixed2 ltRel),
               ((oddName,1), fixed1 oddRel)]
      in
        Fixed
          {functions = fns,
           relations = rels}
      end;
end;

local
  (* Support *)

  fun cutN {size = N} x = if x >= N then N - 1 else x;

  fun oneN sz = cutN sz 1;

  fun multN sz (x,y) = cutN sz (x * y);

  (* Functions *)

  fun numeralFn i sz = if i < 0 then NONE else SOME (cutN sz i);

  fun addFn sz x y = SOME (cutN sz (x + y));

  fun divFn _ x y = if y = 0 then NONE else SOME (x div y);

  fun expFn sz x y = SOME (exp (multN sz) x y (oneN sz));

  fun modFn {size = N} x y =
      if y = 0 orelse x = N - 1 then NONE else SOME (x mod y);

  fun multFn sz x y = SOME (multN sz (x,y));

  fun negFn _ x = if x = 0 then SOME 0 else NONE;

  fun preFn _ x = if x = 0 then NONE else SOME (x - 1);

  fun subFn {size = N} x y =
      if y = 0 then SOME x
      else if x = N - 1 orelse x < y then NONE
      else SOME (x - y);

  fun sucFn sz x = SOME (cutN sz (x + 1));

  (* Relations *)

  fun dividesRel {size = N} x y =
      if x = 1 orelse y = 0 then SOME true
      else if x = 0 then SOME false
      else if y = N - 1 then NONE
      else SOME (divides x y);

  fun evenRel {size = N} x =
      if x = N - 1 then NONE else SOME (x mod 2 = 0);

  fun geRel {size = N} y x =
      if x = N - 1 then if y = N - 1 then NONE else SOME false
      else if y = N - 1 then SOME true else SOME (x <= y);

  fun gtRel {size = N} y x =
      if x = N - 1 then if y = N - 1 then NONE else SOME false
      else if y = N - 1 then SOME true else SOME (x < y);

  fun isZeroRel _ x = SOME (x = 0);

  fun leRel {size = N} x y =
      if x = N - 1 then if y = N - 1 then NONE else SOME false
      else if y = N - 1 then SOME true else SOME (x <= y);

  fun ltRel {size = N} x y =
      if x = N - 1 then if y = N - 1 then NONE else SOME false
      else if y = N - 1 then SOME true else SOME (x < y);

  fun oddRel {size = N} x =
      if x = N - 1 then NONE else SOME (x mod 2 = 1);
in
  val overflowFixed =
      let
        val fns =
            NameArityMap.fromList
              (List.map (fn i => ((numeralName i,0), fixed0 (numeralFn i)))
                 numeralList @
               [((addName,2), fixed2 addFn),
                ((divName,2), fixed2 divFn),
                ((expName,2), fixed2 expFn),
                ((modName,2), fixed2 modFn),
                ((multName,2), fixed2 multFn),
                ((negName,1), fixed1 negFn),
                ((preName,1), fixed1 preFn),
                ((subName,2), fixed2 subFn),
                ((sucName,1), fixed1 sucFn)])

        val rels =
            NameArityMap.fromList
              [((dividesName,2), fixed2 dividesRel),
               ((evenName,1), fixed1 evenRel),
               ((geName,2), fixed2 geRel),
               ((gtName,2), fixed2 gtRel),
               ((isZeroName,1), fixed1 isZeroRel),
               ((leName,2), fixed2 leRel),
               ((ltName,2), fixed2 ltRel),
               ((oddName,1), fixed1 oddRel)]
      in
        Fixed
          {functions = fns,
           relations = rels}
      end;
end;

(* Sets *)

val cardName = Name.fromString "card"
and complementName = Name.fromString "complement"
and differenceName = Name.fromString "difference"
and emptyName = Name.fromString "empty"
and memberName = Name.fromString "member"
and insertName = Name.fromString "insert"
and intersectName = Name.fromString "intersect"
and singletonName = Name.fromString "singleton"
and subsetName = Name.fromString "subset"
and symmetricDifferenceName = Name.fromString "symmetricDifference"
and unionName = Name.fromString "union"
and universeName = Name.fromString "universe";

local
  (* Support *)

  fun eltN {size = N} =
      let
        fun f 0 acc = acc
          | f x acc = f (x div 2) (acc + 1)
      in
        f N ~1
      end;

  fun posN i = Word.<< (0w1, Word.fromInt i);

  fun univN sz = Word.- (posN (eltN sz), 0w1);

  fun setN sz x = Word.andb (Word.fromInt x, univN sz);

  (* Functions *)

  fun cardFn sz x =
      let
        fun f 0w0 acc = acc
          | f s acc =
            let
              val acc = if Word.andb (s,0w1) = 0w0 then acc else acc + 1
            in
              f (Word.>> (s,0w1)) acc
            end
      in
        SOME (f (setN sz x) 0)
      end;

  fun complementFn sz x = SOME (Word.toInt (Word.xorb (univN sz, setN sz x)));

  fun differenceFn sz x y =
      let
        val x = setN sz x
        and y = setN sz y
      in
        SOME (Word.toInt (Word.andb (x, Word.notb y)))
      end;

  fun emptyFn _ = SOME 0;

  fun insertFn sz x y =
      let
        val x = x mod eltN sz
        and y = setN sz y
      in
        SOME (Word.toInt (Word.orb (posN x, y)))
      end;

  fun intersectFn sz x y =
      SOME (Word.toInt (Word.andb (setN sz x, setN sz y)));

  fun singletonFn sz x =
      let
        val x = x mod eltN sz
      in
        SOME (Word.toInt (posN x))
      end;

  fun symmetricDifferenceFn sz x y =
      let
        val x = setN sz x
        and y = setN sz y
      in
        SOME (Word.toInt (Word.xorb (x,y)))
      end;

  fun unionFn sz x y =
      SOME (Word.toInt (Word.orb (setN sz x, setN sz y)));

  fun universeFn sz = SOME (Word.toInt (univN sz));

  (* Relations *)

  fun memberRel sz x y =
      let
        val x = x mod eltN sz
        and y = setN sz y
      in
        SOME (Word.andb (posN x, y) <> 0w0)
      end;

  fun subsetRel sz x y =
      let
        val x = setN sz x
        and y = setN sz y
      in
        SOME (Word.andb (x, Word.notb y) = 0w0)
      end;
in
  val setFixed =
      let
        val fns =
            NameArityMap.fromList
              [((cardName,1), fixed1 cardFn),
               ((complementName,1), fixed1 complementFn),
               ((differenceName,2), fixed2 differenceFn),
               ((emptyName,0), fixed0 emptyFn),
               ((insertName,2), fixed2 insertFn),
               ((intersectName,2), fixed2 intersectFn),
               ((singletonName,1), fixed1 singletonFn),
               ((symmetricDifferenceName,2), fixed2 symmetricDifferenceFn),
               ((unionName,2), fixed2 unionFn),
               ((universeName,0), fixed0 universeFn)]

        val rels =
            NameArityMap.fromList
              [((memberName,2), fixed2 memberRel),
               ((subsetName,2), fixed2 subsetRel)]
      in
        Fixed
          {functions = fns,
           relations = rels}
      end;
end;

(* Lists *)

val appendName = Name.fromString "@"
and consName = Name.fromString "::"
and lengthName = Name.fromString "length"
and nilName = Name.fromString "nil"
and nullName = Name.fromString "null"
and tailName = Name.fromString "tail";

local
  val baseFix =
      let
        val fix = unionFixed projectionFixed overflowFixed

        val sucFn = getFunctionFixed fix (sucName,1)

        fun suc2Fn sz _ x = sucFn sz [x]
      in
        insertFunctionFixed fix ((sucName,2), fixed2 suc2Fn)
      end;

  val fixMap =
      {functionMap = NameArityMap.fromList
                       [((appendName,2),addName),
                        ((consName,2),sucName),
                        ((lengthName,1), projectionName 1),
                        ((nilName,0), numeralName 0),
                        ((tailName,1),preName)],
       relationMap = NameArityMap.fromList
                       [((nullName,1),isZeroName)]};

in
  val listFixed = mapFixed fixMap baseFix;
end;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

datatype valuation = Valuation of element NameMap.map;

val emptyValuation = Valuation (NameMap.new ());

fun insertValuation (Valuation m) v_i = Valuation (NameMap.insert m v_i);

fun peekValuation (Valuation m) v = NameMap.peek m v;

fun constantValuation i =
    let
      fun add (v,V) = insertValuation V (v,i)
    in
      NameSet.foldl add emptyValuation
    end;

val zeroValuation = constantValuation zeroElement;

fun getValuation V v =
    case peekValuation V v of
      SOME i => i
    | NONE => raise Error "Model.getValuation: incomplete valuation";

fun randomValuation {size = N} vs =
    let
      fun f (v,V) = insertValuation V (v, Portable.randomInt N)
    in
      NameSet.foldl f emptyValuation vs
    end;

fun incrementValuation N vars =
    let
      fun inc vs V =
          case vs of
            [] => NONE
          | v :: vs =>
            let
              val (carry,i) =
                  case incrementElement N (getValuation V v) of
                    SOME i => (false,i)
                  | NONE => (true,zeroElement)

              val V = insertValuation V (v,i)
            in
              if carry then inc vs V else SOME V
            end
    in
      inc (NameSet.toList vars)
    end;

fun foldValuation N vars f =
    let
      val inc = incrementValuation N vars

      fun fold V acc =
          let
            val acc = f (V,acc)
          in
            case inc V of
              NONE => acc
            | SOME V => fold V acc
          end

      val zero = zeroValuation vars
    in
      fold zero
    end;

(* ------------------------------------------------------------------------- *)
(* A type of random finite mapping Z^n -> Z.                                 *)
(* ------------------------------------------------------------------------- *)

val UNKNOWN = ~1;

datatype table =
    ForgetfulTable
  | ArrayTable of int Array.array;

fun newTable N arity =
    case elementListSpace {size = N} arity of
      NONE => ForgetfulTable
    | SOME space => ArrayTable (Array.array (space,UNKNOWN));

local
  fun randomResult R = Portable.randomInt R;
in
  fun lookupTable N R table elts =
      case table of
        ForgetfulTable => randomResult R
      | ArrayTable a =>
        let
          val i = elementListIndex {size = N} elts

          val r = Array.sub (a,i)
        in
          if r <> UNKNOWN then r
          else
            let
              val r = randomResult R

              val () = Array.update (a,i,r)
            in
              r
            end
        end;
end;

fun updateTable N table (elts,r) =
    case table of
      ForgetfulTable => ()
    | ArrayTable a =>
      let
        val i = elementListIndex {size = N} elts

        val () = Array.update (a,i,r)
      in
        ()
      end;

(* ------------------------------------------------------------------------- *)
(* A type of random finite mappings name * arity -> Z^arity -> Z.            *)
(* ------------------------------------------------------------------------- *)

datatype tables =
    Tables of
      {domainSize : int,
       rangeSize : int,
       tableMap : table NameArityMap.map ref};

fun newTables N R =
    Tables
      {domainSize = N,
       rangeSize = R,
       tableMap = ref (NameArityMap.new ())};

fun getTables tables n_a =
    let
      val Tables {domainSize = N, rangeSize = _, tableMap = tm} = tables

      val ref m = tm
    in
      case NameArityMap.peek m n_a of
        SOME t => t
      | NONE =>
        let
          val (_,a) = n_a

          val t = newTable N a

          val m = NameArityMap.insert m (n_a,t)

          val () = tm := m
        in
          t
        end
    end;

fun lookupTables tables (n,elts) =
    let
      val Tables {domainSize = N, rangeSize = R, ...} = tables

      val a = length elts

      val table = getTables tables (n,a)
    in
      lookupTable N R table elts
    end;

fun updateTables tables ((n,elts),r) =
    let
      val Tables {domainSize = N, ...} = tables

      val a = length elts

      val table = getTables tables (n,a)
    in
      updateTable N table (elts,r)
    end;

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fixed : fixed};

datatype model =
    Model of
      {size : int,
       fixedFunctions : (element list -> element option) NameArityMap.map,
       fixedRelations : (element list -> bool option) NameArityMap.map,
       randomFunctions : tables,
       randomRelations : tables};

fun new {size = N, fixed} =
    let
      val Fixed {functions = fns, relations = rels} = fixed

      val fixFns = NameArityMap.transform (fn f => f {size = N}) fns
      and fixRels = NameArityMap.transform (fn r => r {size = N}) rels

      val rndFns = newTables N N
      and rndRels = newTables N 2
    in
      Model
        {size = N,
         fixedFunctions = fixFns,
         fixedRelations = fixRels,
         randomFunctions = rndFns,
         randomRelations = rndRels}
    end;

fun size (Model {size = N, ...}) = N;

fun peekFixedFunction M (n,elts) =
    let
      val Model {fixedFunctions = fixFns, ...} = M
    in
      case NameArityMap.peek fixFns (n, length elts) of
        NONE => NONE
      | SOME fixFn => fixFn elts
    end;

fun isFixedFunction M n_elts = Option.isSome (peekFixedFunction M n_elts);

fun peekFixedRelation M (n,elts) =
    let
      val Model {fixedRelations = fixRels, ...} = M
    in
      case NameArityMap.peek fixRels (n, length elts) of
        NONE => NONE
      | SOME fixRel => fixRel elts
    end;

fun isFixedRelation M n_elts = Option.isSome (peekFixedRelation M n_elts);

(* A default model *)

val defaultSize = 8;

val defaultFixed =
    unionListFixed
      [basicFixed,
       projectionFixed,
       modularFixed,
       setFixed,
       listFixed];

val default = {size = defaultSize, fixed = defaultFixed};

(* ------------------------------------------------------------------------- *)
(* Taking apart terms to interpret them.                                     *)
(* ------------------------------------------------------------------------- *)

fun destTerm tm =
    case tm of
      Term.Var _ => tm
    | Term.Fn f_tms =>
      case Term.stripApp tm of
        (_,[]) => tm
      | (v as Term.Var _, tms) => Term.Fn (Term.appName, v :: tms)
      | (Term.Fn (f,tms), tms') => Term.Fn (f, tms @ tms');

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

fun interpretFunction M n_elts =
    case peekFixedFunction M n_elts of
      SOME r => r
    | NONE =>
      let
        val Model {randomFunctions = rndFns, ...} = M
      in
        lookupTables rndFns n_elts
      end;

fun interpretRelation M n_elts =
    case peekFixedRelation M n_elts of
      SOME r => r
    | NONE =>
      let
        val Model {randomRelations = rndRels, ...} = M
      in
        intToBool (lookupTables rndRels n_elts)
      end;

fun interpretTerm M V =
    let
      fun interpret tm =
          case destTerm tm of
            Term.Var v => getValuation V v
          | Term.Fn (f,tms) => interpretFunction M (f, List.map interpret tms)
    in
      interpret
    end;

fun interpretAtom M V (r,tms) =
    interpretRelation M (r, List.map (interpretTerm M V) tms);

fun interpretFormula M =
    let
      val N = size M

      fun interpret V fm =
          case fm of
            Formula.True => true
          | Formula.False => false
          | Formula.Atom atm => interpretAtom M V atm
          | Formula.Not p => not (interpret V p)
          | Formula.Or (p,q) => interpret V p orelse interpret V q
          | Formula.And (p,q) => interpret V p andalso interpret V q
          | Formula.Imp (p,q) => interpret V (Formula.Or (Formula.Not p, q))
          | Formula.Iff (p,q) => interpret V p = interpret V q
          | Formula.Forall (v,p) => interpret' V p v N
          | Formula.Exists (v,p) =>
            interpret V (Formula.Not (Formula.Forall (v, Formula.Not p)))

      and interpret' V fm v i =
          i = 0 orelse
          let
            val i = i - 1
            val V' = insertValuation V (v,i)
          in
            interpret V' fm andalso interpret' V fm v i
          end
    in
      interpret
    end;

fun interpretLiteral M V (pol,atm) =
    let
      val b = interpretAtom M V atm
    in
      if pol then b else not b
    end;

fun interpretClause M V cl = LiteralSet.exists (interpretLiteral M V) cl;

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

fun check interpret {maxChecks} M fv x =
    let
      val N = size M

      fun score (V,{T,F}) =
          if interpret M V x then {T = T + 1, F = F} else {T = T, F = F + 1}

      fun randomCheck acc = score (randomValuation {size = N} fv, acc)

      val maxChecks =
          case maxChecks of
            NONE => maxChecks
          | SOME m =>
            case expInt N (NameSet.size fv) of
              SOME n => if n <= m then NONE else maxChecks
            | NONE => maxChecks
    in
      case maxChecks of
        SOME m => funpow m randomCheck {T = 0, F = 0}
      | NONE => foldValuation {size = N} fv score {T = 0, F = 0}
    end;

fun checkAtom maxChecks M atm =
    check interpretAtom maxChecks M (Atom.freeVars atm) atm;

fun checkFormula maxChecks M fm =
    check interpretFormula maxChecks M (Formula.freeVars fm) fm;

fun checkLiteral maxChecks M lit =
    check interpretLiteral maxChecks M (Literal.freeVars lit) lit;

fun checkClause maxChecks M cl =
    check interpretClause maxChecks M (LiteralSet.freeVars cl) cl;

(* ------------------------------------------------------------------------- *)
(* Updating the model.                                                       *)
(* ------------------------------------------------------------------------- *)

fun updateFunction M func_elts_elt =
    let
      val Model {randomFunctions = rndFns, ...} = M

      val () = updateTables rndFns func_elts_elt
    in
      ()
    end;

fun updateRelation M (rel_elts,pol) =
    let
      val Model {randomRelations = rndRels, ...} = M

      val () = updateTables rndRels (rel_elts, boolToInt pol)
    in
      ()
    end;

(* ------------------------------------------------------------------------- *)
(* A type of terms with interpretations embedded in the subterms.            *)
(* ------------------------------------------------------------------------- *)

datatype modelTerm =
    ModelVar
  | ModelFn of Term.functionName * modelTerm list * int list;

fun modelTerm M V =
    let
      fun modelTm tm =
          case destTerm tm of
            Term.Var v => (ModelVar, getValuation V v)
          | Term.Fn (f,tms) =>
            let
              val (tms,xs) = unzip (List.map modelTm tms)
            in
              (ModelFn (f,tms,xs), interpretFunction M (f,xs))
            end
    in
      modelTm
    end;

(* ------------------------------------------------------------------------- *)
(* Perturbing the model.                                                     *)
(* ------------------------------------------------------------------------- *)

datatype perturbation =
    FunctionPerturbation of (Term.functionName * element list) * element
  | RelationPerturbation of (Atom.relationName * element list) * bool;

fun perturb M pert =
    case pert of
      FunctionPerturbation func_elts_elt => updateFunction M func_elts_elt
    | RelationPerturbation rel_elts_pol => updateRelation M rel_elts_pol;

local
  fun pertTerm _ [] _ acc = acc
    | pertTerm M target tm acc =
      case tm of
        ModelVar => acc
      | ModelFn (func,tms,xs) =>
        let
          fun onTarget ys = mem (interpretFunction M (func,ys)) target

          val func_xs = (func,xs)

          val acc =
              if isFixedFunction M func_xs then acc
              else
                let
                  fun add (y,acc) = FunctionPerturbation (func_xs,y) :: acc
                in
                  List.foldl add acc target
                end
        in
          pertTerms M onTarget tms xs acc
        end

  and pertTerms M onTarget =
      let
        val N = size M

        fun filterElements pred =
            let
              fun filt 0 acc = acc
                | filt i acc =
                  let
                    val i = i - 1
                    val acc = if pred i then i :: acc else acc
                  in
                    filt i acc
                  end
            in
              filt N []
            end

        fun pert _ [] [] acc = acc
          | pert ys (tm :: tms) (x :: xs) acc =
            let
              fun pred y =
                  y <> x andalso onTarget (List.revAppend (ys, y :: xs))

              val target = filterElements pred

              val acc = pertTerm M target tm acc
            in
              pert (x :: ys) tms xs acc
            end
          | pert _ _ _ _ = raise Bug "Model.pertTerms.pert"
      in
        pert []
      end;

  fun pertAtom M V target (rel,tms) acc =
      let
        fun onTarget ys = interpretRelation M (rel,ys) = target

        val (tms,xs) = unzip (List.map (modelTerm M V) tms)

        val rel_xs = (rel,xs)

        val acc =
            if isFixedRelation M rel_xs then acc
            else RelationPerturbation (rel_xs,target) :: acc
      in
        pertTerms M onTarget tms xs acc
      end;

  fun pertLiteral M V ((pol,atm),acc) = pertAtom M V pol atm acc;

  fun pertClause M V cl acc = LiteralSet.foldl (pertLiteral M V) acc cl;

  fun pickPerturb M perts =
      if List.null perts then ()
      else perturb M (List.nth (perts, Portable.randomInt (length perts)));
in
  fun perturbTerm M V (tm,target) =
      pickPerturb M (pertTerm M target (fst (modelTerm M V tm)) []);

  fun perturbAtom M V (atm,target) =
      pickPerturb M (pertAtom M V target atm []);

  fun perturbLiteral M V lit = pickPerturb M (pertLiteral M V (lit,[]));

  fun perturbClause M V cl = pickPerturb M (pertClause M V cl []);
end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun pp M =
    Print.program
      [Print.ppString "Model{",
       Print.ppInt (size M),
       Print.ppString "}"];

end
