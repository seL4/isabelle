(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* Copyright (c) 2003-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Model :> Model =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun intExp x y = exp op* x y 1;

fun natFromString "" = NONE
  | natFromString "0" = SOME 0
  | natFromString s =
    case charToInt (String.sub (s,0)) of
      NONE => NONE
    | SOME 0 => NONE
    | SOME d =>
      let
        fun parse 0 _ acc = SOME acc
          | parse n i acc =
            case charToInt (String.sub (s,i)) of
              NONE => NONE
            | SOME d => parse (n - 1) (i + 1) (10 * acc + d)
      in
        parse (size s - 1) 1 d
      end;

fun projection (_,[]) = NONE
  | projection ("#1", x :: _) = SOME x
  | projection ("#2", _ :: x :: _) = SOME x
  | projection ("#3", _ :: _ :: x :: _) = SOME x
  | projection (func,args) =
    let
      val f = size func
      and n = length args

      val p =
          if f < 2 orelse n <= 3 orelse String.sub (func,0) <> #"#" then NONE
          else if f = 2 then
            (case charToInt (String.sub (func,1)) of
               NONE => NONE
             | p as SOME d => if d <= 3 then NONE else p)
          else if (n < intExp 10 (f - 2) handle Overflow => true) then NONE
          else
            (natFromString (String.extract (func,1,NONE))
             handle Overflow => NONE)
    in
      case p of
        NONE => NONE
      | SOME k => if k > n then NONE else SOME (List.nth (args, k - 1))
    end;

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* Note: a model of size N has integer elements 0...N-1.                     *)
(* ------------------------------------------------------------------------- *)

type fixedModel =
     {functions : (Term.functionName * int list) -> int option,
      relations : (Atom.relationName * int list) -> bool option};

type fixed = {size : int} -> fixedModel

fun fixedMerge fixed1 fixed2 parm =
    let
      val {functions = f1, relations = r1} = fixed1 parm
      and {functions = f2, relations = r2} = fixed2 parm

      fun functions x = case f2 x of NONE => f1 x | s => s

      fun relations x = case r2 x of NONE => r1 x | s => s
    in
      {functions = functions, relations = relations}
    end;

fun fixedMergeList [] = raise Bug "fixedMergeList: empty"
  | fixedMergeList (f :: l) = foldl (uncurry fixedMerge) f l;

fun fixedPure {size = _} =
    let
      fun functions (":",[x,_]) = SOME x
        | functions _ = NONE

      fun relations (rel,[x,y]) =
          if (rel,2) = Atom.eqRelation then SOME (x = y) else NONE
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

fun fixedBasic {size = _} =
    let
      fun functions ("id",[x]) = SOME x
        | functions ("fst",[x,_]) = SOME x
        | functions ("snd",[_,x]) = SOME x
        | functions func_args = projection func_args

      fun relations ("<>",[x,y]) = SOME (x <> y)
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

fun fixedModulo {size = N} =
    let
      fun mod_N k = k mod N

      val one = mod_N 1
                
      fun mult (x,y) = mod_N (x * y)

      fun divides_N 0 = false
        | divides_N x = N mod x = 0

      val even_N = divides_N 2

      fun functions (numeral,[]) =
          Option.map mod_N (natFromString numeral handle Overflow => NONE)
        | functions ("suc",[x]) = SOME (if x = N - 1 then 0 else x + 1)
        | functions ("pre",[x]) = SOME (if x = 0 then N - 1 else x - 1)
        | functions ("~",[x]) = SOME (if x = 0 then 0 else N - x)
        | functions ("+",[x,y]) = SOME (mod_N (x + y))
        | functions ("-",[x,y]) = SOME (if x < y then N + x - y else x - y)
        | functions ("*",[x,y]) = SOME (mult (x,y))
        | functions ("exp",[x,y]) = SOME (exp mult x y one)
        | functions ("div",[x,y]) = if divides_N y then SOME (x div y) else NONE
        | functions ("mod",[x,y]) = if divides_N y then SOME (x mod y) else NONE
        | functions _ = NONE

      fun relations ("is_0",[x]) = SOME (x = 0)
        | relations ("divides",[x,y]) =
          if x = 0 then SOME (y = 0)
          else if divides_N x then SOME (y mod x = 0) else NONE
        | relations ("even",[x]) = if even_N then SOME (x mod 2 = 0) else NONE
        | relations ("odd",[x]) = if even_N then SOME (x mod 2 = 1) else NONE
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

local
  datatype onum = ONeg | ONum of int | OInf;

  val zero = ONum 0
  and one = ONum 1
  and two = ONum 2;

  fun suc (ONum x) = ONum (x + 1)
    | suc v = v;

  fun pre (ONum 0) = ONeg
    | pre (ONum x) = ONum (x - 1)
    | pre v = v;

  fun neg ONeg = NONE
    | neg (n as ONum 0) = SOME n
    | neg _ = SOME ONeg;

  fun add ONeg ONeg = SOME ONeg
    | add ONeg (ONum y) = if y = 0 then SOME ONeg else NONE
    | add ONeg OInf = NONE
    | add (ONum x) ONeg = if x = 0 then SOME ONeg else NONE
    | add (ONum x) (ONum y) = SOME (ONum (x + y))
    | add (ONum _) OInf = SOME OInf
    | add OInf ONeg = NONE
    | add OInf (ONum _) = SOME OInf
    | add OInf OInf = SOME OInf;

  fun sub ONeg ONeg = NONE
    | sub ONeg (ONum _) = SOME ONeg
    | sub ONeg OInf = SOME ONeg
    | sub (ONum _) ONeg = NONE
    | sub (ONum x) (ONum y) = SOME (if x < y then ONeg else ONum (x - y))
    | sub (ONum _) OInf = SOME ONeg
    | sub OInf ONeg = SOME OInf
    | sub OInf (ONum y) = if y = 0 then SOME OInf else NONE
    | sub OInf OInf = NONE;

  fun mult ONeg ONeg = NONE
    | mult ONeg (ONum y) = SOME (if y = 0 then zero else ONeg)
    | mult ONeg OInf = SOME ONeg
    | mult (ONum x) ONeg = SOME (if x = 0 then zero else ONeg)
    | mult (ONum x) (ONum y) = SOME (ONum (x * y))
    | mult (ONum x) OInf = SOME (if x = 0 then zero else OInf)
    | mult OInf ONeg = SOME ONeg
    | mult OInf (ONum y) = SOME (if y = 0 then zero else OInf)
    | mult OInf OInf = SOME OInf;

  fun exp ONeg ONeg = NONE
    | exp ONeg (ONum y) =
      if y = 0 then SOME one else if y mod 2 = 0 then NONE else SOME ONeg
    | exp ONeg OInf = NONE
    | exp (ONum x) ONeg = NONE
    | exp (ONum x) (ONum y) = SOME (ONum (intExp x y) handle Overflow => OInf)
    | exp (ONum x) OInf =
      SOME (if x = 0 then zero else if x = 1 then one else OInf)
    | exp OInf ONeg = NONE
    | exp OInf (ONum y) = SOME (if y = 0 then one else OInf)
    | exp OInf OInf = SOME OInf;

  fun odiv ONeg ONeg = NONE
    | odiv ONeg (ONum y) = if y = 1 then SOME ONeg else NONE
    | odiv ONeg OInf = NONE
    | odiv (ONum _) ONeg = NONE
    | odiv (ONum x) (ONum y) = if y = 0 then NONE else SOME (ONum (x div y))
    | odiv (ONum _) OInf = SOME zero
    | odiv OInf ONeg = NONE
    | odiv OInf (ONum y) = if y = 1 then SOME OInf else NONE
    | odiv OInf OInf = NONE;

  fun omod ONeg ONeg = NONE
    | omod ONeg (ONum y) = if y = 1 then SOME zero else NONE
    | omod ONeg OInf = NONE
    | omod (ONum _) ONeg = NONE
    | omod (ONum x) (ONum y) = if y = 0 then NONE else SOME (ONum (x mod y))
    | omod (x as ONum _) OInf = SOME x
    | omod OInf ONeg = NONE
    | omod OInf (ONum y) = if y = 1 then SOME OInf else NONE
    | omod OInf OInf = NONE;

  fun le ONeg ONeg = NONE
    | le ONeg (ONum y) = SOME true
    | le ONeg OInf = SOME true
    | le (ONum _) ONeg = SOME false
    | le (ONum x) (ONum y) = SOME (x <= y)
    | le (ONum _) OInf = SOME true
    | le OInf ONeg = SOME false
    | le OInf (ONum _) = SOME false
    | le OInf OInf = NONE;

  fun lt x y = Option.map not (le y x);
  
  fun ge x y = le y x;
  
  fun gt x y = lt y x;
  
  fun divides ONeg ONeg = NONE
    | divides ONeg (ONum y) = if y = 0 then SOME true else NONE
    | divides ONeg OInf = NONE
    | divides (ONum x) ONeg =
      if x = 0 then SOME false else if x = 1 then SOME true else NONE
    | divides (ONum x) (ONum y) = SOME (Useful.divides x y)
    | divides (ONum x) OInf =
      if x = 0 then SOME false else if x = 1 then SOME true else NONE
    | divides OInf ONeg = NONE
    | divides OInf (ONum y) = SOME (y = 0)
    | divides OInf OInf = NONE;
  
  fun even n = divides two n;
  
  fun odd n = Option.map not (even n);

  fun fixedOverflow mk_onum dest_onum =
      let
        fun partial_dest_onum NONE = NONE
          | partial_dest_onum (SOME n) = dest_onum n

        fun functions (numeral,[]) =
            (case (natFromString numeral handle Overflow => NONE) of
               NONE => NONE
             | SOME n => dest_onum (ONum n))
          | functions ("suc",[x]) = dest_onum (suc (mk_onum x))
          | functions ("pre",[x]) = dest_onum (pre (mk_onum x))
          | functions ("~",[x]) = partial_dest_onum (neg (mk_onum x))
          | functions ("+",[x,y]) =
            partial_dest_onum (add (mk_onum x) (mk_onum y))
          | functions ("-",[x,y]) =
            partial_dest_onum (sub (mk_onum x) (mk_onum y))
          | functions ("*",[x,y]) =
            partial_dest_onum (mult (mk_onum x) (mk_onum y))
          | functions ("exp",[x,y]) =
            partial_dest_onum (exp (mk_onum x) (mk_onum y))
          | functions ("div",[x,y]) =
            partial_dest_onum (odiv (mk_onum x) (mk_onum y))
          | functions ("mod",[x,y]) =
            partial_dest_onum (omod (mk_onum x) (mk_onum y))
          | functions _ = NONE
  
        fun relations ("is_0",[x]) = SOME (mk_onum x = zero)
          | relations ("<=",[x,y]) = le (mk_onum x) (mk_onum y)
          | relations ("<",[x,y]) = lt (mk_onum x) (mk_onum y)
          | relations (">=",[x,y]) = ge (mk_onum x) (mk_onum y)
          | relations (">",[x,y]) = gt (mk_onum x) (mk_onum y)
          | relations ("divides",[x,y]) = divides (mk_onum x) (mk_onum y)
          | relations ("even",[x]) = even (mk_onum x)
          | relations ("odd",[x]) = odd (mk_onum x)
          | relations _ = NONE
      in
        {functions = functions, relations = relations}
      end;
in
  fun fixedOverflowNum {size = N} =
      let
        val oinf = N - 1
  
        fun mk_onum x = if x = oinf then OInf else ONum x
  
        fun dest_onum ONeg = NONE
          | dest_onum (ONum x) = SOME (if x < oinf then x else oinf)
          | dest_onum OInf = SOME oinf
      in
        fixedOverflow mk_onum dest_onum
      end;

  fun fixedOverflowInt {size = N} =
      let
        val oinf = N - 2
        val oneg = N - 1
  
        fun mk_onum x =
            if x = oneg then ONeg else if x = oinf then OInf else ONum x
  
        fun dest_onum ONeg = SOME oneg
          | dest_onum (ONum x) = SOME (if x < oinf then x else oinf)
          | dest_onum OInf = SOME oinf
      in
        fixedOverflow mk_onum dest_onum
      end;
end;

fun fixedSet {size = N} =
    let
      val M =
          let
            fun f 0 acc = acc
              | f x acc = f (x div 2) (acc + 1)
          in
            f N 0
          end

      val univ = IntSet.fromList (interval 0 M)

      val mk_set =
          let
            fun f _ s 0 = s
              | f k s x =
                let
                  val s = if x mod 2 = 0 then s else IntSet.add s k
                in
                  f (k + 1) s (x div 2)
                end
          in
            f 0 IntSet.empty
          end

      fun dest_set s =
          let
            fun f 0 x = x
              | f k x =
                let
                  val k = k - 1
                in
                  f k (if IntSet.member k s then 2 * x + 1 else 2 * x)
                end

            val x = case IntSet.findr (K true) s of NONE => 0 | SOME k => f k 1
          in
            if x < N then SOME x else NONE
          end

      fun functions ("empty",[]) = dest_set IntSet.empty
        | functions ("univ",[]) = dest_set univ
        | functions ("union",[x,y]) =
          dest_set (IntSet.union (mk_set x) (mk_set y))
        | functions ("intersect",[x,y]) =
          dest_set (IntSet.intersect (mk_set x) (mk_set y))
        | functions ("compl",[x]) =
          dest_set (IntSet.difference univ (mk_set x))
        | functions ("card",[x]) = SOME (IntSet.size (mk_set x))
        | functions _ = NONE
  
      fun relations ("in",[x,y]) = SOME (IntSet.member (x mod M) (mk_set y))
        | relations ("subset",[x,y]) =
          SOME (IntSet.subset (mk_set x) (mk_set y))
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fixed : fixed};

datatype model =
    Model of
      {size : int,
       fixed : fixedModel,
       functions : (Term.functionName * int list, int) Map.map ref,
       relations : (Atom.relationName * int list, bool) Map.map ref};

local
  fun cmp ((n1,l1),(n2,l2)) =
      case String.compare (n1,n2) of
        LESS => LESS
      | EQUAL => lexCompare Int.compare (l1,l2)
      | GREATER => GREATER;
in
  fun new {size = N, fixed} =
      Model
        {size = N,
         fixed = fixed {size = N},
         functions = ref (Map.new cmp),
         relations = ref (Map.new cmp)};
end;

fun size (Model {size = s, ...}) = s;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = int NameMap.map;

val valuationEmpty : valuation = NameMap.new ();

fun valuationRandom {size = N} vs =
    let
      fun f (v,V) = NameMap.insert V (v, Portable.randomInt N)
    in
      NameSet.foldl f valuationEmpty vs
    end;

fun valuationFold {size = N} vs f =
    let
      val vs = NameSet.toList vs

      fun inc [] _ = NONE
        | inc (v :: l) V =
          case NameMap.peek V v of
            NONE => raise Bug "Model.valuationFold"
          | SOME k =>
            let
              val k = if k = N - 1 then 0 else k + 1
              val V = NameMap.insert V (v,k)
            in
              if k = 0 then inc l V else SOME V
            end

      val zero = foldl (fn (v,V) => NameMap.insert V (v,0)) valuationEmpty vs

      fun fold V acc =
          let
            val acc = f (V,acc)
          in
            case inc vs V of NONE => acc | SOME V => fold V acc
          end
    in
      fold zero
    end;

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

fun interpretTerm M V =
    let
      val Model {size = N, fixed, functions, ...} = M
      val {functions = fixed_functions, ...} = fixed

      fun interpret (Term.Var v) =
          (case NameMap.peek V v of
             NONE => raise Error "Model.interpretTerm: incomplete valuation"
           | SOME i => i)
        | interpret (tm as Term.Fn f_tms) =
          let
            val (f,tms) =
                case Term.stripComb tm of
                  (_,[]) => f_tms
                | (v as Term.Var _, tms) => (".", v :: tms)
                | (Term.Fn (f,tms), tms') => (f, tms @ tms')
            val elts = map interpret tms
            val f_elts = (f,elts)
            val ref funcs = functions
          in
            case Map.peek funcs f_elts of
              SOME k => k
            | NONE =>
              let
                val k =
                    case fixed_functions f_elts of
                      SOME k => k
                    | NONE => Portable.randomInt N

                val () = functions := Map.insert funcs (f_elts,k)
              in
                k
              end
          end;
    in
      interpret
    end;

fun interpretAtom M V (r,tms) =
    let
      val Model {fixed,relations,...} = M
      val {relations = fixed_relations, ...} = fixed

      val elts = map (interpretTerm M V) tms
      val r_elts = (r,elts)
      val ref rels = relations
    in
      case Map.peek rels r_elts of
        SOME b => b
      | NONE =>
        let
          val b =
              case fixed_relations r_elts of
                SOME b => b
              | NONE => Portable.randomBool ()

          val () = relations := Map.insert rels (r_elts,b)
        in
          b
        end
    end;

fun interpretFormula M =
    let
      val Model {size = N, ...} = M

      fun interpret _ Formula.True = true
        | interpret _ Formula.False = false
        | interpret V (Formula.Atom atm) = interpretAtom M V atm
        | interpret V (Formula.Not p) = not (interpret V p)
        | interpret V (Formula.Or (p,q)) = interpret V p orelse interpret V q
        | interpret V (Formula.And (p,q)) = interpret V p andalso interpret V q
        | interpret V (Formula.Imp (p,q)) =
          interpret V (Formula.Or (Formula.Not p, q))
        | interpret V (Formula.Iff (p,q)) = interpret V p = interpret V q
        | interpret V (Formula.Forall (v,p)) = interpret' V v p N
        | interpret V (Formula.Exists (v,p)) =
          interpret V (Formula.Not (Formula.Forall (v, Formula.Not p)))
      and interpret' _ _ _ 0 = true
        | interpret' V v p i =
          let
            val i = i - 1
            val V' = NameMap.insert V (v,i)
          in
            interpret V' p andalso interpret' V v p i
          end
    in
      interpret
    end;

fun interpretLiteral M V (true,atm) = interpretAtom M V atm
  | interpretLiteral M V (false,atm) = not (interpretAtom M V atm);

fun interpretClause M V cl = LiteralSet.exists (interpretLiteral M V) cl;

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

local
  fun checkGen freeVars interpret {maxChecks} M x =
      let
        val Model {size = N, ...} = M
            
        fun score (V,{T,F}) =
            if interpret M V x then {T = T + 1, F = F} else {T = T, F = F + 1}

        val vs = freeVars x

        fun randomCheck acc = score (valuationRandom {size = N} vs, acc)

        val small =
            intExp N (NameSet.size vs) <= maxChecks handle Overflow => false
      in
        if small then valuationFold {size = N} vs score {T = 0, F = 0}
        else funpow maxChecks randomCheck {T = 0, F = 0}
      end;
in
  val checkAtom = checkGen Atom.freeVars interpretAtom;

  val checkFormula = checkGen Formula.freeVars interpretFormula;

  val checkLiteral = checkGen Literal.freeVars interpretLiteral;

  val checkClause = checkGen LiteralSet.freeVars interpretClause;
end;

end
