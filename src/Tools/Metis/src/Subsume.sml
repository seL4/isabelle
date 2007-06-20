(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Subsume :> Subsume =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun findRest pred =
    let
      fun f _ [] = NONE
        | f ys (x :: xs) =
          if pred x then SOME (x, List.revAppend (ys,xs)) else f (x :: ys) xs
    in
      f []
    end;

local
  fun addSym (lit,acc) =
      case total Literal.sym lit of
        NONE => acc
      | SOME lit => lit :: acc
in
  fun clauseSym lits = List.foldl addSym lits lits;
end;

fun sortClause cl =
    let
      val lits = LiteralSet.toList cl
    in
      sortMap Literal.typedSymbols (revCompare Int.compare) lits
    end;

fun incompatible lit =
    let
      val lits = clauseSym [lit]
    in
      fn lit' => not (List.exists (can (Literal.unify Subst.empty lit')) lits)
    end;

(* ------------------------------------------------------------------------- *)
(* Clause ids and lengths.                                                   *)
(* ------------------------------------------------------------------------- *)

type clauseId = int;

type clauseLength = int;

local
  type idSet = (clauseId * clauseLength) Set.set;

  fun idCompare ((id1,len1),(id2,len2)) =
      case Int.compare (len1,len2) of
        LESS => LESS
      | EQUAL => Int.compare (id1,id2)
      | GREATER => GREATER;
in
  val idSetEmpty : idSet = Set.empty idCompare;

  fun idSetAdd (id_len,set) : idSet = Set.add set id_len;

  fun idSetAddMax max (id_len as (_,len), set) : idSet =
      if len <= max then Set.add set id_len else set;

  fun idSetIntersect set1 set2 : idSet = Set.intersect set1 set2;
end;

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

datatype 'a subsume =
    Subsume of
      {empty : (Thm.clause * Subst.subst * 'a) list,
       unit : (Literal.literal * Thm.clause * 'a)  LiteralNet.literalNet,
       nonunit :
         {nextId : clauseId,
          clauses : (Literal.literal list * Thm.clause * 'a) IntMap.map,
          fstLits : (clauseId * clauseLength) LiteralNet.literalNet,
          sndLits : (clauseId * clauseLength) LiteralNet.literalNet}};

fun new () =
    Subsume
      {empty = [],
       unit = LiteralNet.new {fifo = false},
       nonunit =
         {nextId = 0,
          clauses = IntMap.new (),
          fstLits = LiteralNet.new {fifo = false},
          sndLits = LiteralNet.new {fifo = false}}};

fun size (Subsume {empty, unit, nonunit = {clauses,...}}) =
    length empty + LiteralNet.size unit + IntMap.size clauses;
      
fun insert (Subsume {empty,unit,nonunit}) (cl',a) =
    case sortClause cl' of
      [] =>
      let
        val empty = (cl',Subst.empty,a) :: empty
      in
        Subsume {empty = empty, unit = unit, nonunit = nonunit}
      end
    | [lit] =>
      let
        val unit = LiteralNet.insert unit (lit,(lit,cl',a))
      in
        Subsume {empty = empty, unit = unit, nonunit = nonunit}
      end
    | fstLit :: (nonFstLits as sndLit :: otherLits) =>
      let
        val {nextId,clauses,fstLits,sndLits} = nonunit
        val id_length = (nextId, LiteralSet.size cl')
        val fstLits = LiteralNet.insert fstLits (fstLit,id_length)
        val (sndLit,otherLits) =
            case findRest (incompatible fstLit) nonFstLits of
              SOME sndLit_otherLits => sndLit_otherLits
            | NONE => (sndLit,otherLits)
        val sndLits = LiteralNet.insert sndLits (sndLit,id_length)
        val lits' = otherLits @ [fstLit,sndLit]
        val clauses = IntMap.insert clauses (nextId,(lits',cl',a))
        val nextId = nextId + 1
        val nonunit = {nextId = nextId, clauses = clauses,
                       fstLits = fstLits, sndLits = sndLits}
      in
        Subsume {empty = empty, unit = unit, nonunit = nonunit}
      end;

fun filter pred (Subsume {empty,unit,nonunit}) =
    let
      val empty = List.filter (pred o #3) empty

      val unit = LiteralNet.filter (pred o #3) unit

      val nonunit =
          let
            val {nextId,clauses,fstLits,sndLits} = nonunit
            val clauses' = IntMap.filter (pred o #3 o snd) clauses
          in
            if IntMap.size clauses = IntMap.size clauses' then nonunit
            else
              let
                fun predId (id,_) = IntMap.inDomain id clauses'
                val fstLits = LiteralNet.filter predId fstLits
                and sndLits = LiteralNet.filter predId sndLits
              in
                {nextId = nextId, clauses = clauses',
                 fstLits = fstLits, sndLits = sndLits}
              end
          end
    in
      Subsume {empty = empty, unit = unit, nonunit = nonunit}
    end;

fun toString subsume = "Subsume{" ^ Int.toString (size subsume) ^ "}";

fun pp p = Parser.ppMap toString Parser.ppString p;

(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun matchLit lit' (lit,acc) =
      case total (Literal.match Subst.empty lit') lit of
        SOME sub => sub :: acc
      | NONE => acc;
in
  fun genClauseSubsumes pred cl' lits' cl a =
      let
        fun mkSubsl acc sub [] = SOME (sub, sortMap length Int.compare acc)
          | mkSubsl acc sub (lit' :: lits') =
            case List.foldl (matchLit lit') [] cl of
              [] => NONE
            | [sub'] =>
              (case total (Subst.union sub) sub' of
                 NONE => NONE
               | SOME sub => mkSubsl acc sub lits')
            | subs => mkSubsl (subs :: acc) sub lits'

        fun search [] = NONE
          | search ((sub,[]) :: others) =
            let
              val x = (cl',sub,a)
            in
              if pred x then SOME x else search others
            end
          | search ((_, [] :: _) :: others) = search others
          | search ((sub, (sub' :: subs) :: subsl) :: others) =
            let
              val others = (sub, subs :: subsl) :: others
            in
              case total (Subst.union sub) sub' of
                NONE => search others
              | SOME sub => search ((sub,subsl) :: others)
            end
      in
        case mkSubsl [] Subst.empty lits' of
          NONE => NONE
        | SOME sub_subsl => search [sub_subsl]
      end;
end;

local
  fun emptySubsumes pred empty = List.find pred empty;

  fun unitSubsumes pred unit =
      let
        fun subLit lit =
            let
              fun subUnit (lit',cl',a) =
                  case total (Literal.match Subst.empty lit') lit of
                    NONE => NONE
                  | SOME sub =>
                    let
                      val x = (cl',sub,a)
                    in
                      if pred x then SOME x else NONE
                    end
            in
              first subUnit (LiteralNet.match unit lit)
            end
      in
        first subLit
      end;

  fun nonunitSubsumes pred nonunit max cl =
      let
        val addId = case max of NONE => idSetAdd | SOME n => idSetAddMax n

        fun subLit lits (lit,acc) =
            List.foldl addId acc (LiteralNet.match lits lit)

        val {nextId = _, clauses, fstLits, sndLits} = nonunit

        fun subCl' (id,_) =
            let
              val (lits',cl',a) = IntMap.get clauses id
            in
              genClauseSubsumes pred cl' lits' cl a
            end

        val fstCands = List.foldl (subLit fstLits) idSetEmpty cl
        val sndCands = List.foldl (subLit sndLits) idSetEmpty cl
        val cands = idSetIntersect fstCands sndCands
      in
        Set.firstl subCl' cands
      end;

  fun genSubsumes pred (Subsume {empty,unit,nonunit}) max cl =
      case emptySubsumes pred empty of
        s as SOME _ => s
      | NONE =>
        if max = SOME 0 then NONE
        else
          let
            val cl = clauseSym (LiteralSet.toList cl)
          in
            case unitSubsumes pred unit cl of
              s as SOME _ => s
            | NONE =>
              if max = SOME 1 then NONE
              else nonunitSubsumes pred nonunit max cl
          end;
in
  fun subsumes pred subsume cl = genSubsumes pred subsume NONE cl;

  fun strictlySubsumes pred subsume cl =
      genSubsumes pred subsume (SOME (LiteralSet.size cl)) cl;
end;

(*TRACE4
val subsumes = fn pred => fn subsume => fn cl =>
    let
      val ppCl = LiteralSet.pp
      val ppSub = Subst.pp
      val () = Parser.ppTrace ppCl "Subsume.subsumes: cl" cl
      val result = subsumes pred subsume cl
      val () =
          case result of
            NONE => trace "Subsume.subsumes: not subsumed\n"
          | SOME (cl,sub,_) =>
            (Parser.ppTrace ppCl "Subsume.subsumes: subsuming cl" cl;
             Parser.ppTrace ppSub "Subsume.subsumes: subsuming sub" sub)
    in
      result
    end;

val strictlySubsumes = fn pred => fn subsume => fn cl =>
    let
      val ppCl = LiteralSet.pp
      val ppSub = Subst.pp
      val () = Parser.ppTrace ppCl "Subsume.strictlySubsumes: cl" cl
      val result = strictlySubsumes subsume cl
      val () =
          case result of
            NONE => trace "Subsume.subsumes: not subsumed\n"
          | SOME (cl,sub,_) =>
            (Parser.ppTrace ppCl "Subsume.subsumes: subsuming cl" cl;
             Parser.ppTrace ppSub "Subsume.subsumes: subsuming sub" sub)
    in
      result
    end;
*)

fun isSubsumed subs cl = Option.isSome (subsumes (K true) subs cl);

fun isStrictlySubsumed subs cl =
    Option.isSome (strictlySubsumes (K true) subs cl);

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

fun clauseSubsumes cl' cl =
    let
      val lits' = sortClause cl'
      and lits = clauseSym (LiteralSet.toList cl)
    in
      case genClauseSubsumes (K true) cl' lits' lits () of
        SOME (_,sub,()) => SOME sub
      | NONE => NONE
    end;

fun clauseStrictlySubsumes cl' cl =
    if LiteralSet.size cl' > LiteralSet.size cl then NONE
    else clauseSubsumes cl' cl;

end
