(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004 Joe Leslie-Hurd, distributed under the BSD License     *)
(* ========================================================================= *)

functor ElementSet (
  KM : KeyMap
) :> ElementSet
where type element = KM.key
and type 'a map = 'a KM.map =
struct

(* ------------------------------------------------------------------------- *)
(* A type of set elements.                                                   *)
(* ------------------------------------------------------------------------- *)

type element = KM.key;

val compareElement = KM.compareKey;

val equalElement = KM.equalKey;

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type 'a map = 'a KM.map;

datatype set = Set of unit map;

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

fun dest (Set m) = m;

fun mapPartial f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.mapPartial mf m
    end;

fun map f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.map mf m
    end;

fun domain m = Set (KM.transform (fn _ => ()) m);

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

val empty = Set (KM.new ());

fun singleton elt = Set (KM.singleton (elt,()));

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun null (Set m) = KM.null m;

fun size (Set m) = KM.size m;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun peek (Set m) elt =
    case KM.peekKey m elt of
      SOME (elt,()) => SOME elt
    | NONE => NONE;

fun member elt (Set m) = KM.inDomain elt m;

fun pick (Set m) =
    let
      val (elt,_) = KM.pick m
    in
      elt
    end;

fun nth (Set m) n =
    let
      val (elt,_) = KM.nth m n
    in
      elt
    end;

fun random (Set m) =
    let
      val (elt,_) = KM.random m
    in
      elt
    end;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

fun add (Set m) elt =
    let
      val m = KM.insert m (elt,())
    in
      Set m
    end;

local
  fun uncurriedAdd (elt,set) = add set elt;
in
  fun addList set = List.foldl uncurriedAdd set;
end;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun delete (Set m) elt =
    let
      val m = KM.delete m elt
    in
      Set m
    end;

fun remove (Set m) elt =
    let
      val m = KM.remove m elt
    in
      Set m
    end;

fun deletePick (Set m) =
    let
      val ((elt,()),m) = KM.deletePick m
    in
      (elt, Set m)
    end;

fun deleteNth (Set m) n =
    let
      val ((elt,()),m) = KM.deleteNth m n
    in
      (elt, Set m)
    end;

fun deleteRandom (Set m) =
    let
      val ((elt,()),m) = KM.deleteRandom m
    in
      (elt, Set m)
    end;

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

fun union (Set m1) (Set m2) = Set (KM.unionDomain m1 m2);

fun unionList sets =
    let
      val ms = List.map dest sets
    in
      Set (KM.unionListDomain ms)
    end;

fun intersect (Set m1) (Set m2) = Set (KM.intersectDomain m1 m2);

fun intersectList sets =
    let
      val ms = List.map dest sets
    in
      Set (KM.intersectListDomain ms)
    end;

fun difference (Set m1) (Set m2) =
    Set (KM.differenceDomain m1 m2);

fun symmetricDifference (Set m1) (Set m2) =
    Set (KM.symmetricDifferenceDomain m1 m2);

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

fun filter pred =
    let
      fun mpred (elt,()) = pred elt
    in
      fn Set m => Set (KM.filter mpred m)
    end;

fun partition pred =
    let
      fun mpred (elt,()) = pred elt
    in
      fn Set m =>
         let
           val (m1,m2) = KM.partition mpred m
         in
           (Set m1, Set m2)
         end
    end;

fun app f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.app mf m
    end;

fun foldl f =
    let
      fun mf (elt,(),acc) = f (elt,acc)
    in
      fn acc => fn Set m => KM.foldl mf acc m
    end;

fun foldr f =
    let
      fun mf (elt,(),acc) = f (elt,acc)
    in
      fn acc => fn Set m => KM.foldr mf acc m
    end;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

fun findl p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m =>
         case KM.findl mp m of
           SOME (elt,()) => SOME elt
         | NONE => NONE
    end;

fun findr p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m =>
         case KM.findr mp m of
           SOME (elt,()) => SOME elt
         | NONE => NONE
    end;

fun firstl f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.firstl mf m
    end;

fun firstr f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.firstr mf m
    end;

fun exists p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => KM.exists mp m
    end;

fun all p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => KM.all mp m
    end;

fun count p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => KM.count mp m
    end;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

fun compareValue ((),()) = EQUAL;

fun equalValue () () = true;

fun compare (Set m1, Set m2) = KM.compare compareValue (m1,m2);

fun equal (Set m1) (Set m2) = KM.equal equalValue m1 m2;

fun subset (Set m1) (Set m2) = KM.subsetDomain m1 m2;

fun disjoint (Set m1) (Set m2) = KM.disjointDomain m1 m2;

(* ------------------------------------------------------------------------- *)
(* Pointwise operations.                                                     *)
(* ------------------------------------------------------------------------- *)

fun lift f =
    let
      fun inc (elt,set) = union set (f elt)
    in
      foldl inc empty
    end;

fun closedAdd f =
    let
      fun adds acc set = foldl check acc set

      and check (elt,acc) =
          if member elt acc then acc
          else expand (add acc elt) elt

      and expand acc elt = adds acc (f elt)
    in
      adds
    end;

fun close f = closedAdd f empty;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

fun transform f =
    let
      fun inc (x,l) = f x :: l
    in
      foldr inc []
    end;

fun toList (Set m) = KM.keys m;

fun fromList elts = addList empty elts;

(* ------------------------------------------------------------------------- *)
(* Depth-first search.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype ordering =
    Linear of element list
  | Cycle of element list;

fun postOrdered children =
    let
      fun check acc elts =
          case elts of
            [] => true
          | elt :: elts =>
            not (member elt acc) andalso
            let
              val acc = closedAdd children acc (singleton elt)
            in
              check acc elts
            end
    in
      check empty
    end;

fun preOrdered children elts = postOrdered children (List.rev elts);

local
  fun takeStackset elt =
      let
        fun notElement (e,_,_) = not (equalElement e elt)
      in
        Useful.takeWhile notElement
      end;

  fun consElement ((e,_,_),el) = e :: el;

  fun depthFirstSearch children =
      let
        fun traverse (dealt,dealtset) (stack,stackset) work =
            case work of
              [] =>
              (case stack of
                 [] => Linear dealt
               | (elt,work,stackset) :: stack =>
                 let
                   val dealt = elt :: dealt

                   val dealtset = add dealtset elt
                 in
                   traverse (dealt,dealtset) (stack,stackset) work
                 end)
            | elt :: work =>
              if member elt dealtset then
                traverse (dealt,dealtset) (stack,stackset) work
              else if member elt stackset then
                let
                  val cycle = takeStackset elt stack

                  val cycle = elt :: List.foldl consElement [elt] cycle
                in
                  Cycle cycle
                end
              else
                let
                  val stack = (elt,work,stackset) :: stack

                  val stackset = add stackset elt

                  val work = toList (children elt)
                in
                  traverse (dealt,dealtset) (stack,stackset) work
                end

        val dealt = []
        and dealtset = empty
        and stack = []
        and stackset = empty
      in
        traverse (dealt,dealtset) (stack,stackset)
      end;
in
  fun preOrder children roots =
      let
        val result = depthFirstSearch children (toList roots)

(*BasicDebug
        val () =
            case result of
              Cycle _ => ()
            | Linear l =>
              let
                val () =
                    if subset roots (fromList l) then ()
                    else raise Useful.Bug "ElementSet.preOrder: missing roots"

                val () =
                    if preOrdered children l then ()
                    else raise Useful.Bug "ElementSet.preOrder: bad ordering"
              in
                ()
              end
*)
      in
        result
      end;

  fun postOrder children roots =
      case depthFirstSearch children (toList roots) of
        Linear l =>
        let
          val l = List.rev l

(*BasicDebug
          val () =
              if subset roots (fromList l) then ()
              else raise Useful.Bug "ElementSet.postOrder: missing roots"

          val () =
              if postOrdered children l then ()
              else raise Useful.Bug "ElementSet.postOrder: bad ordering"
*)
        in
          Linear l
        end
      | cycle => cycle;
end;

(* ------------------------------------------------------------------------- *)
(* Strongly connected components.                                            *)
(* ------------------------------------------------------------------------- *)

fun postOrderedSCC children =
    let
      fun check acc eltsl =
          case eltsl of
            [] => true
          | elts :: eltsl =>
            not (null elts) andalso
            disjoint elts acc andalso
            let
              fun addElt elt = closedAdd children acc (singleton elt)

              val (root,elts) = deletePick elts

              fun checkElt elt = member root (addElt elt)
            in
              all checkElt elts andalso
              let
                val acc = addElt root
              in
                subset elts acc andalso
                check acc eltsl
              end
            end
    in
      check empty
    end;

fun preOrderedSCC children eltsl = postOrderedSCC children (List.rev eltsl);

(* An implementation of Tarjan's algorithm: *)

(* http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm *)

local
  datatype stackSCC = StackSCC of set * (element * set) list;

  val emptyStack = StackSCC (empty,[]);

  fun pushStack (StackSCC (elts,eltl)) elt =
      StackSCC (add elts elt, (elt,elts) :: eltl);

  fun inStack elt (StackSCC (elts,_)) = member elt elts;

  fun popStack root =
      let
        fun pop scc eltl =
            case eltl of
              [] => raise Useful.Bug "ElementSet.popStack"
            | (elt,elts) :: eltl =>
              let
                val scc = add scc elt
              in
                if equalElement elt root then (scc, StackSCC (elts,eltl))
                else pop scc eltl
              end
      in
        fn sccs => fn StackSCC (_,eltl) =>
           let
             val (scc,stack) = pop empty eltl
           in
             (scc :: sccs, stack)
           end
      end;

  fun getIndex indices e : int =
      case KM.peek indices e of
        SOME i => i
      | NONE => raise Useful.Bug "ElementSet.getIndex";

  fun isRoot indices lows e = getIndex indices e = getIndex lows e;

  fun reduceIndex indices (e,i) =
      let
        val j = getIndex indices e
      in
        if j <= i then indices else KM.insert indices (e,i)
      end;

  fun tarjan children =
      let
        fun dfsVertex sccs callstack index indices lows stack elt =
            let
              val indices = KM.insert indices (elt,index)
              and lows = KM.insert lows (elt,index)

              val index = index + 1

              val stack = pushStack stack elt

              val chil = toList (children elt)
            in
              dfsSuccessors sccs callstack index indices lows stack elt chil
            end

        and dfsSuccessors sccs callstack index indices lows stack elt chil =
            case chil of
              [] =>
              let
                val (sccs,stack) =
                    if isRoot indices lows elt then popStack elt sccs stack
                    else (sccs,stack)
              in
                case callstack of
                  [] => (sccs,index,indices,lows)
                | (p,elts) :: callstack =>
                  let
                    val lows = reduceIndex lows (p, getIndex lows elt)
                  in
                    dfsSuccessors sccs callstack index indices lows stack p elts
                  end
              end
            | c :: chil =>
              case KM.peek indices c of
                NONE =>
                let
                  val callstack = (elt,chil) :: callstack
                in
                  dfsVertex sccs callstack index indices lows stack c
                end
              | SOME cind =>
                let
                  val lows =
                      if inStack c stack then reduceIndex lows (elt,cind)
                      else lows
                in
                  dfsSuccessors sccs callstack index indices lows stack elt chil
                end

        fun dfsRoots sccs index indices lows elts =
            case elts of
              [] => sccs
            | elt :: elts =>
              if KM.inDomain elt indices then
                dfsRoots sccs index indices lows elts
              else
                let
                  val callstack = []

                  val (sccs,index,indices,lows) =
                      dfsVertex sccs callstack index indices lows emptyStack elt
                in
                  dfsRoots sccs index indices lows elts
                end

        val sccs = []
        and index = 0
        and indices = KM.new ()
        and lows = KM.new ()
      in
        dfsRoots sccs index indices lows
      end;
in
  fun preOrderSCC children roots =
      let
        val result = tarjan children (toList roots)

(*BasicDebug
        val () =
            if subset roots (unionList result) then ()
            else raise Useful.Bug "ElementSet.preOrderSCC: missing roots"

        val () =
            if preOrderedSCC children result then ()
            else raise Useful.Bug "ElementSet.preOrderSCC: bad ordering"
*)
      in
        result
      end;

  fun postOrderSCC children roots =
      let
        val result = List.rev (tarjan children (toList roots))

(*BasicDebug
        val () =
            if subset roots (unionList result) then ()
            else raise Useful.Bug "ElementSet.postOrderSCC: missing roots"

        val () =
            if postOrderedSCC children result then ()
            else raise Useful.Bug "ElementSet.postOrderSCC: bad ordering"
*)
      in
        result
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun toString set =
    "{" ^ (if null set then "" else Int.toString (size set)) ^ "}";

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type iterator = unit KM.iterator;

fun mkIterator (Set m) = KM.mkIterator m;

fun mkRevIterator (Set m) = KM.mkRevIterator m;

fun readIterator iter =
    let
      val (elt,()) = KM.readIterator iter
    in
      elt
    end;

fun advanceIterator iter = KM.advanceIterator iter;

end

structure IntSet =
ElementSet (IntMap);

structure IntPairSet =
ElementSet (IntPairMap);

structure StringSet =
ElementSet (StringMap);
