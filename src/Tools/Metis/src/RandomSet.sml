(* ========================================================================= *)
(* FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure RandomSet :> Set =
struct

exception Bug = Useful.Bug;

exception Error = Useful.Error;

val pointerEqual = Portable.pointerEqual;

val K = Useful.K;

val snd = Useful.snd;

val randomInt = Useful.random;

(* ------------------------------------------------------------------------- *)
(* Random search trees.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype 'a tree =
    E
  | T of
    {size : int,
     priority : real,
     left : 'a tree,
     key : 'a,
     right : 'a tree};
    
type 'a node =
     {size : int,
      priority : real,
      left : 'a tree,
      key : 'a,
      right : 'a tree};

datatype 'a set = Set of ('a * 'a -> order) * 'a tree;

(* ------------------------------------------------------------------------- *)
(* Random priorities.                                                        *)
(* ------------------------------------------------------------------------- *)

local
  val randomPriority =
      let
        val gen = Random.newgenseed 2.0
      in
        fn () => Random.random gen
      end;

  val priorityOrder = Real.compare;
in
  fun treeSingleton key =
      T {size = 1, priority = randomPriority (),
         left = E, key = key, right = E};

  fun nodePriorityOrder cmp (x1 : 'a node, x2 : 'a node) =
      let
        val {priority = p1, key = k1, ...} = x1
        and {priority = p2, key = k2, ...} = x2
      in
        case priorityOrder (p1,p2) of
          LESS => LESS
        | EQUAL => cmp (k1,k2)
        | GREATER => GREATER
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Debugging functions.                                                      *)
(* ------------------------------------------------------------------------- *)

local
  fun checkSizes E = 0
    | checkSizes (T {size,left,right,...}) =
      let
        val l = checkSizes left
        and r = checkSizes right
        val () = if l + 1 + r = size then () else raise Error "wrong size"
      in
        size
      end

  fun checkSorted _ x E = x
    | checkSorted cmp x (T {left,key,right,...}) =
      let
        val x = checkSorted cmp x left
        val () =
            case x of
              NONE => ()
            | SOME k =>
              case cmp (k,key) of
                LESS => ()
              | EQUAL => raise Error "duplicate keys"
              | GREATER => raise Error "unsorted"
      in
        checkSorted cmp (SOME key) right
      end;

  fun checkPriorities _ E = NONE
    | checkPriorities cmp (T (x as {left,right,...})) =
      let
        val () =
            case checkPriorities cmp left of
              NONE => ()
            | SOME l =>
              case nodePriorityOrder cmp (l,x) of
                LESS => ()
              | EQUAL => raise Error "left child has equal key"
              | GREATER => raise Error "left child has greater priority"
        val () =
            case checkPriorities cmp right of
              NONE => ()
            | SOME r =>
              case nodePriorityOrder cmp (r,x) of
                LESS => ()
              | EQUAL => raise Error "right child has equal key"
              | GREATER => raise Error "right child has greater priority"
      in
        SOME x
      end;
in
  fun checkWellformed s (set as Set (cmp,tree)) =
      (let
         val _ = checkSizes tree
         val _ = checkSorted cmp NONE tree
         val _ = checkPriorities cmp tree
       in
         set
       end
       handle Error err => raise Bug err)
      handle Bug bug => raise Bug (s ^ "\nRandomSet.checkWellformed: " ^ bug);
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun comparison (Set (cmp,_)) = cmp;

fun empty cmp = Set (cmp,E);

fun treeSize E = 0
  | treeSize (T {size = s, ...}) = s;

fun size (Set (_,tree)) = treeSize tree;

fun mkT p l k r =
    T {size = treeSize l + 1 + treeSize r, priority = p,
       left = l, key = k, right = r};

fun singleton cmp key = Set (cmp, treeSingleton key);

local
  fun treePeek cmp E pkey = NONE
    | treePeek cmp (T {left,key,right,...}) pkey =
      case cmp (pkey,key) of
        LESS => treePeek cmp left pkey
      | EQUAL => SOME key
      | GREATER => treePeek cmp right pkey
in
  fun peek (Set (cmp,tree)) key = treePeek cmp tree key;
end;

(* treeAppend assumes that every element of the first tree is less than *)
(* every element of the second tree. *)

fun treeAppend _ t1 E = t1
  | treeAppend _ E t2 = t2
  | treeAppend cmp (t1 as T x1) (t2 as T x2) =
    case nodePriorityOrder cmp (x1,x2) of
      LESS =>
      let
        val {priority = p2, left = l2, key = k2, right = r2, ...} = x2
      in
        mkT p2 (treeAppend cmp t1 l2) k2 r2
      end
    | EQUAL => raise Bug "RandomSet.treeAppend: equal keys"
    | GREATER =>
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
      in
        mkT p1 l1 k1 (treeAppend cmp r1 t2)
      end;

(* nodePartition splits the node into three parts: the keys comparing less *)
(* than the supplied key, an optional equal key, and the keys comparing *)
(* greater. *)

local
  fun mkLeft [] t = t
    | mkLeft (({priority,left,key,...} : 'a node) :: xs) t =
      mkLeft xs (mkT priority left key t);

  fun mkRight [] t = t
    | mkRight (({priority,key,right,...} : 'a node) :: xs) t =
      mkRight xs (mkT priority t key right);

  fun treePart _ _ lefts rights E = (mkLeft lefts E, NONE, mkRight rights E)
    | treePart cmp pkey lefts rights (T x) = nodePart cmp pkey lefts rights x
  and nodePart cmp pkey lefts rights (x as {left,key,right,...}) =
      case cmp (pkey,key) of
        LESS => treePart cmp pkey lefts (x :: rights) left
      | EQUAL => (mkLeft lefts left, SOME key, mkRight rights right)
      | GREATER => treePart cmp pkey (x :: lefts) rights right;
in
  fun nodePartition cmp x pkey = nodePart cmp pkey [] [] x;
end;

(* union first calls treeCombineRemove, to combine the values *)
(* for equal keys into the first map and remove them from the second map. *)
(* Note that the combined key is always the one from the second map. *)

local
  fun treeCombineRemove _ t1 E = (t1,E)
    | treeCombineRemove _ E t2 = (E,t2)
    | treeCombineRemove cmp (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,k2,r2) = nodePartition cmp x2 k1
        val (l1,l2) = treeCombineRemove cmp l1 l2
        and (r1,r2) = treeCombineRemove cmp r1 r2
      in
        case k2 of
          NONE => if treeSize l2 + treeSize r2 = #size x2 then (t1,t2)
                  else (mkT p1 l1 k1 r1, treeAppend cmp l2 r2)
        | SOME k2 => (mkT p1 l1 k2 r1, treeAppend cmp l2 r2)
      end;

  fun treeUnionDisjoint _ t1 E = t1
    | treeUnionDisjoint _ E t2 = t2
    | treeUnionDisjoint cmp (T x1) (T x2) =
      case nodePriorityOrder cmp (x1,x2) of
        LESS => nodeUnionDisjoint cmp x2 x1
      | EQUAL => raise Bug "RandomSet.unionDisjoint: equal keys"
      | GREATER => nodeUnionDisjoint cmp x1 x2

  and nodeUnionDisjoint cmp x1 x2 =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,_,r2) = nodePartition cmp x2 k1
        val l = treeUnionDisjoint cmp l1 l2
        and r = treeUnionDisjoint cmp r1 r2
      in
        mkT p1 l k1 r
      end;
in
  fun union (s1 as Set (cmp,t1)) (Set (_,t2)) =
      if pointerEqual (t1,t2) then s1
      else
        let
          val (t1,t2) = treeCombineRemove cmp t1 t2
        in
          Set (cmp, treeUnionDisjoint cmp t1 t2)
        end;
end;

(*DEBUG
val union = fn t1 => fn t2 =>
    checkWellformed "RandomSet.union: result"
      (union (checkWellformed "RandomSet.union: input 1" t1)
             (checkWellformed "RandomSet.union: input 2" t2));
*)

(* intersect is a simple case of the union algorithm. *)

local
  fun treeIntersect _ _ E = E
    | treeIntersect _ E _ = E
    | treeIntersect cmp (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,k2,r2) = nodePartition cmp x2 k1
        val l = treeIntersect cmp l1 l2
        and r = treeIntersect cmp r1 r2
      in
        case k2 of
          NONE => treeAppend cmp l r
        | SOME k2 => mkT p1 l k2 r
      end;
in
  fun intersect (s1 as Set (cmp,t1)) (Set (_,t2)) =
      if pointerEqual (t1,t2) then s1
      else Set (cmp, treeIntersect cmp t1 t2);
end;

(*DEBUG
val intersect = fn t1 => fn t2 =>
    checkWellformed "RandomSet.intersect: result"
      (intersect (checkWellformed "RandomSet.intersect: input 1" t1)
                 (checkWellformed "RandomSet.intersect: input 2" t2));
*)

(* delete raises an exception if the supplied key is not found, which *)
(* makes it simpler to maximize sharing. *)

local
  fun treeDelete _ E _ = raise Error "RandomSet.delete: element not found"
    | treeDelete cmp (T {priority,left,key,right,...}) dkey =
      case cmp (dkey,key) of
        LESS => mkT priority (treeDelete cmp left dkey) key right
      | EQUAL => treeAppend cmp left right
      | GREATER => mkT priority left key (treeDelete cmp right dkey);
in
  fun delete (Set (cmp,tree)) key = Set (cmp, treeDelete cmp tree key);
end;
 
(*DEBUG
val delete = fn t => fn x =>
    checkWellformed "RandomSet.delete: result"
      (delete (checkWellformed "RandomSet.delete: input" t) x);
*)

(* Set difference *)

local
  fun treeDifference _ t1 E = t1
    | treeDifference _ E _ = E
    | treeDifference cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, priority = p1, left = l1, key = k1, right = r1} = x1
        val (l2,k2,r2) = nodePartition cmp x2 k1
        val l = treeDifference cmp l1 l2
        and r = treeDifference cmp r1 r2
      in
        if Option.isSome k2 then treeAppend cmp l r
        else if treeSize l + treeSize r + 1 = s1 then t1
        else mkT p1 l k1 r
      end;
in
  fun difference (Set (cmp,tree1)) (Set (_,tree2)) =
      if pointerEqual (tree1,tree2) then Set (cmp,E)
      else Set (cmp, treeDifference cmp tree1 tree2);
end;

(*DEBUG
val difference = fn t1 => fn t2 =>
    checkWellformed "RandomSet.difference: result"
      (difference (checkWellformed "RandomSet.difference: input 1" t1)
                  (checkWellformed "RandomSet.difference: input 2" t2));
*)

(* Subsets *)

local
  fun treeSubset _ E _ = true
    | treeSubset _ _ E = false
    | treeSubset cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 <= s2 andalso
        let
          val (l2,k2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2 andalso
          treeSubset cmp l1 l2 andalso
          treeSubset cmp r1 r2
        end
      end;
in
  fun subset (Set (cmp,tree1)) (Set (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeSubset cmp tree1 tree2;
end;

(* Set equality *)

local
  fun treeEqual _ E E = true
    | treeEqual _ E _ = false
    | treeEqual _ _ E = false
    | treeEqual cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 = s2 andalso
        let
          val (l2,k2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2 andalso
          treeEqual cmp l1 l2 andalso
          treeEqual cmp r1 r2
        end
      end;
in
  fun equal (Set (cmp,tree1)) (Set (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeEqual cmp tree1 tree2;
end;

(* filter is the basic function for preserving the tree structure. *)

local
  fun treeFilter _ _ E = E
    | treeFilter cmp pred (T {priority,left,key,right,...}) =
      let
        val left = treeFilter cmp pred left
        and right = treeFilter cmp pred right
      in
        if pred key then mkT priority left key right
        else treeAppend cmp left right
      end;
in
  fun filter pred (Set (cmp,tree)) = Set (cmp, treeFilter cmp pred tree);
end;

(* nth picks the nth smallest key (counting from 0). *)

local
  fun treeNth E _ = raise Subscript
    | treeNth (T {left,key,right,...}) n =
      let
        val k = treeSize left
      in
        if n = k then key
        else if n < k then treeNth left n
        else treeNth right (n - (k + 1))
      end;
in
  fun nth (Set (_,tree)) n = treeNth tree n;
end;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

fun leftSpine E acc = acc
  | leftSpine (t as T {left,...}) acc = leftSpine left (t :: acc);

fun rightSpine E acc = acc
  | rightSpine (t as T {right,...}) acc = rightSpine right (t :: acc);

datatype 'a iterator =
    LR of 'a * 'a tree * 'a tree list
  | RL of 'a * 'a tree * 'a tree list;

fun mkLR [] = NONE
  | mkLR (T {key,right,...} :: l) = SOME (LR (key,right,l))
  | mkLR (E :: _) = raise Bug "RandomSet.mkLR";

fun mkRL [] = NONE
  | mkRL (T {key,left,...} :: l) = SOME (RL (key,left,l))
  | mkRL (E :: _) = raise Bug "RandomSet.mkRL";

fun mkIterator (Set (_,tree)) = mkLR (leftSpine tree []);

fun mkRevIterator (Set (_,tree)) = mkRL (rightSpine tree []);

fun readIterator (LR (key,_,_)) = key
  | readIterator (RL (key,_,_)) = key;

fun advanceIterator (LR (_,next,l)) = mkLR (leftSpine next l)
  | advanceIterator (RL (_,next,l)) = mkRL (rightSpine next l);

(* ------------------------------------------------------------------------- *)
(* Derived operations.                                                       *)
(* ------------------------------------------------------------------------- *)

fun null s = size s = 0;

fun member x s = Option.isSome (peek s x);

(* add must be primitive to get hold of the comparison function *)

fun add s x = union s (singleton (comparison s) x);

(*DEBUG
val add = fn s => fn x =>
    checkWellformed "RandomSet.add: result"
      (add (checkWellformed "RandomSet.add: input" s) x);
*)

local
  fun unionPairs ys [] = rev ys
    | unionPairs ys (xs as [_]) = List.revAppend (ys,xs)
    | unionPairs ys (x1 :: x2 :: xs) = unionPairs (union x1 x2 :: ys) xs;
in
  fun unionList [] = raise Error "Set.unionList: no sets"
    | unionList [s] = s
    | unionList l = unionList (unionPairs [] l);
end;

local
  fun intersectPairs ys [] = rev ys
    | intersectPairs ys (xs as [_]) = List.revAppend (ys,xs)
    | intersectPairs ys (x1 :: x2 :: xs) =
      intersectPairs (intersect x1 x2 :: ys) xs;
in
  fun intersectList [] = raise Error "Set.intersectList: no sets"
    | intersectList [s] = s
    | intersectList l = intersectList (intersectPairs [] l);
end;

fun symmetricDifference s1 s2 = union (difference s1 s2) (difference s2 s1);

fun disjoint s1 s2 = null (intersect s1 s2);

fun partition pred set = (filter pred set, filter (not o pred) set);

local
  fun fold _ NONE acc = acc
    | fold f (SOME iter) acc =
      let
        val key = readIterator iter
      in
        fold f (advanceIterator iter) (f (key,acc))
      end;
in
  fun foldl f b m = fold f (mkIterator m) b;

  fun foldr f b m = fold f (mkRevIterator m) b;
end;

local
  fun find _ NONE = NONE
    | find pred (SOME iter) =
      let
        val key = readIterator iter
      in
        if pred key then SOME key
        else find pred (advanceIterator iter)
      end;
in
  fun findl p m = find p (mkIterator m);

  fun findr p m = find p (mkRevIterator m);
end;

local
  fun first _ NONE = NONE
    | first f (SOME iter) =
      let
        val key = readIterator iter
      in
        case f key of
          NONE => first f (advanceIterator iter)
        | s => s
      end;
in
  fun firstl f m = first f (mkIterator m);

  fun firstr f m = first f (mkRevIterator m);
end;

fun count p = foldl (fn (x,n) => if p x then n + 1 else n) 0;

fun fromList cmp l = List.foldl (fn (k,s) => add s k) (empty cmp) l;

fun addList s l = union s (fromList (comparison s) l);

fun toList s = foldr op:: [] s;

fun map f s = rev (foldl (fn (x,l) => (x, f x) :: l) [] s);

fun transform f s = rev (foldl (fn (x,l) => f x :: l) [] s);

fun app f s = foldl (fn (x,()) => f x) () s;

fun exists p s = Option.isSome (findl p s);

fun all p s = not (exists (not o p) s);

local
  fun iterCompare _ NONE NONE = EQUAL
    | iterCompare _ NONE (SOME _) = LESS
    | iterCompare _ (SOME _) NONE = GREATER
    | iterCompare cmp (SOME i1) (SOME i2) =
      keyIterCompare cmp (readIterator i1) (readIterator i2) i1 i2

  and keyIterCompare cmp k1 k2 i1 i2 =
      case cmp (k1,k2) of
        LESS => LESS
      | EQUAL => iterCompare cmp (advanceIterator i1) (advanceIterator i2)
      | GREATER => GREATER;
in
  fun compare (s1,s2) =
      if pointerEqual (s1,s2) then EQUAL
      else
        case Int.compare (size s1, size s2) of
          LESS => LESS
        | EQUAL => iterCompare (comparison s1) (mkIterator s1) (mkIterator s2)
        | GREATER => GREATER;
end;

fun pick s =
    case findl (K true) s of
      SOME p => p
    | NONE => raise Error "RandomSet.pick: empty";

fun random s = case size s of 0 => raise Empty | n => nth s (randomInt n);

fun deletePick s = let val x = pick s in (x, delete s x) end;

fun deleteRandom s = let val x = random s in (x, delete s x) end;

fun close f s = let val s' = f s in if equal s s' then s else close f s' end;

fun toString s = "{" ^ (if null s then "" else Int.toString (size s)) ^ "}";

end
