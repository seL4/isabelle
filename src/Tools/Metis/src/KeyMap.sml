(* ========================================================================= *)
(* FINITE MAPS WITH A FIXED KEY TYPE                                         *)
(* Copyright (c) 2004 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

functor KeyMap (Key : Ordered) :> KeyMap where type key = Key.t =
struct

(* ------------------------------------------------------------------------- *)
(* Importing from the input signature.                                       *)
(* ------------------------------------------------------------------------- *)

type key = Key.t;

val compareKey = Key.compare;

(* ------------------------------------------------------------------------- *)
(* Importing useful functionality.                                           *)
(* ------------------------------------------------------------------------- *)

exception Bug = Useful.Bug;

exception Error = Useful.Error;

val pointerEqual = Portable.pointerEqual;

val K = Useful.K;

val randomInt = Portable.randomInt;

val randomWord = Portable.randomWord;

(* ------------------------------------------------------------------------- *)
(* Converting a comparison function to an equality function.                 *)
(* ------------------------------------------------------------------------- *)

fun equalKey key1 key2 = compareKey (key1,key2) = EQUAL;

(* ------------------------------------------------------------------------- *)
(* Priorities.                                                               *)
(* ------------------------------------------------------------------------- *)

type priority = Word.word;

val randomPriority = randomWord;

val comparePriority = Word.compare;

(* ------------------------------------------------------------------------- *)
(* Priority search trees.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype 'value tree =
    E
  | T of 'value node

and 'value node =
    Node of
      {size : int,
       priority : priority,
       left : 'value tree,
       key : key,
       value : 'value,
       right : 'value tree};

fun lowerPriorityNode node1 node2 =
    let
      val Node {priority = p1, ...} = node1
      and Node {priority = p2, ...} = node2
    in
      comparePriority (p1,p2) = LESS
    end;

(* ------------------------------------------------------------------------- *)
(* Tree debugging functions.                                                 *)
(* ------------------------------------------------------------------------- *)

(*BasicDebug
local
  fun checkSizes tree =
      case tree of
        E => 0
      | T (Node {size,left,right,...}) =>
        let
          val l = checkSizes left
          and r = checkSizes right

          val () = if l + 1 + r = size then () else raise Bug "wrong size"
        in
          size
        end;

  fun checkSorted x tree =
      case tree of
        E => x
      | T (Node {left,key,right,...}) =>
        let
          val x = checkSorted x left

          val () =
              case x of
                NONE => ()
              | SOME k =>
                case compareKey (k,key) of
                  LESS => ()
                | EQUAL => raise Bug "duplicate keys"
                | GREATER => raise Bug "unsorted"

          val x = SOME key
        in
          checkSorted x right
        end;

  fun checkPriorities tree =
      case tree of
        E => NONE
      | T node =>
        let
          val Node {left,right,...} = node

          val () =
              case checkPriorities left of
                NONE => ()
              | SOME lnode =>
                if not (lowerPriorityNode node lnode) then ()
                else raise Bug "left child has greater priority"

          val () =
              case checkPriorities right of
                NONE => ()
              | SOME rnode =>
                if not (lowerPriorityNode node rnode) then ()
                else raise Bug "right child has greater priority"
        in
          SOME node
        end;
in
  fun treeCheckInvariants tree =
      let
        val _ = checkSizes tree

        val _ = checkSorted NONE tree

        val _ = checkPriorities tree
      in
        tree
      end
      handle Error err => raise Bug err;
end;
*)

(* ------------------------------------------------------------------------- *)
(* Tree operations.                                                          *)
(* ------------------------------------------------------------------------- *)

fun treeNew () = E;

fun nodeSize (Node {size = x, ...}) = x;

fun treeSize tree =
    case tree of
      E => 0
    | T x => nodeSize x;

fun mkNode priority left key value right =
    let
      val size = treeSize left + 1 + treeSize right
    in
      Node
        {size = size,
         priority = priority,
         left = left,
         key = key,
         value = value,
         right = right}
    end;

fun mkTree priority left key value right =
    let
      val node = mkNode priority left key value right
    in
      T node
    end;

(* ------------------------------------------------------------------------- *)
(* Extracting the left and right spines of a tree.                           *)
(* ------------------------------------------------------------------------- *)

fun treeLeftSpine acc tree =
    case tree of
      E => acc
    | T node => nodeLeftSpine acc node

and nodeLeftSpine acc node =
    let
      val Node {left,...} = node
    in
      treeLeftSpine (node :: acc) left
    end;

fun treeRightSpine acc tree =
    case tree of
      E => acc
    | T node => nodeRightSpine acc node

and nodeRightSpine acc node =
    let
      val Node {right,...} = node
    in
      treeRightSpine (node :: acc) right
    end;

(* ------------------------------------------------------------------------- *)
(* Singleton trees.                                                          *)
(* ------------------------------------------------------------------------- *)

fun mkNodeSingleton priority key value =
    let
      val size = 1
      and left = E
      and right = E
    in
      Node
        {size = size,
         priority = priority,
         left = left,
         key = key,
         value = value,
         right = right}
    end;

fun nodeSingleton (key,value) =
    let
      val priority = randomPriority ()
    in
      mkNodeSingleton priority key value
    end;

fun treeSingleton key_value =
    let
      val node = nodeSingleton key_value
    in
      T node
    end;

(* ------------------------------------------------------------------------- *)
(* Appending two trees, where every element of the first tree is less than   *)
(* every element of the second tree.                                         *)
(* ------------------------------------------------------------------------- *)

fun treeAppend tree1 tree2 =
    case tree1 of
      E => tree2
    | T node1 =>
      case tree2 of
        E => tree1
      | T node2 =>
        if lowerPriorityNode node1 node2 then
          let
            val Node {priority,left,key,value,right,...} = node2

            val left = treeAppend tree1 left
          in
            mkTree priority left key value right
          end
        else
          let
            val Node {priority,left,key,value,right,...} = node1

            val right = treeAppend right tree2
          in
            mkTree priority left key value right
          end;

(* ------------------------------------------------------------------------- *)
(* Appending two trees and a node, where every element of the first tree is  *)
(* less than the node, which in turn is less than every element of the       *)
(* second tree.                                                              *)
(* ------------------------------------------------------------------------- *)

fun treeCombine left node right =
    let
      val left_node = treeAppend left (T node)
    in
      treeAppend left_node right
    end;

(* ------------------------------------------------------------------------- *)
(* Searching a tree for a value.                                             *)
(* ------------------------------------------------------------------------- *)

fun treePeek pkey tree =
    case tree of
      E => NONE
    | T node => nodePeek pkey node

and nodePeek pkey node =
    let
      val Node {left,key,value,right,...} = node
    in
      case compareKey (pkey,key) of
        LESS => treePeek pkey left
      | EQUAL => SOME value
      | GREATER => treePeek pkey right
    end;

(* ------------------------------------------------------------------------- *)
(* Tree paths.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Generating a path by searching a tree for a key/value pair *)

fun treePeekPath pkey path tree =
    case tree of
      E => (path,NONE)
    | T node => nodePeekPath pkey path node

and nodePeekPath pkey path node =
    let
      val Node {left,key,right,...} = node
    in
      case compareKey (pkey,key) of
        LESS => treePeekPath pkey ((true,node) :: path) left
      | EQUAL => (path, SOME node)
      | GREATER => treePeekPath pkey ((false,node) :: path) right
    end;

(* A path splits a tree into left/right components *)

fun addSidePath ((wentLeft,node),(leftTree,rightTree)) =
    let
      val Node {priority,left,key,value,right,...} = node
    in
      if wentLeft then (leftTree, mkTree priority rightTree key value right)
      else (mkTree priority left key value leftTree, rightTree)
    end;

fun addSidesPath left_right = List.foldl addSidePath left_right;

fun mkSidesPath path = addSidesPath (E,E) path;

(* Updating the subtree at a path *)

local
  fun updateTree ((wentLeft,node),tree) =
      let
        val Node {priority,left,key,value,right,...} = node
      in
        if wentLeft then mkTree priority tree key value right
        else mkTree priority left key value tree
      end;
in
  fun updateTreePath tree = List.foldl updateTree tree;
end;

(* Inserting a new node at a path position *)

fun insertNodePath node =
    let
      fun insert left_right path =
          case path of
            [] =>
            let
              val (left,right) = left_right
            in
              treeCombine left node right
            end
          | (step as (_,snode)) :: rest =>
            if lowerPriorityNode snode node then
              let
                val left_right = addSidePath (step,left_right)
              in
                insert left_right rest
              end
            else
              let
                val (left,right) = left_right

                val tree = treeCombine left node right
              in
                updateTreePath tree path
              end
    in
      insert (E,E)
    end;

(* ------------------------------------------------------------------------- *)
(* Using a key to split a node into three components: the keys comparing     *)
(* less than the supplied key, an optional equal key, and the keys comparing *)
(* greater.                                                                  *)
(* ------------------------------------------------------------------------- *)

fun nodePartition pkey node =
    let
      val (path,pnode) = nodePeekPath pkey [] node
    in
      case pnode of
        NONE =>
        let
          val (left,right) = mkSidesPath path
        in
          (left,NONE,right)
        end
      | SOME node =>
        let
          val Node {left,key,value,right,...} = node

          val (left,right) = addSidesPath (left,right) path
        in
          (left, SOME (key,value), right)
        end
    end;

(* ------------------------------------------------------------------------- *)
(* Searching a tree for a key/value pair.                                    *)
(* ------------------------------------------------------------------------- *)

fun treePeekKey pkey tree =
    case tree of
      E => NONE
    | T node => nodePeekKey pkey node

and nodePeekKey pkey node =
    let
      val Node {left,key,value,right,...} = node
    in
      case compareKey (pkey,key) of
        LESS => treePeekKey pkey left
      | EQUAL => SOME (key,value)
      | GREATER => treePeekKey pkey right
    end;

(* ------------------------------------------------------------------------- *)
(* Inserting new key/values into the tree.                                   *)
(* ------------------------------------------------------------------------- *)

fun treeInsert key_value tree =
    let
      val (key,value) = key_value

      val (path,inode) = treePeekPath key [] tree
    in
      case inode of
        NONE =>
        let
          val node = nodeSingleton (key,value)
        in
          insertNodePath node path
        end
      | SOME node =>
        let
          val Node {size,priority,left,right,...} = node

          val node =
              Node
                {size = size,
                 priority = priority,
                 left = left,
                 key = key,
                 value = value,
                 right = right}
        in
          updateTreePath (T node) path
        end
    end;

(* ------------------------------------------------------------------------- *)
(* Deleting key/value pairs: it raises an exception if the supplied key is   *)
(* not present.                                                              *)
(* ------------------------------------------------------------------------- *)

fun treeDelete dkey tree =
    case tree of
      E => raise Bug "KeyMap.delete: element not found"
    | T node => nodeDelete dkey node

and nodeDelete dkey node =
    let
      val Node {size,priority,left,key,value,right} = node
    in
      case compareKey (dkey,key) of
        LESS =>
        let
          val size = size - 1
          and left = treeDelete dkey left

          val node =
              Node
                {size = size,
                 priority = priority,
                 left = left,
                 key = key,
                 value = value,
                 right = right}
        in
          T node
        end
      | EQUAL => treeAppend left right
      | GREATER =>
        let
          val size = size - 1
          and right = treeDelete dkey right

          val node =
              Node
                {size = size,
                 priority = priority,
                 left = left,
                 key = key,
                 value = value,
                 right = right}
        in
          T node
        end
    end;

(* ------------------------------------------------------------------------- *)
(* Partial map is the basic operation for preserving tree structure.         *)
(* It applies its argument function to the elements *in order*.              *)
(* ------------------------------------------------------------------------- *)

fun treeMapPartial f tree =
    case tree of
      E => E
    | T node => nodeMapPartial f node

and nodeMapPartial f (Node {priority,left,key,value,right,...}) =
    let
      val left = treeMapPartial f left
      and vo = f (key,value)
      and right = treeMapPartial f right
    in
      case vo of
        NONE => treeAppend left right
      | SOME value => mkTree priority left key value right
    end;

(* ------------------------------------------------------------------------- *)
(* Mapping tree values.                                                      *)
(* ------------------------------------------------------------------------- *)

fun treeMap f tree =
    case tree of
      E => E
    | T node => T (nodeMap f node)

and nodeMap f node =
    let
      val Node {size,priority,left,key,value,right} = node

      val left = treeMap f left
      and value = f (key,value)
      and right = treeMap f right
    in
      Node
        {size = size,
         priority = priority,
         left = left,
         key = key,
         value = value,
         right = right}
    end;

(* ------------------------------------------------------------------------- *)
(* Merge is the basic operation for joining two trees. Note that the merged  *)
(* key is always the one from the second map.                                *)
(* ------------------------------------------------------------------------- *)

fun treeMerge f1 f2 fb tree1 tree2 =
    case tree1 of
      E => treeMapPartial f2 tree2
    | T node1 =>
      case tree2 of
        E => treeMapPartial f1 tree1
      | T node2 => nodeMerge f1 f2 fb node1 node2

and nodeMerge f1 f2 fb node1 node2 =
    let
      val Node {priority,left,key,value,right,...} = node2

      val (l,kvo,r) = nodePartition key node1

      val left = treeMerge f1 f2 fb l left
      and right = treeMerge f1 f2 fb r right

      val vo =
          case kvo of
            NONE => f2 (key,value)
          | SOME kv => fb (kv,(key,value))
    in
      case vo of
        NONE => treeAppend left right
      | SOME value =>
        let
          val node = mkNodeSingleton priority key value
        in
          treeCombine left node right
        end
    end;

(* ------------------------------------------------------------------------- *)
(* A union operation on trees.                                               *)
(* ------------------------------------------------------------------------- *)

fun treeUnion f f2 tree1 tree2 =
    case tree1 of
      E => tree2
    | T node1 =>
      case tree2 of
        E => tree1
      | T node2 => nodeUnion f f2 node1 node2

and nodeUnion f f2 node1 node2 =
    if pointerEqual (node1,node2) then nodeMapPartial f2 node1
    else
      let
        val Node {priority,left,key,value,right,...} = node2

        val (l,kvo,r) = nodePartition key node1

        val left = treeUnion f f2 l left
        and right = treeUnion f f2 r right

        val vo =
            case kvo of
              NONE => SOME value
            | SOME kv => f (kv,(key,value))
      in
        case vo of
          NONE => treeAppend left right
        | SOME value =>
          let
            val node = mkNodeSingleton priority key value
          in
            treeCombine left node right
          end
      end;

(* ------------------------------------------------------------------------- *)
(* An intersect operation on trees.                                          *)
(* ------------------------------------------------------------------------- *)

fun treeIntersect f t1 t2 =
    case t1 of
      E => E
    | T n1 =>
      case t2 of
        E => E
      | T n2 => nodeIntersect f n1 n2

and nodeIntersect f n1 n2 =
    let
      val Node {priority,left,key,value,right,...} = n2

      val (l,kvo,r) = nodePartition key n1

      val left = treeIntersect f l left
      and right = treeIntersect f r right

      val vo =
          case kvo of
            NONE => NONE
          | SOME kv => f (kv,(key,value))
    in
      case vo of
        NONE => treeAppend left right
      | SOME value => mkTree priority left key value right
    end;

(* ------------------------------------------------------------------------- *)
(* A union operation on trees which simply chooses the second value.         *)
(* ------------------------------------------------------------------------- *)

fun treeUnionDomain tree1 tree2 =
    case tree1 of
      E => tree2
    | T node1 =>
      case tree2 of
        E => tree1
      | T node2 =>
        if pointerEqual (node1,node2) then tree2
        else nodeUnionDomain node1 node2

and nodeUnionDomain node1 node2 =
    let
      val Node {priority,left,key,value,right,...} = node2

      val (l,_,r) = nodePartition key node1

      val left = treeUnionDomain l left
      and right = treeUnionDomain r right

      val node = mkNodeSingleton priority key value
    in
      treeCombine left node right
    end;

(* ------------------------------------------------------------------------- *)
(* An intersect operation on trees which simply chooses the second value.    *)
(* ------------------------------------------------------------------------- *)

fun treeIntersectDomain tree1 tree2 =
    case tree1 of
      E => E
    | T node1 =>
      case tree2 of
        E => E
      | T node2 =>
        if pointerEqual (node1,node2) then tree2
        else nodeIntersectDomain node1 node2

and nodeIntersectDomain node1 node2 =
    let
      val Node {priority,left,key,value,right,...} = node2

      val (l,kvo,r) = nodePartition key node1

      val left = treeIntersectDomain l left
      and right = treeIntersectDomain r right
    in
      if Option.isSome kvo then mkTree priority left key value right
      else treeAppend left right
    end;

(* ------------------------------------------------------------------------- *)
(* A difference operation on trees.                                          *)
(* ------------------------------------------------------------------------- *)

fun treeDifferenceDomain t1 t2 =
    case t1 of
      E => E
    | T n1 =>
      case t2 of
        E => t1
      | T n2 => nodeDifferenceDomain n1 n2

and nodeDifferenceDomain n1 n2 =
    if pointerEqual (n1,n2) then E
    else
      let
        val Node {priority,left,key,value,right,...} = n1

        val (l,kvo,r) = nodePartition key n2

        val left = treeDifferenceDomain left l
        and right = treeDifferenceDomain right r
      in
        if Option.isSome kvo then treeAppend left right
        else mkTree priority left key value right
      end;

(* ------------------------------------------------------------------------- *)
(* A subset operation on trees.                                              *)
(* ------------------------------------------------------------------------- *)

fun treeSubsetDomain tree1 tree2 =
    case tree1 of
      E => true
    | T node1 =>
      case tree2 of
        E => false
      | T node2 => nodeSubsetDomain node1 node2

and nodeSubsetDomain node1 node2 =
    pointerEqual (node1,node2) orelse
    let
      val Node {size,left,key,right,...} = node1
    in
      size <= nodeSize node2 andalso
      let
        val (l,kvo,r) = nodePartition key node2
      in
        Option.isSome kvo andalso
        treeSubsetDomain left l andalso
        treeSubsetDomain right r
      end
    end;

(* ------------------------------------------------------------------------- *)
(* Picking an arbitrary key/value pair from a tree.                          *)
(* ------------------------------------------------------------------------- *)

fun nodePick node =
    let
      val Node {key,value,...} = node
    in
      (key,value)
    end;

fun treePick tree =
    case tree of
      E => raise Bug "KeyMap.treePick"
    | T node => nodePick node;

(* ------------------------------------------------------------------------- *)
(* Removing an arbitrary key/value pair from a tree.                         *)
(* ------------------------------------------------------------------------- *)

fun nodeDeletePick node =
    let
      val Node {left,key,value,right,...} = node
    in
      ((key,value), treeAppend left right)
    end;

fun treeDeletePick tree =
    case tree of
      E => raise Bug "KeyMap.treeDeletePick"
    | T node => nodeDeletePick node;

(* ------------------------------------------------------------------------- *)
(* Finding the nth smallest key/value (counting from 0).                     *)
(* ------------------------------------------------------------------------- *)

fun treeNth n tree =
    case tree of
      E => raise Bug "KeyMap.treeNth"
    | T node => nodeNth n node

and nodeNth n node =
    let
      val Node {left,key,value,right,...} = node

      val k = treeSize left
    in
      if n = k then (key,value)
      else if n < k then treeNth n left
      else treeNth (n - (k + 1)) right
    end;

(* ------------------------------------------------------------------------- *)
(* Removing the nth smallest key/value (counting from 0).                    *)
(* ------------------------------------------------------------------------- *)

fun treeDeleteNth n tree =
    case tree of
      E => raise Bug "KeyMap.treeDeleteNth"
    | T node => nodeDeleteNth n node

and nodeDeleteNth n node =
    let
      val Node {size,priority,left,key,value,right} = node

      val k = treeSize left
    in
      if n = k then ((key,value), treeAppend left right)
      else if n < k then
        let
          val (key_value,left) = treeDeleteNth n left

          val size = size - 1

          val node =
              Node
                {size = size,
                 priority = priority,
                 left = left,
                 key = key,
                 value = value,
                 right = right}
        in
          (key_value, T node)
        end
      else
        let
          val n = n - (k + 1)

          val (key_value,right) = treeDeleteNth n right

          val size = size - 1

          val node =
              Node
                {size = size,
                 priority = priority,
                 left = left,
                 key = key,
                 value = value,
                 right = right}
        in
          (key_value, T node)
        end
    end;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

datatype 'value iterator =
    LR of (key * 'value) * 'value tree * 'value node list
  | RL of (key * 'value) * 'value tree * 'value node list;

fun fromSpineLR nodes =
    case nodes of
      [] => NONE
    | Node {key,value,right,...} :: nodes =>
      SOME (LR ((key,value),right,nodes));

fun fromSpineRL nodes =
    case nodes of
      [] => NONE
    | Node {key,value,left,...} :: nodes =>
      SOME (RL ((key,value),left,nodes));

fun addLR nodes tree = fromSpineLR (treeLeftSpine nodes tree);

fun addRL nodes tree = fromSpineRL (treeRightSpine nodes tree);

fun treeMkIterator tree = addLR [] tree;

fun treeMkRevIterator tree = addRL [] tree;

fun readIterator iter =
    case iter of
      LR (key_value,_,_) => key_value
    | RL (key_value,_,_) => key_value;

fun advanceIterator iter =
    case iter of
      LR (_,tree,nodes) => addLR nodes tree
    | RL (_,tree,nodes) => addRL nodes tree;

fun foldIterator f acc io =
    case io of
      NONE => acc
    | SOME iter =>
      let
        val (key,value) = readIterator iter
      in
        foldIterator f (f (key,value,acc)) (advanceIterator iter)
      end;

fun findIterator pred io =
    case io of
      NONE => NONE
    | SOME iter =>
      let
        val key_value = readIterator iter
      in
        if pred key_value then SOME key_value
        else findIterator pred (advanceIterator iter)
      end;

fun firstIterator f io =
    case io of
      NONE => NONE
    | SOME iter =>
      let
        val key_value = readIterator iter
      in
        case f key_value of
          NONE => firstIterator f (advanceIterator iter)
        | s => s
      end;

fun compareIterator compareValue io1 io2 =
    case (io1,io2) of
      (NONE,NONE) => EQUAL
    | (NONE, SOME _) => LESS
    | (SOME _, NONE) => GREATER
    | (SOME i1, SOME i2) =>
      let
        val (k1,v1) = readIterator i1
        and (k2,v2) = readIterator i2
      in
        case compareKey (k1,k2) of
          LESS => LESS
        | EQUAL =>
          (case compareValue (v1,v2) of
             LESS => LESS
           | EQUAL =>
             let
               val io1 = advanceIterator i1
               and io2 = advanceIterator i2
             in
               compareIterator compareValue io1 io2
             end
           | GREATER => GREATER)
        | GREATER => GREATER
      end;

fun equalIterator equalValue io1 io2 =
    case (io1,io2) of
      (NONE,NONE) => true
    | (NONE, SOME _) => false
    | (SOME _, NONE) => false
    | (SOME i1, SOME i2) =>
      let
        val (k1,v1) = readIterator i1
        and (k2,v2) = readIterator i2
      in
        equalKey k1 k2 andalso
        equalValue v1 v2 andalso
        let
          val io1 = advanceIterator i1
          and io2 = advanceIterator i2
        in
          equalIterator equalValue io1 io2
        end
      end;

(* ------------------------------------------------------------------------- *)
(* A type of finite maps.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype 'value map =
    Map of 'value tree;

(* ------------------------------------------------------------------------- *)
(* Map debugging functions.                                                  *)
(* ------------------------------------------------------------------------- *)

(*BasicDebug
fun checkInvariants s m =
    let
      val Map tree = m

      val _ = treeCheckInvariants tree
    in
      m
    end
    handle Bug bug => raise Bug (s ^ "\n" ^ "KeyMap.checkInvariants: " ^ bug);
*)

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

fun new () =
    let
      val tree = treeNew ()
    in
      Map tree
    end;

fun singleton key_value =
    let
      val tree = treeSingleton key_value
    in
      Map tree
    end;

(* ------------------------------------------------------------------------- *)
(* Map size.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun size (Map tree) = treeSize tree;

fun null m = size m = 0;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun peekKey (Map tree) key = treePeekKey key tree;

fun peek (Map tree) key = treePeek key tree;

fun inDomain key m = Option.isSome (peek m key);

fun get m key =
    case peek m key of
      NONE => raise Error "KeyMap.get: element not found"
    | SOME value => value;

fun pick (Map tree) = treePick tree;

fun nth (Map tree) n = treeNth n tree;

fun random m =
    let
      val n = size m
    in
      if n = 0 then raise Bug "KeyMap.random: empty"
      else nth m (randomInt n)
    end;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

fun insert (Map tree) key_value =
    let
      val tree = treeInsert key_value tree
    in
      Map tree
    end;

(*BasicDebug
val insert = fn m => fn kv =>
    checkInvariants "KeyMap.insert: result"
      (insert (checkInvariants "KeyMap.insert: input" m) kv);
*)

fun insertList m =
    let
      fun ins (key_value,acc) = insert acc key_value
    in
      List.foldl ins m
    end;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun delete (Map tree) dkey =
    let
      val tree = treeDelete dkey tree
    in
      Map tree
    end;

(*BasicDebug
val delete = fn m => fn k =>
    checkInvariants "KeyMap.delete: result"
      (delete (checkInvariants "KeyMap.delete: input" m) k);
*)

fun remove m key = if inDomain key m then delete m key else m;

fun deletePick (Map tree) =
    let
      val (key_value,tree) = treeDeletePick tree
    in
      (key_value, Map tree)
    end;

(*BasicDebug
val deletePick = fn m =>
    let
      val (kv,m) = deletePick (checkInvariants "KeyMap.deletePick: input" m)
    in
      (kv, checkInvariants "KeyMap.deletePick: result" m)
    end;
*)

fun deleteNth (Map tree) n =
    let
      val (key_value,tree) = treeDeleteNth n tree
    in
      (key_value, Map tree)
    end;

(*BasicDebug
val deleteNth = fn m => fn n =>
    let
      val (kv,m) = deleteNth (checkInvariants "KeyMap.deleteNth: input" m) n
    in
      (kv, checkInvariants "KeyMap.deleteNth: result" m)
    end;
*)

fun deleteRandom m =
    let
      val n = size m
    in
      if n = 0 then raise Bug "KeyMap.deleteRandom: empty"
      else deleteNth m (randomInt n)
    end;

(* ------------------------------------------------------------------------- *)
(* Joining (all join operations prefer keys in the second map).              *)
(* ------------------------------------------------------------------------- *)

fun merge {first,second,both} (Map tree1) (Map tree2) =
    let
      val tree = treeMerge first second both tree1 tree2
    in
      Map tree
    end;

(*BasicDebug
val merge = fn f => fn m1 => fn m2 =>
    checkInvariants "KeyMap.merge: result"
      (merge f
         (checkInvariants "KeyMap.merge: input 1" m1)
         (checkInvariants "KeyMap.merge: input 2" m2));
*)

fun union f (Map tree1) (Map tree2) =
    let
      fun f2 kv = f (kv,kv)

      val tree = treeUnion f f2 tree1 tree2
    in
      Map tree
    end;

(*BasicDebug
val union = fn f => fn m1 => fn m2 =>
    checkInvariants "KeyMap.union: result"
      (union f
         (checkInvariants "KeyMap.union: input 1" m1)
         (checkInvariants "KeyMap.union: input 2" m2));
*)

fun intersect f (Map tree1) (Map tree2) =
    let
      val tree = treeIntersect f tree1 tree2
    in
      Map tree
    end;

(*BasicDebug
val intersect = fn f => fn m1 => fn m2 =>
    checkInvariants "KeyMap.intersect: result"
      (intersect f
         (checkInvariants "KeyMap.intersect: input 1" m1)
         (checkInvariants "KeyMap.intersect: input 2" m2));
*)

(* ------------------------------------------------------------------------- *)
(* Iterators over maps.                                                      *)
(* ------------------------------------------------------------------------- *)

fun mkIterator (Map tree) = treeMkIterator tree;

fun mkRevIterator (Map tree) = treeMkRevIterator tree;

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

fun mapPartial f (Map tree) =
    let
      val tree = treeMapPartial f tree
    in
      Map tree
    end;

(*BasicDebug
val mapPartial = fn f => fn m =>
    checkInvariants "KeyMap.mapPartial: result"
      (mapPartial f (checkInvariants "KeyMap.mapPartial: input" m));
*)

fun map f (Map tree) =
    let
      val tree = treeMap f tree
    in
      Map tree
    end;

(*BasicDebug
val map = fn f => fn m =>
    checkInvariants "KeyMap.map: result"
      (map f (checkInvariants "KeyMap.map: input" m));
*)

fun transform f = map (fn (_,value) => f value);

fun filter pred =
    let
      fun f (key_value as (_,value)) =
          if pred key_value then SOME value else NONE
    in
      mapPartial f
    end;

fun partition p =
    let
      fun np x = not (p x)
    in
      fn m => (filter p m, filter np m)
    end;

fun foldl f b m = foldIterator f b (mkIterator m);

fun foldr f b m = foldIterator f b (mkRevIterator m);

fun app f m = foldl (fn (key,value,()) => f (key,value)) () m;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

fun findl p m = findIterator p (mkIterator m);

fun findr p m = findIterator p (mkRevIterator m);

fun firstl f m = firstIterator f (mkIterator m);

fun firstr f m = firstIterator f (mkRevIterator m);

fun exists p m = Option.isSome (findl p m);

fun all p =
    let
      fun np x = not (p x)
    in
      fn m => not (exists np m)
    end;

fun count pred =
    let
      fun f (k,v,acc) = if pred (k,v) then acc + 1 else acc
    in
      foldl f 0
    end;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

fun compare compareValue (m1,m2) =
    if pointerEqual (m1,m2) then EQUAL
    else
      case Int.compare (size m1, size m2) of
        LESS => LESS
      | EQUAL =>
        let
          val Map _ = m1

          val io1 = mkIterator m1
          and io2 = mkIterator m2
        in
          compareIterator compareValue io1 io2
        end
      | GREATER => GREATER;

fun equal equalValue m1 m2 =
    pointerEqual (m1,m2) orelse
    (size m1 = size m2 andalso
     let
       val Map _ = m1

       val io1 = mkIterator m1
       and io2 = mkIterator m2
     in
       equalIterator equalValue io1 io2
     end);

(* ------------------------------------------------------------------------- *)
(* Set operations on the domain.                                             *)
(* ------------------------------------------------------------------------- *)

fun unionDomain (Map tree1) (Map tree2) =
    let
      val tree = treeUnionDomain tree1 tree2
    in
      Map tree
    end;

(*BasicDebug
val unionDomain = fn m1 => fn m2 =>
    checkInvariants "KeyMap.unionDomain: result"
      (unionDomain
         (checkInvariants "KeyMap.unionDomain: input 1" m1)
         (checkInvariants "KeyMap.unionDomain: input 2" m2));
*)

local
  fun uncurriedUnionDomain (m,acc) = unionDomain acc m;
in
  fun unionListDomain ms =
      case ms of
        [] => raise Bug "KeyMap.unionListDomain: no sets"
      | m :: ms => List.foldl uncurriedUnionDomain m ms;
end;

fun intersectDomain (Map tree1) (Map tree2) =
    let
      val tree = treeIntersectDomain tree1 tree2
    in
      Map tree
    end;

(*BasicDebug
val intersectDomain = fn m1 => fn m2 =>
    checkInvariants "KeyMap.intersectDomain: result"
      (intersectDomain
         (checkInvariants "KeyMap.intersectDomain: input 1" m1)
         (checkInvariants "KeyMap.intersectDomain: input 2" m2));
*)

local
  fun uncurriedIntersectDomain (m,acc) = intersectDomain acc m;
in
  fun intersectListDomain ms =
      case ms of
        [] => raise Bug "KeyMap.intersectListDomain: no sets"
      | m :: ms => List.foldl uncurriedIntersectDomain m ms;
end;

fun differenceDomain (Map tree1) (Map tree2) =
    let
      val tree = treeDifferenceDomain tree1 tree2
    in
      Map tree
    end;

(*BasicDebug
val differenceDomain = fn m1 => fn m2 =>
    checkInvariants "KeyMap.differenceDomain: result"
      (differenceDomain
         (checkInvariants "KeyMap.differenceDomain: input 1" m1)
         (checkInvariants "KeyMap.differenceDomain: input 2" m2));
*)

fun symmetricDifferenceDomain m1 m2 =
    unionDomain (differenceDomain m1 m2) (differenceDomain m2 m1);

fun equalDomain m1 m2 = equal (K (K true)) m1 m2;

fun subsetDomain (Map tree1) (Map tree2) =
    treeSubsetDomain tree1 tree2;

fun disjointDomain m1 m2 = null (intersectDomain m1 m2);

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

fun keys m = foldr (fn (key,_,l) => key :: l) [] m;

fun values m = foldr (fn (_,value,l) => value :: l) [] m;

fun toList m = foldr (fn (key,value,l) => (key,value) :: l) [] m;

fun fromList l =
    let
      val m = new ()
    in
      insertList m l
    end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun toString m = "<" ^ (if null m then "" else Int.toString (size m)) ^ ">";

end

structure IntMap =
KeyMap (IntOrdered);

structure IntPairMap =
KeyMap (IntPairOrdered);

structure StringMap =
KeyMap (StringOrdered);
