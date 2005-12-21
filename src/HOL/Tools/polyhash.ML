(* Modified for Poly/ML from SML/NJ Library version 0.2
 *
 * COPYRIGHT (c) 1992 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *
 * Original author: John Reppy, AT&T Bell Laboratories, Murray Hill, NJ 07974
 * Current version largely by Joseph Hurd
 *)

(* Polyhash -- polymorphic hashtables as in the SML/NJ Library *)

signature Polyhash =
sig

type ('key, 'data) hash_table

val mkTable     : ('_key -> int) * ('_key * '_key -> bool) -> int * exn 
                  -> ('_key, '_data) hash_table
val numItems    : ('key, 'data) hash_table -> int
val insert      : ('_key, '_data) hash_table -> '_key * '_data -> unit
val peekInsert  : ('_key, '_data) hash_table -> '_key * '_data 
                  -> '_data option
val find        : ('key, 'data) hash_table -> 'key -> 'data
val peek        : ('key, 'data) hash_table -> 'key -> 'data option
val remove      : ('key, 'data) hash_table -> 'key -> 'data
val listItems   : ('key, 'data) hash_table -> ('key * 'data) list
val apply       : ('key * 'data -> unit) -> ('key, 'data) hash_table -> unit
val map         : ('_key * 'data -> '_res) -> ('_key, 'data) hash_table 
                  -> ('_key, '_res) hash_table
val filter      : ('key * 'data -> bool) -> ('key, 'data) hash_table -> unit
val transform   : ('data -> '_res) -> ('_key, 'data) hash_table 
                  -> ('_key, '_res) hash_table
val copy        : ('_key, '_data) hash_table -> ('_key, '_data) hash_table
val bucketSizes : ('key, 'data) hash_table -> int list

(*Additions due to L. C. Paulson and Jia Meng*)
val hashw : word * word -> word
val hashw_char : Char.char * word -> word
val hashw_vector : word Vector.vector * word -> word
val hashw_string : string * word -> word
val hashw_strings : string list * word -> word
val hash_string : string -> int

(* 
   [('key, 'data) hash_table] is the type of hashtables with keys of type
   'key and data values of type 'data.

   [mkTable (hashVal, sameKey) (sz, exc)] returns a new hashtable,
   using hash function hashVal and equality predicate sameKey.  The sz
   is a size hint, and exc is the exception raised by function find.
   It must be the case that sameKey(k1, k2) implies hashVal(k1) =
   hashVal(k2) for all k1,k2.

   [numItems htbl] is the number of items in the hash table.

   [insert htbl (k, d)] inserts data d for key k.  If k already had an
   item associated with it, then the old item is overwritten.

   [find htbl k] returns d, where d is the data item associated with key k, 
   or raises the exception (given at creation of htbl) if there is no such d.

   [peek htbl k] returns SOME d, where d is the data item associated with 
   key k, or NONE if there is no such d.

   [peekInsert htbl (k, d)] inserts data d for key k, if k is not
   already in the table, returning NONE.  If k is already in the
   table, and the associated data value is d', then returns SOME d'
   and leaves the table unmodified.

   [remove htbl k] returns d, where d is the data item associated with key k, 
   removing d from the table; or raises the exception if there is no such d.

   [listItems htbl] returns a list of the (key, data) pairs in the hashtable.

   [apply f htbl] applies function f to all (key, data) pairs in the 
   hashtable, in some order.

   [map f htbl] returns a new hashtable, whose data items have been
   obtained by applying f to the (key, data) pairs in htbl.  The new
   tables have the same keys, hash function, equality predicate, and
   exception, as htbl.

   [filter p htbl] deletes from htbl all data items which do not
   satisfy predicate p.

   [transform f htbl] as map, but only the (old) data values are used
   when computing the new data values.

   [copy htbl] returns a complete copy of htbl.

   [bucketSizes htbl] returns a list of the sizes of the buckets.
   This is to allow users to gauge the quality of their hashing
   function.  
*)

end


structure Polyhash :> Polyhash =
struct

datatype ('key, 'data) bucket_t
  = NIL
  | B of int * 'key * 'data * ('key, 'data) bucket_t

datatype ('key, 'data) hash_table = 
    HT of {hashVal   : 'key -> int,
	   sameKey   : 'key * 'key -> bool,
	   not_found : exn,
	   table     : ('key, 'data) bucket_t Array.array ref,
	   n_items   : int ref}

local
(*
    prim_val andb_      : int -> int -> int = 2 "and";
    prim_val lshift_    : int -> int -> int = 2 "shift_left";
*)
    fun andb_ x y = Word.toInt (Word.andb (Word.fromInt x, Word.fromInt y));
    fun lshift_ x y = Word.toInt (Word.<< (Word.fromInt x, Word.fromInt y));
in 
    fun index (i, sz) = andb_ i (sz-1)

  (* find smallest power of 2 (>= 32) that is >= n *)
    fun roundUp n = 
	let fun f i = if (i >= n) then i else f (lshift_ i 1)
	in f 32 end
end;

  (* Create a new table; the int is a size hint and the exception
   * is to be raised by find.
   *)
    fun mkTable (hashVal, sameKey) (sizeHint, notFound) = HT{
            hashVal=hashVal,
	    sameKey=sameKey,
	    not_found = notFound,
	    table = ref (Array.array(roundUp sizeHint, NIL)),
	    n_items = ref 0
	  };

  (* conditionally grow a table *)
    fun growTable (HT{table, n_items, ...}) = let
	    val arr = !table
	    val sz = Array.length arr
	    in
	      if (!n_items >= sz)
		then let
		  val newSz = sz+sz
		  val newArr = Array.array (newSz, NIL)
		  fun copy NIL = ()
		    | copy (B(h, key, v, rest)) = let
			val indx = index (h, newSz)
			in
			  Array.update (newArr, indx,
			    B(h, key, v, Array.sub(newArr, indx)));
			  copy rest
			end
		  fun bucket n = (copy (Array.sub(arr, n)); bucket (n+1))
		  in
		    (bucket 0) handle _ => ();
		    table := newArr
		  end
		else ()
	    end (* growTable *);

  (* Insert an item.  If the key already has an item associated with it,
   * then the old item is discarded.
   *)
    fun insert (tbl as HT{hashVal, sameKey, table, n_items, ...}) (key, item) =
	let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = (
		Array.update(arr, indx, B(hash, key, item, Array.sub(arr, indx)));
		n_items := !n_items + 1;
		growTable tbl;
		NIL)
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then B(hash, key, item, r)
		else (case (look r)
		   of NIL => NIL
		    | rest => B(h, k, v, rest)
		  (* end case *))
	  in
	    case (look (Array.sub (arr, indx)))
	     of NIL => ()
	      | b => Array.update(arr, indx, b)
	  end;

  (* Insert an item if not there already; if it is there already, 
     then return the old data value and leave the table unmodified..
   *)
    fun peekInsert (tbl as HT{hashVal, sameKey, table, n_items, ...}) (key, item) =
	let val arr = !table
	    val sz = Array.length arr
	    val hash = hashVal key
	    val indx = index (hash, sz)
	    fun look NIL = 
		(Array.update(arr, indx, B(hash, key, item, 
					   Array.sub(arr, indx)));
		 n_items := !n_items + 1;
		 growTable tbl;
		 NONE)
	      | look (B(h, k, v, r)) = 
		if hash = h andalso sameKey(key, k) then SOME v
		else look r
	in
	    look (Array.sub (arr, indx))
	end;

  (* find an item, the table's exception is raised if the item doesn't exist *)
    fun find (HT{hashVal, sameKey, table, not_found, ...}) key = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = raise not_found
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then v
		else look r
	  in
	    look (Array.sub (arr, indx))
	  end;

  (* look for an item, return NONE if the item doesn't exist *)
    fun peek (HT{hashVal, sameKey, table, ...}) key = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = NONE
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then SOME v
		else look r
	  in
	    look (Array.sub (arr, indx))
	  end;

  (* Remove an item.  The table's exception is raised if
   * the item doesn't exist.
   *)
    fun remove (HT{hashVal, sameKey, not_found, table, n_items}) key = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = raise not_found
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then (v, r)
		else let val (item, r') = look r in (item, B(h, k, v, r')) end
	  val (item, bucket) = look (Array.sub (arr, indx))
	  in
	    Array.update (arr, indx, bucket);
	    n_items := !n_items - 1;
	    item
	  end (* remove *);

  (* Return the number of items in the table *)
   fun numItems (HT{n_items, ...}) = !n_items

  (* return a list of the items in the table *)
    fun listItems (HT{table = ref arr, n_items, ...}) = let
	  fun f (_, l, 0) = l
	    | f (~1, l, _) = l
	    | f (i, l, n) = let
		fun g (NIL, l, n) = f (i-1, l, n)
		  | g (B(_, k, v, r), l, n) = g(r, (k, v)::l, n-1)
		in
		  g (Array.sub(arr, i), l, n)
		end
	  in
	    f ((Array.length arr) - 1, [], !n_items)
	  end (* listItems *);

  (* Apply a function to the entries of the table *)
    fun apply f (HT{table, ...}) = let
	  fun appF NIL = ()
	    | appF (B(_, key, item, rest)) = (
		f (key, item);
		appF rest)
	  val arr = !table
	  val sz = Array.length arr
	  fun appToTbl i = if (i < sz)
		then (appF (Array.sub (arr, i)); appToTbl(i+1))
		else ()
	  in
	    appToTbl 0
	  end (* apply *);

  (* Map a table to a new table that has the same keys and exception *)
    fun map f (HT{hashVal, sameKey, table, n_items, not_found}) = let
	  fun mapF NIL = NIL
	    | mapF (B(hash, key, item, rest)) =
		B(hash, key, f (key, item), mapF rest)
	  val arr = !table
	  val sz = Array.length arr
	  val newArr = Array.array (sz, NIL)
	  fun mapTbl i = if (i < sz)
		then (
		  Array.update(newArr, i, mapF (Array.sub(arr, i)));
		  mapTbl (i+1))
		else ()
	  in
	    mapTbl 0;
	    HT{hashVal=hashVal,
	       sameKey=sameKey,
	       table = ref newArr, 
	       n_items = ref(!n_items), 
	       not_found = not_found}
	  end (* transform *);

  (* remove any hash table items that do not satisfy the given
   * predicate.
   *)
    fun filter pred (HT{table, n_items, not_found, ...}) = let
	  fun filterP NIL = NIL
	    | filterP (B(hash, key, item, rest)) = if (pred(key, item))
		then B(hash, key, item, filterP rest)
		else filterP rest
	  val arr = !table
	  val sz = Array.length arr
	  fun filterTbl i = if (i < sz)
		then (
		  Array.update (arr, i, filterP (Array.sub (arr, i)));
		  filterTbl (i+1))
		else ()
	  in
	    filterTbl 0
	  end (* filter *);

  (* Map a table to a new table that has the same keys, exception,
     hash function, and equality function *)

    fun transform f (HT{hashVal, sameKey, table, n_items, not_found}) = let
	  fun mapF NIL = NIL
	    | mapF (B(hash, key, item, rest)) = B(hash, key, f item, mapF rest)
	  val arr = !table
	  val sz = Array.length arr
	  val newArr = Array.array (sz, NIL)
	  fun mapTbl i = if (i < sz)
		then (
		  Array.update(newArr, i, mapF (Array.sub(arr, i)));
		  mapTbl (i+1))
		else ()
	  in
	    mapTbl 0;
	    HT{hashVal=hashVal, 
	       sameKey=sameKey, 
	       table = ref newArr, 
	       n_items = ref(!n_items), 
	       not_found = not_found}
	  end (* transform *);

  (* Create a copy of a hash table *)
    fun copy (HT{hashVal, sameKey, table, n_items, not_found}) = let
	  val arr = !table
	  val sz = Array.length arr
	  val newArr = Array.array (sz, NIL)
	  fun mapTbl i = (
		Array.update (newArr, i, Array.sub(arr, i));
		mapTbl (i+1))
	  in
	    (mapTbl 0) handle _ => ();
	    HT{hashVal=hashVal, 
	       sameKey=sameKey,
	       table = ref newArr, 
	       n_items = ref(!n_items), 
	       not_found = not_found}
	  end (* copy *);

  (* returns a list of the sizes of the various buckets.  This is to
   * allow users to gauge the quality of their hashing function.
   *)
    fun bucketSizes (HT{table = ref arr, ...}) = let
	  fun len (NIL, n) = n
	    | len (B(_, _, _, r), n) = len(r, n+1)
	  fun f (~1, l) = l
	    | f (i, l) = f (i-1, len (Array.sub (arr, i), 0) :: l)
	  in
	    f ((Array.length arr)-1, [])
	  end

   (*Added by lcp.
      This is essentially the hashpjw function described in Compilers:
      Principles, Techniques, and Tools, by Aho, Sethi and Ullman.*)
 (*  local infix << >>
	 val left = Word.fromInt (Word.wordSize - 4)
	 val right = Word.fromInt (Word.wordSize - 8)
	 open Word
   in  
   val mask = 0wxf << left
   fun hashw (u,w) =
     let val w' = (w << 0w4) + u
	 val g = Word.andb(w', mask)  
     in  
	 if g <> 0w0 then Word.xorb(g, Word.xorb(w', g >> right))
	 else w'
     end;
   end;*)

   (*This version is also recommended by Aho et al. and does not trigger the Poly/ML bug*)
   val hmulti = Word.fromInt 65599;
   fun hashw (u,w) = Word.+ (u, Word.*(hmulti,w))

   fun hashw_char (c,w) = hashw (Word.fromInt (Char.ord c), w);
   
   fun hashw_vector (v,w) = Vector.foldl hashw w v;
   
   fun hashw_string (s:string, w) = CharVector.foldl hashw_char w s;
   
   fun hashw_strings (ss, w) = List.foldl hashw_string w ss;

   fun hash_string s = Word.toIntX (hashw_string(s,0w0));

end
