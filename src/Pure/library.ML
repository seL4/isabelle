(*  Title:      Pure/library.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Basic library: functions, options, pairs, booleans, lists, integers,
strings, lists as sets, association lists, generic tables, balanced trees,
input / output, timing, filenames, misc functions.
*)


(** functions **)

(*handy combinators*)
fun curry f x y = f (x, y);
fun uncurry f (x, y) = f x y;
fun I x = x;
fun K x y = x;

(*combine two functions forming the union of their domains*)
infix orelf;
fun f orelf g = fn x => f x handle Match => g x;

(*application of (infix) operator to its left or right argument*)
fun apl (x, f) y = f (x, y);
fun apr (f, y) x = f (x, y);

(*functional for pairs*)
fun pairself f (x, y) = (f x, f y);

(*function exponentiation: f(...(f x)...) with n applications of f*)
fun funpow n f x =
  let fun rep (0, x) = x
        | rep (n, x) = rep (n - 1, f x)
  in rep (n, x) end;



(** options **)

datatype 'a option = None | Some of 'a;

exception OPTION of string;

fun the (Some x) = x
  | the None = raise OPTION "the";

fun is_some (Some _) = true
  | is_some None = false;

fun is_none (Some _) = false
  | is_none None = true;

fun apsome f (Some x) = Some (f x)
  | apsome _ None = None;



(** pairs **)

fun pair x y = (x, y);
fun rpair x y = (y, x);

fun fst (x, y) = x;
fun snd (x, y) = y;

fun eq_fst ((x1, _), (x2, _)) = x1 = x2;
fun eq_snd ((_, y1), (_, y2)) = y1 = y2;

fun swap (x, y) = (y, x);

(*apply the function to a component of a pair*)
fun apfst f (x, y) = (f x, y);
fun apsnd f (x, y) = (x, f y);



(** booleans **)

(* equality *)

fun equal x y = x = y;
fun not_equal x y = x <> y;


(* operators for combining predicates *)

infix orf;
fun p orf q = fn x => p x orelse q x;

infix andf;
fun p andf q = fn x => p x andalso q x;

fun notf p x = not (p x);


(* predicates on lists *)

fun orl [] = false
  | orl (x :: xs) = x orelse orl xs;

fun andl [] = true
  | andl (x :: xs) = x andalso andl xs;

(*exists pred [x1, ..., xn] ===> pred x1 orelse ... orelse pred xn*)
fun exists (pred: 'a -> bool) : 'a list -> bool =
  let fun boolf [] = false
        | boolf (x :: xs) = pred x orelse boolf xs
  in boolf end;

(*forall pred [x1, ..., xn] ===> pred x1 andalso ... andalso pred xn*)
fun forall (pred: 'a -> bool) : 'a list -> bool =
  let fun boolf [] = true
        | boolf (x :: xs) = pred x andalso boolf xs
  in boolf end;



(** lists **)

exception LIST of string;

fun null [] = true
  | null (_ :: _) = false;

fun hd [] = raise LIST "hd"
  | hd (x :: _) = x;

fun tl [] = raise LIST "tl"
  | tl (_ :: xs) = xs;

fun cons x xs = x :: xs;


(* fold *)

(*the following versions of fold are designed to fit nicely with infixes*)

(*  (op @) (e, [x1, ..., xn])  ===>  ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
fun foldl (f: 'a * 'b -> 'a) : 'a * 'b list -> 'a =
  let fun itl (e, [])  = e
        | itl (e, a::l) = itl (f(e, a), l)
  in  itl end;

(*  (op @) ([x1, ..., xn], e)  ===>   x1 @ (x2 ... @ (xn @ e))
    for operators that associate to the right (not tail recursive)*)
fun foldr f (l, e) =
  let fun itr [] = e
        | itr (a::l) = f(a, itr l)
  in  itr l  end;

(*  (op @) [x1, ..., xn]  ===>   x1 @ (x2 ... @ (x[n-1] @ xn))
    for n > 0, operators that associate to the right (not tail recursive)*)
fun foldr1 f l =
  let fun itr [x] = x                       (* FIXME [] case: elim warn (?) *)
        | itr (x::l) = f(x, itr l)
  in  itr l  end;


(* basic list functions *)

(*length of a list, should unquestionably be a standard function*)
local fun length1 (n, [])  = n   (*TAIL RECURSIVE*)
        | length1 (n, x :: xs) = length1 (n + 1, xs)
in  fun length l = length1 (0, l) end;

(*take the first n elements from a list*)
fun take (n, []) = []
  | take (n, x :: xs) =
      if n > 0 then x :: take (n - 1, xs) else [];

(*drop the first n elements from a list*)
fun drop (n, []) = []
  | drop (n, x :: xs) =
      if n > 0 then drop (n - 1, xs) else x :: xs;

(*return nth element of a list, where 0 designates the first element;
  raise EXCEPTION if list too short*)
fun nth_elem NL =
  (case drop NL of
    [] => raise LIST "nth_elem"
  | x :: _ => x);

(*last element of a list*)
fun last_elem [] = raise LIST "last_elem"
  | last_elem [x] = x
  | last_elem (_ :: xs) = last_elem xs;

(*find the position of an element in a list*)
fun find (x, ys) =
  let fun f (y :: ys, i) = if x = y then i else f (ys, i + 1)
        | f (_, _) = raise LIST "find"
  in f (ys, 0) end;

(*flatten a list of lists to a list*)
fun flat (ls: 'c list list) : 'c list = foldr (op @) (ls, []);


(*like Lisp's MAPC -- seq proc [x1, ..., xn] evaluates
  (proc x1; ...; proc xn) for side effects*)
fun seq (proc: 'a -> unit) : 'a list -> unit =
  let fun seqf [] = ()
        | seqf (x :: xs) = (proc x; seqf xs)
  in seqf end;


(*separate s [x1, x2, ..., xn]  ===>  [x1, s, x2, s, ..., s, xn]*)
fun separate s (x :: (xs as _ :: _)) = x :: s :: separate s xs
  | separate _ xs = xs;

(*make the list [x, x, ..., x] of length n*)
fun replicate n (x: 'a) : 'a list =
  let fun rep (0, xs) = xs
        | rep (n, xs) = rep (n - 1, x :: xs)
  in
    if n < 0 then raise LIST "replicate"
    else rep (n, [])
  end;


(* filter *)

(*copy the list preserving elements that satisfy the predicate*)
fun filter (pred: 'a->bool) : 'a list -> 'a list =
  let fun filt [] = []
        | filt (x :: xs) = if pred x then x :: filt xs else filt xs
  in filt end;

fun filter_out f = filter (not o f);


fun mapfilter (f: 'a -> 'b option) ([]: 'a list) = [] : 'b list
  | mapfilter f (x :: xs) =
      (case f x of
        None => mapfilter f xs
      | Some y => y :: mapfilter f xs);


(* lists of pairs *)

(*combine two lists forming a list of pairs:
  [x1, ..., xn] ~~ [y1, ..., yn]  ===>  [(x1, y1), ..., (xn, yn)]*)
infix ~~;
fun [] ~~ [] = []
  | (x :: xs) ~~ (y :: ys) = (x, y) :: (xs ~~ ys)
  | _ ~~ _ = raise LIST "~~";

(*combine two lists*)
fun map2 _ ([], []) = []
  | map2 f (x :: xs, y :: ys) = (f (x, y) :: map2 f (xs, ys))
  | map2 _ _ = raise LIST "map2";

(*inverse of ~~; the old 'split':
  [(x1, y1), ..., (xn, yn)]  ===>  ([x1, ..., xn], [y1, ..., yn])*)
fun split_list (l: ('a * 'b) list) = (map #1 l, map #2 l);



(* prefixes, suffixes *)

infix prefix;
fun [] prefix _ = true
  | (x :: xs) prefix (y :: ys) = x = y andalso (xs prefix ys)
  | _ prefix _ = false;

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., x(i-1)], [xi, ..., xn])
   where xi is the first element that does not satisfy the predicate*)
fun take_prefix (pred : 'a -> bool)  (xs: 'a list) : 'a list * 'a list =
  let fun take (rxs, []) = (rev rxs, [])
        | take (rxs, x::xs) =
            if  pred x  then  take(x::rxs, xs)  else  (rev rxs, x::xs)
  in  take([], xs)  end;

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., xi], [x(i+1), ..., xn])
   where xi is the last element that does not satisfy the predicate*)
fun take_suffix _ [] = ([], [])
  | take_suffix pred (x :: xs) =
      (case take_suffix pred xs of
        ([], sffx) => if pred x then ([], x :: sffx) else ([x], sffx)
      | (prfx, sffx) => (x :: prfx, sffx));



(** integers **)

fun inc i = i := ! i + 1;
fun dec i = i := ! i - 1;


(* lists of integers *)

(*make the list [from, from + 1, ..., to]*)
infix upto;
fun from upto to =
  if from > to then [] else from :: ((from + 1) upto to);

(*make the list [from, from - 1, ..., to]*)
infix downto;
fun from downto to =
  if from < to then [] else from :: ((from - 1) downto to);

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;


(* operations on integer lists *)

fun sum [] = 0
  | sum (n :: ns) = n + sum ns;

fun max [m:int] = m
  | max (m :: n :: ns) = if m > n then max (m :: ns) else max (n :: ns)
  | max [] = raise LIST "max";

fun min [m:int] = m
  | min (m :: n :: ns) = if m < n then min (m :: ns) else min (n :: ns)
  | min [] = raise LIST "min";


(* convert integers to strings *)

(*expand the number in the given base;
  example: radixpand (2, 8) gives [1, 0, 0, 0]*)
fun radixpand (base, num) : int list =
  let
    fun radix (n, tail) =
      if n < base then n :: tail
      else radix (n div base, (n mod base) :: tail)
  in radix (num, []) end;

(*expands a number into a string of characters starting from "zerochar";
  example: radixstring (2, "0", 8) gives "1000"*)
fun radixstring (base, zerochar, num) =
  let val offset = ord zerochar;
      fun chrof n = chr (offset + n)
  in implode (map chrof (radixpand (base, num))) end;


fun string_of_int n =
  if n < 0 then "~" ^ radixstring (10, "0", ~n) else radixstring (10, "0", n);



(** strings **)

fun is_letter ch =
  ord "A" <= ord ch andalso ord ch <= ord "Z" orelse
  ord "a" <= ord ch andalso ord ch <= ord "z";

fun is_digit ch =
  ord "0" <= ord ch andalso ord ch <= ord "9";

(*letter or _ or prime (')*)
fun is_quasi_letter "_" = true
  | is_quasi_letter "'" = true
  | is_quasi_letter ch = is_letter ch;

(*white space: blanks, tabs, newlines*)
val is_blank : string -> bool =
  fn " " => true | "\t" => true | "\n" => true | _ => false;

val is_letdig = is_quasi_letter orf is_digit;


(*lower all chars of string*)
val to_lower =
  let
    fun lower ch =
      if ch >= "A" andalso ch <= "Z" then
        chr (ord ch - ord "A" + ord "a")
      else ch;
  in implode o (map lower) o explode end;


(*simple quoting (does not escape special chars)*)
fun quote s = "\"" ^ s ^ "\"";

(*space_implode "..." (explode "hello"); gives "h...e...l...l...o"*)
fun space_implode a bs = implode (separate a bs);

(*concatenate messages, one per line, into a string*)
val cat_lines = implode o (map (apr (op ^, "\n")));



(** lists as sets **)

(*membership in a list*)
infix mem;
fun x mem [] = false
  | x mem (y :: ys) = x = y orelse x mem ys;

(*generalized membership test*)
fun gen_mem eq (x, []) = false
  | gen_mem eq (x, y :: ys) = eq (x, y) orelse gen_mem eq (x, ys);


(*insertion into list if not already there*)
infix ins;
fun x ins xs = if x mem xs then xs else x :: xs;

(*generalized insertion*)
fun gen_ins eq (x, xs) = if gen_mem eq (x, xs) then xs else x :: xs;


(*union of sets represented as lists: no repetitions*)
infix union;
fun xs union [] = xs
  | [] union ys = ys
  | (x :: xs) union ys = xs union (x ins ys);

(*generalized union*)
fun gen_union eq (xs, []) = xs
  | gen_union eq ([], ys) = ys
  | gen_union eq (x :: xs, ys) = gen_union eq (xs, gen_ins eq (x, ys));


(*intersection*)
infix inter;
fun [] inter ys = []
  | (x :: xs) inter ys =
      if x mem ys then x :: (xs inter ys) else xs inter ys;


(*subset*)
infix subset;
fun [] subset ys = true
  | (x :: xs) subset ys = x mem ys andalso xs subset ys;

fun gen_subset eq (xs, ys) = forall (fn x => gen_mem eq (x, ys)) xs;


(*removing an element from a list WITHOUT duplicates*)
infix \;
fun (y :: ys) \ x = if x = y then ys else y :: (ys \ x)
  | [] \ x = [];

infix \\;
val op \\ = foldl (op \);

(*removing an element from a list -- possibly WITH duplicates*)
fun gen_rem eq (xs, y) = filter_out (fn x => eq (x, y)) xs;

val gen_rems = foldl o gen_rem;


(*makes a list of the distinct members of the input; preserves order, takes
  first of equal elements*)
fun gen_distinct eq lst =
  let
    val memb = gen_mem eq;

    fun dist (rev_seen, []) = rev rev_seen
      | dist (rev_seen, x :: xs) =
          if memb (x, rev_seen) then dist (rev_seen, xs)
          else dist (x :: rev_seen, xs);
  in
    dist ([], lst)
  end;

val distinct = gen_distinct (op =);


(*returns the tail beginning with the first repeated element, or []*)
fun findrep [] = []
  | findrep (x :: xs) = if x mem xs then x :: xs else findrep xs;



(** association lists **)

(*association list lookup*)
fun assoc ([], key) = None
  | assoc ((keyi, xi) :: pairs, key) =
      if key = keyi then Some xi else assoc (pairs, key);

fun assocs ps x =
  (case assoc (ps, x) of
    None => []
  | Some ys => ys);

(*generalized association list lookup*)
fun gen_assoc eq ([], key) = None
  | gen_assoc eq ((keyi, xi) :: pairs, key) =
      if eq (key, keyi) then Some xi else gen_assoc eq (pairs, key);

(*association list update*)
fun overwrite (al, p as (key, _)) =
  let fun over ((q as (keyi, _)) :: pairs) =
            if keyi = key then p :: pairs else q :: (over pairs)
        | over [] = [p]
  in over al end;



(** generic tables **)

(*Tables are supposed to be 'efficient' encodings of lists of elements distinct
  wrt. an equality "eq". The extend and merge operations below are optimized
  for long-term space efficiency.*)

(*append (new) elements to a table*)
fun generic_extend _ _ _ tab [] = tab
  | generic_extend eq dest_tab mk_tab tab1 lst2 =
      let
        val lst1 = dest_tab tab1;
        val new_lst2 = gen_rems eq (lst2, lst1);
      in
        if null new_lst2 then tab1
        else mk_tab (lst1 @ new_lst2)
      end;

(*append (new) elements of 2nd table to 1st table*)
fun generic_merge eq dest_tab mk_tab tab1 tab2 =
  let
    val lst1 = dest_tab tab1;
    val lst2 = dest_tab tab2;
    val new_lst2 = gen_rems eq (lst2, lst1);
  in
    if null new_lst2 then tab1
    else if gen_subset eq (lst1, lst2) then tab2
    else mk_tab (lst1 @ new_lst2)
  end;


(*lists as tables*)
val extend_list = generic_extend (op =) I I;
val merge_lists = generic_merge (op =) I I;



(** balanced trees **)

exception Balance;      (*indicates non-positive argument to balancing fun*)

(*balanced folding; avoids deep nesting*)
fun fold_bal f [x] = x
  | fold_bal f [] = raise Balance
  | fold_bal f xs =
      let val k = length xs div 2
      in  f (fold_bal f (take(k, xs)),
             fold_bal f (drop(k, xs)))
      end;

(*construct something of the form f(...g(...(x)...)) for balanced access*)
fun access_bal (f, g, x) n i =
  let fun acc n i =     (*1<=i<=n*)
          if n=1 then x else
          let val n2 = n div 2
          in  if i<=n2 then f (acc n2 i)
                       else g (acc (n-n2) (i-n2))
          end
  in  if 1<=i andalso i<=n then acc n i else raise Balance  end;

(*construct ALL such accesses; could try harder to share recursive calls!*)
fun accesses_bal (f, g, x) n =
  let fun acc n =
          if n=1 then [x] else
          let val n2 = n div 2
              val acc2 = acc n2
          in  if n-n2=n2 then map f acc2 @ map g acc2
                         else map f acc2 @ map g (acc (n-n2)) end
  in  if 1<=n then acc n else raise Balance  end;



(** input / output **)

fun prs s = output (std_out, s);
fun writeln s = prs (s ^ "\n");


(*print error message and abort to top level*)
exception ERROR;
fun error msg = (writeln msg; raise ERROR);
fun sys_error msg = (writeln "*** System Error ***"; error msg);

fun assert p msg = if p then () else error msg;
fun deny p msg = if p then error msg else ();


(* FIXME close file (?) *)
(*for the "test" target in Makefiles -- signifies successful termination*)
fun maketest msg =
  (writeln msg; output (open_out "test", "Test examples ran successfully\n"));


(*print a list surrounded by the brackets lpar and rpar, with comma separator
  print nothing for empty list*)
fun print_list (lpar, rpar, pre: 'a -> unit) (l : 'a list) =
  let fun prec x = (prs ","; pre x)
  in
    (case l of
      [] => ()
    | x::l => (prs lpar; pre x; seq prec l; prs rpar))
  end;

(*print a list of items separated by newlines*)
fun print_list_ln (pre: 'a -> unit) : 'a list -> unit =
  seq (fn x => (pre x; writeln ""));


val print_int = prs o string_of_int;



(** timing **)

(*unconditional timing function*)
val timeit = cond_timeit true;

(*timed application function*)
fun timeap f x = timeit (fn () => f x);

(*timed "use" function, printing filenames*)
fun time_use fname = timeit (fn () =>
  (writeln ("\n**** Starting " ^ fname ^ " ****"); use fname;
   writeln ("\n**** Finished " ^ fname ^ " ****")));



(** filenames **)

(*convert UNIX filename of the form "path/file" to "path/" and "file";
  if filename contains no slash, then it returns "" and "file"*)
val split_filename =
  (pairself implode) o take_suffix (not_equal "/") o explode;

val base_name = #2 o split_filename;

(*merge splitted filename (path and file);
  if path does not end with one a slash is appended*)
fun tack_on "" name = name
  | tack_on path name =
      if last_elem (explode path) = "/" then path ^ name
      else path ^ "/" ^ name;

(*remove the extension of a filename, i.e. the part after the last '.'*)
val remove_ext = implode o #1 o take_suffix (not_equal ".") o explode;



(** misc functions **)

(*use the keyfun to make a list of (x, key) pairs*)
fun make_keylist (keyfun: 'a->'b) : 'a list -> ('a * 'b) list =
  let fun keypair x = (x, keyfun x)
  in map keypair end;

(*given a list of (x, key) pairs and a searchkey
  return the list of xs from each pair whose key equals searchkey*)
fun keyfilter [] searchkey = []
  | keyfilter ((x, key) :: pairs) searchkey =
      if key = searchkey then x :: keyfilter pairs searchkey
      else keyfilter pairs searchkey;


(*Partition list into elements that satisfy predicate and those that don't.
  Preserves order of elements in both lists.*)
fun partition (pred: 'a->bool) (ys: 'a list) : ('a list * 'a list) =
    let fun part ([], answer) = answer
          | part (x::xs, (ys, ns)) = if pred(x)
            then  part (xs, (x::ys, ns))
            else  part (xs, (ys, x::ns))
    in  part (rev ys, ([], []))  end;


fun partition_eq (eq:'a * 'a -> bool) =
    let fun part [] = []
          | part (x::ys) = let val (xs, xs') = partition (apl(x, eq)) ys
                           in (x::xs)::(part xs') end
    in part end;


(*Partition a list into buckets  [ bi, b(i+1), ..., bj ]
   putting x in bk if p(k)(x) holds.  Preserve order of elements if possible.*)
fun partition_list p i j =
  let fun part k xs =
            if k>j then
              (case xs of [] => []
                         | _ => raise LIST "partition_list")
            else
            let val (ns, rest) = partition (p k) xs;
            in  ns :: part(k+1)rest  end
  in  part i end;


(* sorting *)

(*insertion sort; stable (does not reorder equal elements)
  'less' is less-than test on type 'a*)
fun sort (less: 'a*'a -> bool) =
  let fun insert (x, []) = [x]
        | insert (x, y::ys) =
              if less(y, x) then y :: insert (x, ys) else x::y::ys;
      fun sort1 [] = []
        | sort1 (x::xs) = insert (x, sort1 xs)
  in  sort1  end;

(*sort strings*)
val sort_strings = sort (op <= : string * string -> bool);


(* transitive closure (not Warshall's algorithm) *)

fun transitive_closure [] = []
  | transitive_closure ((x, ys)::ps) =
      let val qs = transitive_closure ps
          val zs = foldl (fn (zs, y) => assocs qs y union zs) (ys, ys)
          fun step(u, us) = (u, if x mem us then zs union us else us)
      in (x, zs) :: map step qs end;


(* generating identifiers *)

local
  val a = ord "a" and z = ord "z" and A = ord "A" and Z = ord "Z"
  and k0 = ord "0" and k9 = ord "9"
in

(*Increment a list of letters like a reversed base 26 number.
  If head is "z", bumps chars in tail.
  Digits are incremented as if they were integers.
  "_" and "'" are not changed.
  For making variants of identifiers.*)

fun bump_int_list(c::cs) = if c="9" then "0" :: bump_int_list cs else
        if k0 <= ord(c) andalso ord(c) < k9 then chr(ord(c)+1) :: cs
        else "1" :: c :: cs
  | bump_int_list([]) = error("bump_int_list: not an identifier");

fun bump_list([], d) = [d]
  | bump_list(["'"], d) = [d, "'"]
  | bump_list("z"::cs, _) = "a" :: bump_list(cs, "a")
  | bump_list("Z"::cs, _) = "A" :: bump_list(cs, "A")
  | bump_list("9"::cs, _) = "0" :: bump_int_list cs
  | bump_list(c::cs, _) = let val k = ord(c)
        in if (a <= k andalso k < z) orelse (A <= k andalso k < Z) orelse
              (k0 <= k andalso k < k9) then chr(k+1) :: cs else
           if c="'" orelse c="_" then c :: bump_list(cs, "") else
                error("bump_list: not legal in identifier: " ^
                        implode(rev(c::cs)))
        end;

end;

fun bump_string s : string = implode (rev (bump_list(rev(explode s), "")));


(* lexical scanning *)

(*scan a list of characters into "words" composed of "letters" (recognized by
  is_let) and separated by any number of non-"letters"*)
fun scanwords is_let cs =
  let fun scan1 [] = []
        | scan1 cs =
            let val (lets, rest) = take_prefix is_let cs
            in implode lets :: scanwords is_let rest end;
  in scan1 (#2 (take_prefix (not o is_let) cs)) end;

