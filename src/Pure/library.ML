(*  Title:      Pure/library.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Basic library: booleans, lists, pairs, input/output, etc.
*)


(**** Booleans: operators for combining predicates ****)

infix orf; 
fun p orf q = fn x => p x orelse q x ;

infix andf; 
fun p andf q = fn x => p x andalso q x ;

fun notf p x = not (p x) ;

fun orl [] = false
  | orl (x::l) =  x  orelse  orl l;

fun andl [] = true
  | andl (x::l) =  x  andalso  andl l;

(*exists pred [x1,...,xn] ======>  pred(x1)  orelse  ...  orelse  pred(xn)*)
fun exists (pred: 'a -> bool) : 'a list -> bool = 
  let fun boolf [] = false
        | boolf (x::l) = (pred x) orelse boolf l
  in boolf end;

(*forall pred [x1,...,xn] ======>  pred(x1)  andalso  ...  andalso  pred(xn)*)
fun forall (pred: 'a -> bool) : 'a list -> bool = 
  let fun boolf [] = true
        | boolf (x::l) = (pred x) andalso (boolf l)
  in boolf end;


(** curried equality **)

fun equal x y = (x = y);

fun not_equal x y = x <> y;



(*** Lists ***)

exception LIST of string;

(*discriminator and selectors for lists. *)
fun null   []   = true
  | null (_::_) = false;

fun hd   []   = raise LIST "hd"
  | hd (a::_) = a;

fun tl   []   = raise LIST "tl"
  | tl (_::l) = l;


(*curried cons and reverse cons*)

fun cons x xs = x :: xs;

fun rcons xs x = x :: xs;


(*curried functions for pairing and reversed pairing*)
fun pair x y = (x,y);
fun rpair x y = (y,x);

fun fst(x,y) = x and snd(x,y) = y;

(*Handy combinators*)
fun curry f x y = f(x,y);
fun uncurry f(x,y) = f x y;
fun I x = x  and  K x y = x;

(*Combine two functions forming the union of their domains*)
infix orelf;
fun f orelf g = fn x => f x  handle Match=> g x;


(*Application of (infix) operator to its left or right argument*)
fun apl (x,f) y = f(x,y);
fun apr (f,y) x = f(x,y);


(*functional for pairs*)
fun pairself f (x,y) = (f x, f y);

(*Apply the function to a component of a pair*)
fun apfst f (x, y) = (f x, y);
fun apsnd f (x, y) = (x, f y);

fun square (n: int) = n*n;

fun fact 0 = 1
  | fact n = n * fact(n-1);


(*The following versions of fold are designed to fit nicely with infixes.*)

(*  (op @) (e, [x1,...,xn])  ======>   ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left.  TAIL RECURSIVE*)
fun foldl (f: 'a * 'b -> 'a) : 'a * 'b list -> 'a =
  let fun itl (e, [])  = e
        | itl (e, a::l) = itl (f(e,a), l)
  in  itl end;

(*  (op @) ([x1,...,xn], e)  ======>   x1 @ (x2 ... @ (xn @ e))
    for operators that associate to the right.  Not tail recursive.*)
fun foldr f (l,e) =
  let fun itr [] = e
        | itr (a::l) = f(a, itr l)
  in  itr l  end;

(*  (op @) [x1,...,xn]  ======>   x1 @ (x2 ..(x[n-1]. @ xn))
    for n>0, operators that associate to the right.  Not tail recursive.*)
fun foldr1 f l =
  let fun itr [x] = x
        | itr (x::l) = f(x, itr l)
  in  itr l  end;


(*Length of a list.  Should unquestionably be a standard function*)
local fun length1 (n, [ ])  = n   (*TAIL RECURSIVE*)
        | length1 (n, x::l) = length1 (n+1, l)   
in  fun length l = length1 (0,l) end;


(*Take the first n elements from l.*)
fun take (n, []) = []
  | take (n, x::xs) = if n>0 then x::take(n-1,xs)  
                      else  [];

(*Drop the first n elements from l.*)
fun drop (_, [])    = []
  | drop (n, x::xs) = if n>0 then drop (n-1, xs) 
                             else x::xs;

(*Return nth element of l, where 0 designates the first element;
  raise EXCEPTION if list too short.*)
fun nth_elem NL = case (drop NL) of
    []   => raise LIST "nth_elem" 
  | x::l => x;


(*Last element of a list*)
fun last_elem [] = raise LIST "last_elem"
  | last_elem [x] = x
  | last_elem (_ :: xs) = last_elem xs;


(*make the list [from, from+1, ..., to]*)
infix upto;
fun from upto to =
    if from>to then []  else  from :: ((from+1) upto to);

(*make the list [from, from-1, ..., to]*)
infix downto;
fun from downto to =
    if from<to then []  else  from :: ((from-1) downto to);

(* predicate: downto0(is,n) <=> is = [n,n-1,...,0] *)
fun downto0(i::is,n) = i=n andalso downto0(is,n-1)
  | downto0([],n)    = n = ~1;

(*Like Lisp's MAPC -- seq proc [x1,...,xn] evaluates 
  proc(x1); ... ; proc(xn) for side effects.*)
fun seq (proc: 'a -> unit) : 'a list -> unit = 
  let fun seqf []     = ()
        | seqf (x::l) = (proc x;  seqf l)
  in  seqf end;


(*** Balanced folding; access to balanced trees ***)

exception Balance;	(*indicates non-positive argument to balancing fun*)

(*Balanced folding; avoids deep nesting*)
fun fold_bal f [x] = x
  | fold_bal f [] = raise Balance
  | fold_bal f xs =
      let val k = length xs div 2
      in  f (fold_bal f (take(k,xs)),
	     fold_bal f (drop(k,xs)))  
      end;

(*Construct something of the form f(...g(...(x)...)) for balanced access*)
fun access_bal (f,g,x) n i =
  let fun acc n i = 	(* 1<=i<=n*)
          if n=1 then x else
	  let val n2 = n div 2
	  in  if i<=n2 then f (acc n2 i) 
	               else g (acc (n-n2) (i-n2))
          end
  in  if 1<=i andalso i<=n then acc n i else raise Balance  end;

(*Construct ALL such accesses; could try harder to share recursive calls!*)
fun accesses_bal (f,g,x) n =
  let fun acc n =  
          if n=1 then [x] else 
	  let val n2 = n div 2
	      val acc2 = acc n2
	  in  if n-n2=n2 then map f acc2 @ map g acc2
	                 else map f acc2 @ map g (acc (n-n2)) end
  in  if 1<=n then acc n else raise Balance  end;


(*** Input/Output ***)

fun prs s = output(std_out,s);
fun writeln s = prs (s ^ "\n");

(*Print error message and abort to top level*)
exception ERROR;
fun error (msg) = (writeln msg;  raise ERROR);

fun assert p msg = if p then () else error msg;
fun deny p msg = if p then error msg else ();

(*For the "test" target in Makefiles -- signifies successful termination*)
fun maketest msg = 
    (writeln msg;
     output(open_out "test", "Test examples ran successfully\n"));

(*print a list surrounded by the brackets lpar and rpar, with comma separator
  print nothing for empty list*)
fun print_list (lpar, rpar, pre: 'a -> unit)  (l : 'a list) = 
    let fun prec(x) = (prs",";  pre(x)) 
    in  case l of
	    [] => () 
	  | x::l =>  (prs lpar;  pre x;  seq prec l;  prs rpar)
    end;

(*print a list of items separated by newlines*)
fun print_list_ln (pre: 'a -> unit)  : 'a list -> unit = 
    seq (fn x => (pre x;  writeln""));

fun is_letter ch =
  (ord"A" <= ord ch)  andalso  (ord ch <= ord"Z")   orelse
  (ord"a" <= ord ch)  andalso  (ord ch <= ord"z");

fun is_digit ch =
  (ord"0" <= ord ch)  andalso  (ord ch <= ord"9");

(*letter or _ or prime (') *)
fun is_quasi_letter "_" = true
  | is_quasi_letter "'" = true
  | is_quasi_letter ch  = is_letter ch;

(*white space: blanks, tabs, newlines*)
val is_blank : string -> bool = fn
     " " => true  |  "\t" => true  |  "\n" => true  |  _ => false;

val is_letdig = is_quasi_letter orf is_digit;

val to_lower =
  let
    fun lower ch =
      if ch >= "A" andalso ch <= "Z" then
        chr (ord ch - ord "A" + ord "a")
      else ch;
  in
    implode o (map lower) o explode
  end;


(*** Timing ***)

(*Unconditional timing function*)
val timeit = cond_timeit true;

(*Timed application function*)
fun timeap f x = timeit(fn()=> f x);

(*Timed "use" function, printing filenames*)
fun time_use fname = timeit(fn()=> 
   (writeln("\n**** Starting " ^ fname ^ " ****");  use fname;  
    writeln("\n**** Finished " ^ fname ^ " ****")));  


(*** Misc functions ***)

(*Function exponentiation: f(...(f x)...) with n applications of f *)
fun funpow n f x =
  let fun rep (0,x) = x
        | rep (n,x) = rep (n-1, f x)
  in  rep (n,x)  end;

(*Combine two lists forming a list of pairs:
  [x1,...,xn] ~~ [y1,...,yn]  ======>   [(x1,y1), ..., (xn,yn)] *)
infix ~~;
fun []   ~~  []   = []
  | (x::xs) ~~ (y::ys) = (x,y) :: (xs ~~ ys)
  |  _   ~~   _   = raise LIST "~~";

(*Inverse of ~~;  the old 'split'.
   [(x1,y1), ..., (xn,yn)]  ======>  ( [x1,...,xn] , [y1,...,yn] ) *)
fun split_list (l: ('a*'b)list) = (map #1 l, map #2 l);

(*make the list [x; x; ...; x] of length n*)
fun replicate n (x: 'a) : 'a list =
  let fun rep (0,xs) = xs
        | rep (n,xs) = rep(n-1, x::xs) 
  in   if n<0 then raise LIST "replicate"
       else rep (n,[])
  end;

(*Flatten a list of lists to a list.*)
fun flat (ls: 'c list list) : 'c list = foldr (op @) (ls,[]);


(*** polymorphic set operations ***)

(*membership in a list*)
infix mem;
fun x mem []  =  false
  | x mem (y::l)  =  (x=y) orelse (x mem l);

(*insertion into list if not already there*)
infix ins;
fun x ins xs = if x mem xs then  xs   else  x::xs;

(*union of sets represented as lists: no repetitions*)
infix union;
fun   xs    union [] = xs
  |   []    union ys = ys
  | (x::xs) union ys = xs union (x ins ys);

infix inter;
fun   []    inter ys = []
  | (x::xs) inter ys = if x mem ys then x::(xs inter ys)
                                   else     xs inter ys;

infix subset;
fun   []    subset ys = true
  | (x::xs) subset ys = x mem ys   andalso  xs subset ys;

(*removing an element from a list WITHOUT duplicates*)
infix \;
fun (y::ys) \ x = if x=y then ys else y::(ys \ x)
  |   []    \ x = [];

infix \\;
val op \\ = foldl (op \);

(*** option stuff ***)

datatype 'a option = None | Some of 'a;

exception OPTION of string;

fun the (Some x) = x
  | the None = raise OPTION "the";

fun is_some (Some _) = true
  | is_some None = false;

fun is_none (Some _) = false
  | is_none None = true;


(*** Association lists ***)

(*Association list lookup*)
fun assoc ([], key) = None
  | assoc ((keyi,xi)::pairs, key) =
      if key=keyi then Some xi  else assoc (pairs,key);

fun assocs ps x = case assoc(ps,x) of None => [] | Some(ys) => ys;

(*Association list update*)
fun overwrite(al,p as (key,_)) =
  let fun over((q as (keyi,_))::pairs) =
	    if keyi=key then p::pairs else q::(over pairs)
	| over[] = [p]
  in over al end;

(*Copy the list preserving elements that satisfy the predicate*)
fun filter (pred: 'a->bool) : 'a list -> 'a list = 
  let fun filt [] = []
        | filt (x::xs) =  if pred(x) then x :: filt xs  else  filt xs
  in  filt   end;

fun filter_out f = filter (not o f);


(*** List operations, generalized to an arbitrary equality function "eq"
     -- so what good are equality types?? ***)

(*removing an element from a list -- possibly WITH duplicates*)
fun gen_rem eq (xs,y) = filter_out (fn x => eq(x,y)) xs;

(*generalized membership test*)
fun gen_mem eq (x, [])     =  false
  | gen_mem eq (x, y::ys)  =  eq(x,y) orelse gen_mem eq (x,ys);

(*generalized insertion*)
fun gen_ins eq (x,xs) = if gen_mem eq (x,xs) then  xs   else  x::xs;

(*generalized union*)
fun gen_union eq (xs,[]) = xs
  | gen_union eq ([],ys) = ys
  | gen_union eq (x::xs,ys) = gen_union eq (xs, gen_ins eq (x,ys));

(*Generalized association list lookup*)
fun gen_assoc eq ([], key) = None
  | gen_assoc eq ((keyi,xi)::pairs, key) =
      if eq(key,keyi) then Some xi  else gen_assoc eq (pairs,key);

(** Finding list elements and duplicates **)

(* find the position of an element in a list *)
fun find(x,ys) =
    let fun f(y::ys,i) = if x=y then i else f(ys,i+1)
          | f(_,_) = raise LIST "find"
    in f(ys,0) end;

(*Returns the tail beginning with the first repeated element, or []. *)
fun findrep [] = []
  | findrep (x::xs) = if  x mem xs  then  x::xs   else   findrep xs;

fun distinct1 (seen, []) = rev seen
  | distinct1 (seen, x::xs) =
      if x mem seen then distinct1 (seen, xs)
    		    else distinct1 (x::seen, xs);

(*Makes a list of the distinct members of the input*)
fun distinct xs = distinct1([],xs);


(*Use the keyfun to make a list of (x,key) pairs.*)
fun make_keylist (keyfun: 'a->'b) : 'a list -> ('a * 'b) list =
  let fun keypair x = (x, keyfun x) 
  in   map keypair  end;

(*Given a list of (x,key) pairs and a searchkey
  return the list of xs from each pair whose key equals searchkey*)
fun keyfilter [] searchkey = []
  | keyfilter ((x,key)::pairs) searchkey = 
	if key=searchkey then x :: keyfilter pairs searchkey
	else keyfilter pairs searchkey;

fun mapfilter (f: 'a -> 'b option) ([]: 'a list) = [] : 'b list
  | mapfilter f (x::xs) =
      case (f x) of
	  None => mapfilter f xs
	| Some y => y :: mapfilter f xs;


(*Partition list into elements that satisfy predicate and those that don't.
  Preserves order of elements in both lists. *)
fun partition (pred: 'a->bool) (ys: 'a list) : ('a list * 'a list) =
    let fun part ([], answer) = answer
	  | part (x::xs, (ys, ns)) = if pred(x)
	    then  part (xs, (x::ys, ns))
	    else  part (xs, (ys, x::ns))
    in  part (rev ys, ([],[]))  end;


fun partition_eq (eq:'a * 'a -> bool) =
    let fun part [] = []
	  | part (x::ys) = let val (xs,xs') = partition (apl(x,eq)) ys
			   in (x::xs)::(part xs') end
    in part end;


(*Partition a list into buckets  [ bi, b(i+1),...,bj ]
   putting x in bk if p(k)(x) holds.  Preserve order of elements if possible.*)
fun partition_list p i j =
  let fun part k xs = 
            if k>j then 
              (case xs of [] => []
                         | _ => raise LIST "partition_list")
            else
	    let val (ns,rest) = partition (p k) xs;
	    in  ns :: part(k+1)rest  end
  in  part i end;


(*Insertion sort.  Stable (does not reorder equal elements)
  'less' is less-than test on type 'a. *)
fun sort (less: 'a*'a -> bool) = 
  let fun insert (x, []) = [x]
        | insert (x, y::ys) = 
              if less(y,x) then y :: insert (x,ys) else x::y::ys;
      fun sort1 [] = []
        | sort1 (x::xs) = insert (x, sort1 xs)
  in  sort1  end;

(*sort strings*)
val sort_strings = sort (op <= : string * string -> bool);


(*Transitive Closure. Not Warshall's algorithm*)
fun transitive_closure [] = []
  | transitive_closure ((x,ys)::ps) =
      let val qs = transitive_closure ps
          val zs = foldl (fn (zs,y) => assocs qs y union zs) (ys,ys)
          fun step(u,us) = (u, if x mem us then zs union us else us)
      in (x,zs) :: map step qs end;

(*** Converting integers to strings, generating identifiers, etc. ***)

(*Expand the number in the given base 
 example: radixpand(2, 8)  gives   [1, 0, 0, 0] *)
fun radixpand (base,num) : int list =
  let fun radix (n,tail) =
  	if n<base then n :: tail
	else radix (n div base, (n mod base) :: tail)
  in  radix (num,[])  end;

(*Expands a number into a string of characters starting from "zerochar"
 example: radixstring(2,"0", 8)  gives  "1000" *)
fun radixstring (base,zerochar,num) =
  let val offset = ord(zerochar); 
      fun chrof n = chr(offset+n)
  in  implode (map chrof (radixpand (base,num)))  end;

fun string_of_int n = 
  if n < 0 then "~" ^ radixstring(10,"0",~n)  else radixstring(10,"0",n);

val print_int = prs o string_of_int;

local
val a = ord("a") and z = ord("z") and A = ord("A") and Z = ord("Z")
and k0 = ord("0") and k9 = ord("9")
in

(*Increment a list of letters like a reversed base 26 number.
  If head is "z",  bumps chars in tail.
  Digits are incremented as if they were integers.
  "_" and "'" are not changed.
  For making variants of identifiers. *)

fun bump_int_list(c::cs) = if c="9" then "0" :: bump_int_list cs else
	if k0 <= ord(c) andalso ord(c) < k9 then chr(ord(c)+1) :: cs
	else "1" :: c :: cs
  | bump_int_list([]) = error("bump_int_list: not an identifier");

fun bump_list([],d) = [d]
  | bump_list(["'"],d) = [d,"'"]
  | bump_list("z"::cs,_) = "a" :: bump_list(cs,"a")
  | bump_list("Z"::cs,_) = "A" :: bump_list(cs,"A")
  | bump_list("9"::cs,_) = "0" :: bump_int_list cs
  | bump_list(c::cs,_) = let val k = ord(c)
	in if (a <= k andalso k < z) orelse (A <= k andalso k < Z) orelse
	      (k0 <= k andalso k < k9) then chr(k+1) :: cs else
	   if c="'" orelse c="_" then c :: bump_list(cs,"") else
		error("bump_list: not legal in identifier: " ^
			implode(rev(c::cs)))
	end;

end;

fun bump_string s : string = implode (rev (bump_list(rev(explode s),"")));


(*** Operations on integer lists ***)

fun sum [] = 0
  | sum (n::ns) = n + sum ns;

fun max[m : int]  = m
  | max(m::n::ns) = if m>n  then  max(m::ns)  else  max(n::ns)
  | max []        = raise LIST "max";

fun min[m : int]  = m
  | min(m::n::ns) = if m<n  then  min(m::ns)  else  min(n::ns)
  | min []        = raise LIST "min";


(*** Lexical scanning ***)

(* [x1,...,xi,...,xn]  --->  ([x1,...,x(i-1)], [xi,..., xn])
   where xi is the first element that does not satisfy the predicate*)
fun take_prefix (pred : 'a -> bool)  (xs: 'a list) : 'a list * 'a list =
  let fun take (rxs, []) = (rev rxs, [])
	| take (rxs, x::xs) =
	    if  pred x  then  take(x::rxs, xs)  else  (rev rxs, x::xs)
  in  take([],xs)  end;

(* [x1,...,xi,...,xn]  --->  ([x1,...,xi], [x(i+1),..., xn])
   where xi is the last element that does not satisfy the predicate*)
fun take_suffix _ [] = ([], [])
  | take_suffix pred (x :: xs) =
      (case take_suffix pred xs of
        ([], sffx) => if pred x then ([], x :: sffx) else ([x], sffx)
      | (prfx, sffx) => (x :: prfx, sffx));


infix prefix;
fun [] prefix _ = true
  | (x::xs) prefix (y::ys) = (x=y) andalso (xs prefix ys)
  | _ prefix _ = false;

(* [x1, x2, ..., xn] ---> [x1, s, x2, s, ..., s, xn] *)
fun separate s (x :: (xs as _ :: _)) = x :: s :: separate s xs
  | separate _ xs = xs;

(*space_implode "..." (explode "hello");  gives  "h...e...l...l...o" *)
fun space_implode a bs = implode (separate a bs); 

(*simple quoting (does not escape special chars) *)
fun quote s = "\"" ^ s ^ "\"";

(*Concatenate messages, one per line, into a string*)
val cat_lines = implode o (map (apr(op^,"\n")));

(*Scan a list of characters into "words" composed of "letters" (recognized
  by is_let) and separated by any number of non-"letters".*)
fun scanwords is_let cs = 
  let fun scan1 [] = []
	| scan1 cs =
	    let val (lets, rest) = take_prefix is_let cs
	    in  implode lets :: scanwords is_let rest  end;
  in  scan1 (#2 (take_prefix (not o is_let) cs))  end;


(*** Operations on filenames ***)

(*Convert Unix filename of the form path/file to "path/" and "file" ;
  if filename contains no slash, then it returns "" and "file" *)
fun split_filename name =
  let val (file,path) = take_prefix (apr(op<>,"/")) (rev (explode name))
  in  (implode(rev path), implode(rev file)) end;

(*Merge splitted filename (path and file);
  if path does not end with one a slash is appended *)
fun tack_on "" name = name
  | tack_on path name =
      if last_elem (explode path) = "/" then path ^ name
      else path ^ "/" ^ name;

(*Remove the extension of a filename, i.e. the part after the last '.' *)
fun remove_ext name =
  let val (file,_) = take_prefix (apr(op<>,".")) (rev (explode name))
  in implode (rev file) end;

