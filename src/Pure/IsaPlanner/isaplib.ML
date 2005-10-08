(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      Pure/IsaPlanner/isaplib.ML
    ID:		$Id$
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A few useful system-independent utilities.
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature ISAP_LIB =
sig
  (* seq operations *)
  val ALL_BUT_LAST : ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val FST : ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val NTH : int -> ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val all_but_last_of_seq : 'a Seq.seq -> 'a Seq.seq
  val nat_seq : int Seq.seq
  val nth_of_seq : int -> 'a Seq.seq -> 'a option
  val pair_seq : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq
  val seq_is_empty : 'a Seq.seq -> bool
  val number_seq : 'a Seq.seq -> (int * 'a) Seq.seq

  datatype 'a skipseqT = 
           skipmore of int
         | skipseq of 'a Seq.seq Seq.seq;
  val skipto_seqseq : int -> 'a Seq.seq Seq.seq -> 'a skipseqT
  val seqflat_seq : 'a Seq.seq Seq.seq -> 'a Seq.seq 

  (* lists *)
  val mk_num_list : int -> int list
  val number_list : int -> 'a list -> (int * 'a) list
  val repeated_list : int -> 'a -> 'a list
  val all_pairs : 'a list -> 'b list -> ('a * 'b) list
	val get_ends_of : ('a * 'a -> bool) ->
										('a * 'a) -> 'a list -> ('a * 'a)
  val flatmap : ('a -> 'b list) -> 'a list -> 'b list

	val lrem : ('a * 'b -> bool) -> 'a list -> 'b list -> 'b list
  val forall_list : ('a -> bool) -> 'a list -> bool

  (* the list of lists with one of each of the original sublists *)
  val one_of_each : 'a list list -> 'a list list

  (* type changing *)
  exception NOT_A_DIGIT of string
  val int_of_string : string -> int

  (* string manipulations *)
  val remove_end_spaces : string -> string
  val str_indent : string -> string
  val string_of_intlist : int list -> string
  val string_of_list : ('a -> string) -> 'a list -> string

  (* options *)
  val aptosome : 'a option -> ('a -> 'b) -> 'b option
  val seq_mapfilter : ('a -> 'b option) -> 'a Seq.seq -> 'b Seq.seq
  val seq_map_to_some_filter : ('a -> 'b) -> 'a option Seq.seq 
                               -> 'b Seq.seq
end;



structure IsaPLib : ISAP_LIB = 
struct
 
(* Seq *)
fun seq_map_to_some_filter f s0 =
    let 
      fun recf s () = 
          case (Seq.pull s) of 
            NONE => NONE
          | SOME (NONE,s') => recf s' ()
          | SOME (SOME d, s') => 
            SOME (f d, Seq.make (recf s'))
    in Seq.make (recf s0) end;

fun seq_mapfilter f s0 =
    let 
      fun recf s () = 
          case (Seq.pull s) of 
            NONE => NONE
          | SOME (a,s') => 
            (case f a of NONE => recf s' ()
                       | SOME b => SOME (b, Seq.make (recf s')))
    in Seq.make (recf s0) end;



(* a simple function to pair with each element of a list, a number *)
fun number_list i [] = []
	| number_list i (h::t) = 
		(i,h)::(number_list (i+1) t)

(* check to see if a sequence is empty *)
fun seq_is_empty s = is_none (Seq.pull s);

(* the sequence of natural numbers *)
val nat_seq = 
      let fun nseq i () = SOME (i, Seq.make (nseq (i+1)))
      in Seq.make (nseq 1)
      end;

(* create a sequence of pairs of the elements of the two sequences
   If one sequence becomes empty, then so does the pairing of them. 
   
   This is particularly useful if you wish to perform counting or
   other repeated operations on a sequence and you want to combvine
   this infinite sequence with a possibly finite one.

   behaviour: 
   s1: a1, a2, ... an
   s2: b1, b2, ... bn ...

   pair_seq s1 s2: (a1,b1), (a2,b2), ... (an,bn)
*)
fun pair_seq seq1 seq2 = 
    let
      fun pseq s1 s2 () = 
	        case Seq.pull s1 of 
	          NONE => NONE
	        | SOME (s1h, s1t) => 
	          case Seq.pull s2 of 
		          NONE => NONE
	          | SOME (s2h, s2t) =>
		          SOME ((s1h, s2h), Seq.make (pseq s1t s2t))
    in
      Seq.make (pseq seq1 seq2)
    end;

(* number a sequence *)
fun number_seq s = pair_seq nat_seq s;

(* cuts off the last element of a sequence *)
fun all_but_last_of_seq s = 
    let 
      fun f () = 
	  case Seq.pull s of
	    NONE => NONE
	  | SOME (a, s2) => 
	    (case Seq.pull s2 of 
	       NONE => NONE
	     | SOME (a2,s3) => 
	       SOME (a, all_but_last_of_seq (Seq.cons (a2,s3))))
    in
      Seq.make f
    end;

 fun ALL_BUT_LAST r st = all_but_last_of_seq (r st);


  (* nth elem for sequenes, return none if out of bounds *)
  fun nth_of_seq i l = 
           if (seq_is_empty l) then NONE 
           else if i <= 1 then SOME (Seq.hd l)
           else nth_of_seq (i-1) (Seq.tl l);

  (* for use with tactics... gives no_tac if element isn't there *)
  fun NTH n f st = 
      let val r = nth_of_seq n (f st) in 
        if (is_none r) then Seq.empty else (Seq.single (valOf r))
      end;
 
  (* First result of a tactic... uses NTH, so if there is no elements,

     then no_tac is returned. *)
  fun FST f = NTH 1 f;

datatype 'a skipseqT = skipmore of int
  | skipseq of 'a Seq.seq Seq.seq;
(* given a seqseq, skip the first m non-empty seq's *)
fun skipto_seqseq m s = 
    let 
      fun skip_occs n sq = 
          case Seq.pull sq of 
            NONE => skipmore n
          | SOME (h,t) => 
            (case Seq.pull h of NONE => skip_occs n t
             | SOME _ => if n <= 1 then skipseq (Seq.cons (h, t))
                         else skip_occs (n - 1) t)
    in (skip_occs m s) end;

(* handy function for re-arranging Sequence operations *)
(* [[a,b,c],[d,e],...] => flatten [[a,d,...], [b,e,...], [c, ...]] *)
fun seqflat_seq ss = 
    let 
      fun pulltl LL () = 
          (case Seq.pull LL of 
             NONE => NONE
           | SOME (hL,tLL) => 
             (case Seq.pull hL of 
                NONE => pulltl tLL ()
              | SOME (h,tL) => 
                SOME (h, Seq.make (recf (tLL, (Seq.single tL))))))
      and recf (fstLL,sndLL) () = 
          (case Seq.pull fstLL of 
             NONE => pulltl sndLL ()
           | SOME (hL, tLL) => 
             (case Seq.pull hL of 
                NONE => recf (tLL, sndLL) ()
              | SOME (h,tL) => 
                SOME (h, Seq.make (recf (tLL, Seq.append (sndLL, Seq.single tL))))))
    in Seq.make (pulltl ss) end;
(* tested with: 
val ss = Seq.of_list [Seq.of_list [1,2,3], Seq.of_list [4,5], Seq.of_list [7,8,9,10]];
Seq.list_of (seqflat_seq ss);
val it = [1, 4, 7, 2, 5, 8, 3, 9, 10] : int list
*)



  (* create a list opf the form (n, n-1, n-2, ... ) *)
  fun mk_num_list n =  
      if n < 1 then [] else (n :: (mk_num_list (n-1))); 

  fun repeated_list n a =  
      if n < 1 then [] else (a :: (repeated_list (n-1) a)); 

  (* create all possible pairs with fst element from the first list
     and snd element from teh second list *)
  fun all_pairs xs ys = 
      let 
        fun all_pairs_aux yss [] _ acc = acc
          | all_pairs_aux yss (x::xs) [] acc = 
            all_pairs_aux yss xs yss acc
          | all_pairs_aux yss (xs as (x1::x1s)) (y::ys) acc = 
                               all_pairs_aux yss xs ys ((x1,y)::acc)
      in
        all_pairs_aux ys xs ys []
      end;


  (* create all possible pairs with fst element from the first list
     and snd element from teh second list *)
  (* FIXME: make tail recursive and quick *)
  fun one_of_each [] = []
    | one_of_each [[]] = []
    | one_of_each [(h::t)] = [h] :: (one_of_each [t])
    | one_of_each ([] :: xs) = []
    | one_of_each ((h :: t) :: xs) = 
      (map (fn z => h :: z) (one_of_each xs)) 
      @ (one_of_each (t :: xs));


(* function to get the upper/lower bounds of a list 
given: 
gr : 'a * 'a -> bool  = greater than check
e as (u,l) : ('a * 'a) = upper and lower bits
l : 'a list = the list to get the upper and lower bounds of
returns a pair ('a * 'a) of the biggest and lowest value w.r.t "gr"
*)
fun get_ends_of gr (e as (u,l)) [] = e
  | get_ends_of gr (e as (u,l)) (h :: t) = 
    if gr(h,u) then get_ends_of gr (h,l) t
    else if gr(l,h) then get_ends_of gr (u,h) t
    else get_ends_of gr (u,l) t;

fun flatmap f = List.concat o map f;

  (* quick removal of "rs" elements from "ls" when (eqf (r,l)) is true 
		 Ignores ordering. *)
  fun lrem eqf rs ls = 
			let fun list_remove rs ([],[]) = []
						| list_remove [] (xs,_) = xs
						| list_remove (r::rs) ([],leftovers) = 
							list_remove rs (leftovers,[])
						| list_remove (r1::rs) ((x::xs),leftovers) = 
							if eqf (r1, x) then list_remove (r1::rs) (xs,leftovers)
							else list_remove (r1::rs) (xs, x::leftovers)
			in
				list_remove rs (ls,[])
			end;

fun forall_list f [] = true
  | forall_list f (a::t) = f a orelse forall_list f t;


  (* crappy string indeter *)
  fun str_indent s = 
    implode (map (fn s => if s = "\n" then "\n  " else s) (explode s));
      

  fun remove_end_spaces s = 
      let 
				fun rem_starts [] = [] 
					| rem_starts (" " :: t) = rem_starts t
					| rem_starts ("\t" :: t) = rem_starts t
					| rem_starts ("\n" :: t) = rem_starts t
					| rem_starts l = l
				fun rem_ends l = rev (rem_starts (rev l))
      in
				implode (rem_ends (rem_starts (explode s)))
      end;

(* convert a string to an integer *)
  exception NOT_A_DIGIT of string;

  fun int_of_string s = 
      let 
				fun digits_to_int [] x = x
					| digits_to_int (h :: t) x = digits_to_int t (x * 10 + h);
	
				fun char_to_digit c = 
						case c of 
							"0" => 0
						| "1" => 1
						| "2" => 2
						| "3" => 3
						| "4" => 4
						| "5" => 5
						| "6" => 6
						| "7" => 7
						| "8" => 8
						| "9" => 9
						| _ => raise NOT_A_DIGIT c
      in
				digits_to_int (map char_to_digit (explode (remove_end_spaces s))) 0
      end;

  (* Debugging/printing code for this datatype *)
  fun string_of_list f l = 
      let 
				fun auxf [] = ""
					| auxf [a] = (f a)
					| auxf (h :: (t as (h2 :: t2))) = (f h) ^ ", " ^ (auxf t)
      in
				"[" ^ (auxf l) ^ "]"
      end;

   val string_of_intlist = string_of_list string_of_int;


  (* options *)
  fun aptosome NONE f = NONE
    | aptosome (SOME x) f = SOME (f x);

end;
