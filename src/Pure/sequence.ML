(*  Title: 	sequence
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1988  University of Cambridge
*)

(*Unbounded sequences implemented by closures.

  Could use   'a seq = Seq of ('a * (unit -> 'a seq)) option.
  Recomputes if sequence is re-inspected; memoing would need polymorphic refs.
*)


signature SEQUENCE = 
  sig
  type 'a seq
  val append	: 'a seq * 'a seq -> 'a seq
  val chop	: int * 'a seq -> 'a list * 'a seq
  val cons	: 'a * 'a seq -> 'a seq
  val filters	: ('a -> bool) -> 'a seq -> 'a seq
  val flats	: 'a seq seq -> 'a seq
  val hd	: 'a seq -> 'a
  val interleave: 'a seq * 'a seq -> 'a seq
  val its_right	: ('a * 'b seq -> 'b seq) -> 'a seq * 'b seq -> 'b seq
  val list_of_s	: 'a seq -> 'a list
  val mapp	: ('a -> 'b) -> 'a seq -> 'b seq -> 'b seq
  val maps	: ('a -> 'b) -> 'a seq -> 'b seq
  val null	: 'a seq
  val prints	: (int -> 'a -> unit) -> int -> 'a seq -> unit
  val pull	: 'a seq -> ('a * 'a seq) option
  val s_of_list	: 'a list -> 'a seq
  val seqof	: (unit -> ('a * 'a seq) option) -> 'a seq
  val single	: 'a -> 'a seq
  val tl	: 'a seq -> 'a seq
  end;


functor SequenceFun () : SEQUENCE = 
struct
    
datatype 'a seq = Seq of unit -> ('a * 'a seq)option;

(*Return next sequence element as None or Some(x,str) *)
fun pull(Seq f) = f();

(*Head and tail.  Beware of calling the sequence function twice!!*)
fun hd s = #1 (the (pull s))
and tl s = #2 (the (pull s));

(*the abstraction for making a sequence*)
val seqof = Seq;

(*prefix an element to the sequence
    use cons(x,s) only if evaluation of s need not be delayed,
      otherwise use seqof(fn()=> Some(x,s)) *)
fun cons all = Seq(fn()=>Some all);

(*the empty sequence*)
val null = Seq(fn()=>None);

fun single(x) = cons (x, null);

(*The list of the first n elements, paired with rest of sequence.
  If length of list is less than n, then sequence had less than n elements.*)
fun chop (n:int, s: 'a seq): 'a list * 'a seq =
  if n<=0 then ([],s)
  else case pull(s) of
           None => ([],s)
         | Some(x,s') => let val (xs,s'') = chop (n-1,s')
		         in  (x::xs, s'')  end;

(*conversion from sequence to list*)
fun list_of_s (s: 'a seq) : 'a list = case pull(s) of
        None => []
      | Some(x,s') => x :: list_of_s s';


(*conversion from list to sequence*)
fun s_of_list []     = null
  | s_of_list (x::l) = cons (x, s_of_list l);


(*functional to print a sequence, up to "count" elements
  the function prelem should print the element number and also the element*)
fun prints (prelem: int -> 'a -> unit) count (s: 'a seq) : unit =
  let fun pr (k,s) = 
	   if k>count then ()
	   else case pull(s) of
	       None => ()
	     | Some(x,s') => (prelem k x;  prs"\n";  pr (k+1, s'))
  in  pr(1,s)  end;

(*Map the function f over the sequence, making a new sequence*)
fun maps f xq = seqof (fn()=> case pull(xq) of
        None       => None
      | Some(x,yq) => Some(f x,  maps f yq));

(*Sequence append:  put the elements of xq in front of those of yq*)
fun append (xq,yq)  =
  let fun copy xq = seqof (fn()=>
	    case pull xq of  
		 None       => pull yq
	       | Some(x,xq') => Some (x, copy xq'))
  in  copy xq end;

(*Interleave elements of xq with those of yq -- fairer than append*)
fun interleave (xq,yq) = seqof (fn()=>
      case pull(xq) of  
          None       => pull yq
	| Some(x,xq') => Some (x, interleave(yq, xq')));

(*map over a sequence xq, append the sequence yq*)
fun mapp f xq yq =
  let fun copy s = seqof (fn()=> 
            case pull(s) of
	        None       => pull(yq)
              | Some(x,xq') => Some(f x, copy xq'))
  in  copy xq end;

(*Flatten a sequence of sequences to a single sequence. *)
fun flats ss = seqof (fn()=> case pull(ss) of
        None => None
      | Some(s,ss') =>  pull(append(s, flats ss')));

(*accumulating a function over a sequence;  this is lazy*)
fun its_right (f: 'a * 'b seq -> 'b seq) (s: 'a seq, bstr: 'b seq) : 'b seq =
  let fun its s = seqof (fn()=>
            case pull(s) of
	        None       => pull bstr
	      | Some(a,s') => pull(f(a, its s')))
  in  its s end; 

fun filters pred xq =
  let fun copy s = seqof (fn()=> 
            case pull(s) of
	        None       => None
              | Some(x,xq') => if pred x then Some(x, copy xq')
			       else pull (copy xq') )
  in  copy xq end

end;
