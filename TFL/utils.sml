(*  Title:      TFL/utils.sml
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Basic utilities.
*)

signature Utils_sig =
sig
  exception ERR of {module:string,func:string, mesg:string}

  val can   : ('a -> 'b) -> 'a -> bool
  val holds : ('a -> bool) -> 'a -> bool
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
  val itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val pluck : ('a -> bool) -> 'a list -> 'a * 'a list
  val zip3 : 'a list -> 'b list -> 'c list -> ('a*'b*'c) list
  val take  : ('a -> 'b) -> int * 'a list -> 'b list
  val sort  : ('a -> 'a -> bool) -> 'a list -> 'a list

end;


structure Utils = 
struct

(* Standard exception for TFL. *)
exception ERR of {module:string,func:string, mesg:string};
fun UTILS_ERR{func,mesg} = ERR{module = "Utils",func=func,mesg=mesg};


(* Simple combinators *)

fun C f x y = f y x

fun itlist f L base_value =
   let fun it [] = base_value
         | it (a::rst) = f a (it rst)
   in it L 
   end;

fun rev_itlist f =
   let fun rev_it [] base = base
         | rev_it (a::rst) base = rev_it rst (f a base)
   in rev_it
   end;

fun end_itlist f =
   let fun endit [] = raise UTILS_ERR{func="end_itlist", mesg="list too short"}
         | endit alist = 
            let val (base::ralist) = rev alist
            in itlist f (rev ralist) base
            end
   in endit
   end;

fun itlist2 f L1 L2 base_value =
 let fun it ([],[]) = base_value
       | it ((a::rst1),(b::rst2)) = f a b (it (rst1,rst2))
       | it _ = raise UTILS_ERR{func="itlist2",mesg="different length lists"}
 in  it (L1,L2)
 end;

fun pluck p  =
  let fun remv ([],_) = raise UTILS_ERR{func="pluck",mesg = "item not found"}
        | remv (h::t, A) = if p h then (h, rev A @ t) else remv (t,h::A)
  in fn L => remv(L,[])
  end;

fun take f =
  let fun grab(0,L) = []
        | grab(n, x::rst) = f x::grab(n-1,rst)
  in grab
  end;

fun zip3 [][][] = []
  | zip3 (x::l1) (y::l2) (z::l3) = (x,y,z)::zip3 l1 l2 l3
  | zip3 _ _ _ = raise UTILS_ERR{func="zip3",mesg="different lengths"};


fun can f x = (f x ; true) handle _ => false;
fun holds P x = P x handle _ => false;


fun sort R = 
let fun part (m, []) = ([],[])
      | part (m, h::rst) =
         let val (l1,l2) = part (m,rst)
         in if (R h m) then (h::l1, l2)
                       else (l1,  h::l2) end
    fun qsort [] = []
      | qsort (h::rst) = 
        let val (l1,l2) = part(h,rst)
        in qsort l1@ [h] @qsort l2
        end
in qsort
end;



end; (* Utils *)
