(*---------------------------------------------------------------------------
 * Some common utilities. This strucuture is parameterized over
 * "int_to_string" because there is a difference between the string 
 * operations of SML/NJ versions 93 and 109.
 *---------------------------------------------------------------------------*)

functor UTILS (val int_to_string : int -> string) :Utils_sig = 
struct

(* Standard exception for TFL. *)
exception ERR of {module:string,func:string, mesg:string};
fun UTILS_ERR{func,mesg} = ERR{module = "Utils",func=func,mesg=mesg};

local 
fun info_string s {module,func,mesg} =
       (s^" at "^module^"."^func^":\n"^mesg^"\n")
in
val ERR_string = info_string "Exception raised"
val MESG_string = info_string "Message"
end;

fun Raise (e as ERR sss) = (output(std_out, ERR_string sss);  raise e)
  | Raise e = raise e;


(* option type *)
datatype 'a option = SOME of 'a | NONE


(* Simple combinators *)

infix 3 ##
fun f ## g = (fn (x,y) => (f x, g y))

fun W f x = f x x
fun C f x y = f y x
fun I x = x

fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y

fun fst(x,y) = x
fun snd(x,y) = y;

val concat = curry (op ^)
fun quote s = "\""^s^"\"";

fun map2 f L1 L2 =
 let fun mp2 [] [] L = rev L
       | mp2 (a1::rst1) (a2::rst2) L = mp2 rst1 rst2 (f a1 a2::L)
       | mp2 _ _ _ = raise UTILS_ERR{func="map2",mesg="different length lists"}
   in mp2 L1 L2 []
   end;


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

fun filter p L = itlist (fn x => fn y => if (p x) then x::y else y) L []

fun mapfilter f alist = itlist (fn i=>fn L=> (f i::L) handle _ => L) alist [];

fun pluck p  =
  let fun remv ([],_) = raise UTILS_ERR{func="pluck",mesg = "item not found"}
        | remv (h::t, A) = if p h then (h, rev A @ t) else remv (t,h::A)
  in fn L => remv(L,[])
  end;

fun front_back [] = raise UTILS_ERR{func="front_back",mesg="empty list"}
  | front_back [x] = ([],x)
  | front_back (h::t) = 
       let val (L,b) = front_back t
       in (h::L,b)
       end;

fun take f =
  let fun grab(0,L) = []
        | grab(n, x::rst) = f x::grab(n-1,rst)
  in grab
  end;

fun all p =
   let fun every [] = true
         | every (a::rst) = (p a) andalso every rst       
   in every 
   end;

fun exists p =
   let fun ex [] = false
         | ex (a::rst) = (p a) orelse ex rst       
   in ex 
   end;

fun zip [] [] = []
  | zip (a::b) (c::d) = (a,c)::(zip b d)
  | zip _ _ = raise UTILS_ERR{func = "zip",mesg = "different length lists"};

fun unzip L = itlist (fn (x,y) => fn (l1,l2) =>((x::l1),(y::l2))) L ([],[]);

fun zip3 [][][] = []
  | zip3 (x::l1) (y::l2) (z::l3) = (x,y,z)::zip3 l1 l2 l3
  | zip3 _ _ _ = raise UTILS_ERR{func="zip3",mesg="different lengths"};


fun can f x = (f x ; true) handle _ => false;
fun holds P x = P x handle _ => false;


fun assert p x = 
 if (p x) then x else raise UTILS_ERR{func="assert", mesg="predicate not true"}

fun assoc1 eq item =
   let fun assc ((entry as (key,_))::rst) = 
             if eq(item,key) then SOME entry else assc rst
         | assc [] = NONE
    in assc
    end;

(* Set ops *)
nonfix mem union;  (* Gag Barf Choke *)
fun mem eq_func i =
   let val eqi = eq_func i
       fun mm [] = false
         | mm (a::rst) = eqi a orelse mm rst
   in mm
   end;

fun union eq_func =
   let val mem = mem eq_func
       fun un S1 []  = S1
         | un [] S1  = S1
         | un (a::rst) S2 = if (mem a S2) then (un rst S2) else (a::un rst S2)
   in un
   end;

fun mk_set eq_func =
   let val mem = mem eq_func
       fun mk [] = []
         | mk (a::rst) = if (mem a rst) then mk rst else a::(mk rst)
   in mk
   end;

(* Union of a family of sets *)
fun Union eq_func set_o_sets = itlist (union eq_func) set_o_sets [];

fun intersect eq_func S1 S2 = mk_set eq_func (filter (C (mem eq_func) S2) S1);

(* All the elements in the first set that are not also in the second set. *)
fun set_diff eq_func S1 S2 = filter (fn x => not (mem eq_func x S2)) S1

fun set_eq eq_func S1 S2 = 
   null(set_diff eq_func S1 S2) andalso null(set_diff eq_func S2 S1);


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


val int_to_string = int_to_string;

end; (* Utils *)
