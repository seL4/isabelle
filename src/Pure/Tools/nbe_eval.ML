(*  ID:         $Id$
    Author:     Klaus Aehlig, Tobias Nipkow
*)

(* ------------------------------ Evaluator  ------------------------------ *)

(* Optimizations:
 int instead of string in Constr
 xtab as real table
 treat int via ML ints
*)

signature NBE_EVAL =
sig
(* named terms used for output only *)
datatype nterm =
    C of string (* Named Constants *)
  | V of string (* Free Variable *)
  | B of int (* Named(!!) Bound Variables *)
  | A of nterm*nterm (* Application *)
  | AbsN of int*nterm ; (* Binding of named Variables *)

val nbe: term -> nterm

datatype Univ = 
    Constr of string*(Univ list)       (* Named Constructors *)
  | Var of string*(Univ list)          (* Free variables *)
  | BVar of int*(Univ list)            (* Bound named variables *)
  | Fun of (Univ list -> Univ) * (Univ list) * int * (unit -> nterm);
                                            (* Functions *)
val apply: Univ -> Univ -> Univ;
val to_term: Univ -> nterm;

val lookup: string -> Univ;
val is_constr: string -> bool;
val register: string * (Univ list -> Univ) * int -> unit
val new_name: unit -> int;

(* For testing
val eval: term -> (Univ list) -> Univ
*)

end;

(* FIXME add_funs and relatives should NOT be exported. Eventually it
should work like for quickcheck: Eval generates code which leaves the
function values in a public reference variable, the code is executed,
and the value of the reference variable is added to the internal
tables, all in one go, w/o interruption. *)


structure NBE_Eval:NBE_EVAL =
struct

datatype nterm =
    C of string (* Named Constants *)
  | V of string (* Free Variable *)
  | B of int (* Named(!!) Variables *)
  | A of nterm * nterm (* Application *)
  | AbsN of int * nterm (* Binding of named Variables *);

fun apps t args = foldr (fn (y,x) => A(x,y)) t args;

(* ------------------------------ The semantical universe --------------------- *)

(*
   Functions are given by their semantical function value. To avoid
   trouble with the ML-type system, these functions have the most
   generic type, that is "Univ list -> Univ". The calling convention is
   that the arguments come as a list, the last argument first. In
   other words, a function call that usually would look like

   f x_1 x_2 ... x_n   or   f(x_1,x_2, ..., x_n)

   would be in our convention called as

              f [x_n,..,x_2,x_1]

   Moreover, to handle functions that are still waiting for some
   arguments we have additionally a list of arguments collected to far
   and the number of arguments we're still waiting for.

   Finally, it might happen, that a function does not get all the
   arguments it needs. In this case the function must provide means to
   present itself as a string. As this might be a heavy-wight
   operation, we delay it.
*)

datatype Univ = 
    Constr of string*(Univ list)       (* Named Constructors *)
  | Var of string*(Univ list)          (* Free variables *)
  | BVar of int*(Univ list)         (* Bound named variables *)
  | Fun of (Univ list -> Univ) * (Univ list) * int * (unit -> nterm);

fun to_term (Constr(name, args))    = apps (C name) (map to_term args)
  |	to_term (Var   (name, args))    = apps (V name) (map to_term args)
  |	to_term (BVar  (name, args))    = apps (B name) (map to_term args)
  |	to_term (Fun(_,args,_,name_thunk)) = apps (name_thunk ()) (map to_term args);

(*
   A typical operation, why functions might be good for, is
   application. Moreover, functions are the only values that can
   reasonably we applied in a semantical way.
*)

fun  apply (Fun(f,xs,1,name))  x = f (x::xs)
   | apply (Fun(f,xs,n,name))  x = Fun(f,x::xs,n-1,name)
   | apply (Constr(name,args)) x = Constr(name,x::args)
   | apply (Var(name,args))    x = Var(name,x::args)
   | apply (BVar(name,args))   x = BVar(name,x::args);

(* ---------------- table with the meaning of constants -------------------- *)

val xfun_tab: (string * Univ)list ref = ref [];
fun do_register sx = (xfun_tab := sx :: !xfun_tab);
fun register(name,v,0) = do_register(name,v [])
  | register(name,v,n) = do_register(name,Fun(v,[],n, fn () => C name));

fun do_lookup [] s          = NONE
  |	do_lookup ((n,v)::xs) s = if (s=n) then SOME v else do_lookup xs s;

fun lookup s = case do_lookup (!xfun_tab) s of
    SOME x => x
  | NONE   => Constr(s,[]);

fun is_constr s = is_none (do_lookup (!xfun_tab) s);

(* ------------------ evaluation with greetings to Tarski ------------------ *)

(* generation of fresh names *)

val counter = ref 0;

fun new_name() = (counter := !counter +1; !counter);

(* greetings to Tarski *)

fun eval(Const(f,_)) xs = lookup f
  | eval(Free(x,_)) xs = Var(x,[])
  | eval(Bound n) xs = List.nth(xs,n)
  | eval(s $ t) xs = apply (eval s xs) (eval t xs)
  | eval(Abs(_,_, t)) xs = Fun ((fn [x] => eval t (x::xs)),[],1,
                           fn () => let val var = new_name() in
                         AbsN(var, to_term (eval t ((BVar(var,[]) :: xs)))) end);


(* finally... *)

fun nbe t = (counter :=0; to_term(eval t []));

end;
