(*  Title:      Pure/nbe_eval.ML
    ID:         $Id$
    Author:     Klaus Aehlig, LMU Muenchen; Tobias Nipkow, TU Muenchen

Evaluator infrastructure for "normalization by evaluation".
*)

(* Optimizations:
 int instead of string in Constr
 treat int via ML ints
*)

signature NBE_EVAL =
sig
  (*named terms used for output only*)
  datatype nterm =
      C of string         (*named constants*)
    | V of string         (*free variable*)
    | B of int            (*named(!!) bound variables*)
    | A of nterm * nterm  (*application*)
    | AbsN of int * nterm (*binding of named variables*);
  datatype Univ = 
      Constr of string*(Univ list)       (*named constructors*)
    | Var of string*(Univ list)          (*free variables*)
    | BVar of int*(Univ list)            (*bound named variables*)
    | Fun of (Univ list -> Univ) * (Univ list) * int * (unit -> nterm)
                                         (*functions*);

  val eval: theory -> Univ Symtab.table -> term -> nterm
  val apply: Univ -> Univ -> Univ
  val prep_term: theory -> term -> term

  val to_term: Univ -> nterm

  val mk_Fun: string * (Univ list -> Univ) * int -> string * Univ
  val new_name: unit -> int

  val string_of_nterm: nterm -> string
end;

structure NBE_Eval: NBE_EVAL =
struct

datatype nterm =
    C of string
  | V of string
  | B of int
  | A of nterm * nterm
  | AbsN of int * nterm;

fun string_of_nterm(C s) = "(C \"" ^ s ^ "\")"
  | string_of_nterm(V s) = "(V \"" ^ s ^ "\")"
  | string_of_nterm(B n) = "(B " ^ string_of_int n ^ ")"
  | string_of_nterm(A(s,t)) =
       "(A " ^ string_of_nterm s ^ string_of_nterm t ^ ")"
  | string_of_nterm(AbsN(n,t)) =
      "(Abs " ^ string_of_int n ^ " " ^ string_of_nterm t ^ ")";

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
  | to_term (Var   (name, args))    = apps (V name) (map to_term args)
  | to_term (BVar  (name, args))    = apps (B name) (map to_term args)
  | to_term (Fun(_,args,_,name_thunk)) = apps (name_thunk ()) (map to_term args);

(*
   A typical operation, why functions might be good for, is
   application. Moreover, functions are the only values that can
   reasonably we applied in a semantical way.
*)

fun apply (Fun(f,xs,1,name))  x = f (x::xs)
  | apply (Fun(f,xs,n,name))  x = Fun(f,x::xs,n-1,name)
  | apply (Constr(name,args)) x = Constr(name,x::args)
  | apply (Var(name,args))    x = Var(name,x::args)
  | apply (BVar(name,args))   x = BVar(name,x::args);

fun mk_Fun(name,v,0) = (name,v [])
  | mk_Fun(name,v,n) = (name,Fun(v,[],n, fn () => C name));


(* ------------------ evaluation with greetings to Tarski ------------------ *)

fun prep_term thy (Const c) = Const (CodegenNames.const thy
      (CodegenConsts.const_of_cexpr thy c), dummyT)
  | prep_term thy (Free v_ty) = Free v_ty
  | prep_term thy (s $ t) = prep_term thy s $ prep_term thy t
  | prep_term thy (Abs (raw_v, ty, raw_t)) =
      let
        val (v, t) = Syntax.variant_abs (raw_v, ty, raw_t);
      in Abs (v, ty, prep_term thy t) end;


(* generation of fresh names *)

val counter = ref 0;
fun new_name () = (counter := !counter +1; !counter);


(* greetings to Tarski *)

fun eval thy tab t =
  let
    fun evl vars (Const (s, _)) =
          the_default (Constr (s, [])) (Symtab.lookup tab s)
      | evl vars (Free (v, _)) =
          the_default (Var (v, [])) (AList.lookup (op =) vars v)
      | evl vars (s $ t) =
          apply (evl vars s) (evl vars t)
      | evl vars (Abs (v, _, t)) =
          Fun (fn [x] => evl (AList.update (op =) (v, x) vars) t, [], 1,
            fn () => let val var = new_name() in
              AbsN (var, to_term (evl (AList.update (op =) (v, BVar (var, [])) vars) t)) end)
  in (counter := 0; to_term (evl [] (prep_term thy t))) end;

end;
