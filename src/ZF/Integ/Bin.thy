(*  Title:      ZF/ex/Bin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Arithmetic on binary integers.

   The sign Pls stands for an infinite string of leading 0's.
   The sign Min stands for an infinite string of leading 1's.

A number can have multiple representations, namely leading 0's with sign
Pls and leading 1's with sign Min.  See twos-compl.ML/int_of_binary for
the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1

Division is not defined yet!
*)

Bin = Int + Datatype + 

consts
  integ_of  :: i=>i
  NCons     :: [i,i]=>i
  bin_succ  :: i=>i
  bin_pred  :: i=>i
  bin_minus :: i=>i
  bin_add   :: [i,i]=>i
  adding    :: [i,i,i]=>i
  bin_mult  :: [i,i]=>i

  bin       :: i

syntax
  "_Int"           :: xnum => i        ("_")

datatype
  "bin" = Pls
        | Min
        | Cons ("w: bin", "b: bool")
  type_intrs "[bool_into_univ]"


primrec
  "integ_of (Pls)       = $# 0"
  "integ_of (Min)       = $~($#1)"
  "integ_of (Cons(w,b)) = $#b $+ integ_of(w) $+ integ_of(w)"

    (** recall that cond(1,b,c)=b and cond(0,b,c)=0 **)

primrec (*NCons adds a bit, suppressing leading 0s and 1s*)
  "NCons (Pls,b)       = cond(b,Cons(Pls,b),Pls)"
  "NCons (Min,b)       = cond(b,Min,Cons(Min,b))"
  "NCons (Cons(w,c),b) = Cons(Cons(w,c),b)"

primrec (*successor.  If a Cons, can change a 0 to a 1 without recursion.*)
  bin_succ_Pls
    "bin_succ (Pls)       = Cons(Pls,1)"
  bin_succ_Min
    "bin_succ (Min)       = Pls"
      "bin_succ (Cons(w,b)) = cond(b, Cons(bin_succ(w), 0),
				    NCons(w,1))"

primrec (*predecessor*)
  bin_pred_Pls
    "bin_pred (Pls)       = Min"
  bin_pred_Min
    "bin_pred (Min)       = Cons(Min,0)"
    "bin_pred (Cons(w,b)) = cond(b, NCons(w,0),
				    Cons(bin_pred(w), 1))"

primrec (*unary negation*)
  bin_minus_Pls
    "bin_minus (Pls)       = Pls"
  bin_minus_Min
    "bin_minus (Min)       = Cons(Pls,1)"
    "bin_minus (Cons(w,b)) = cond(b, bin_pred(NCons(bin_minus(w),0)),
				     Cons(bin_minus(w),0))"

(*Mutual recursion is not always sound, but it is for primitive recursion.*)
primrec (*sum*)
  "bin_add (Pls,w)       = w"
  "bin_add (Min,w)       = bin_pred(w)"
  "bin_add (Cons(v,x),w) = adding(v,x,w)"

primrec (*auxilliary function for sum*)
  "adding (v,x,Pls)       = Cons(v,x)"
  "adding (v,x,Min)       = bin_pred(Cons(v,x))"
  "adding (v,x,Cons(w,y)) = NCons(bin_add (v, cond(x and y, bin_succ(w), w)), 
				  x xor y)"

primrec
  bin_mult_Pls
    "bin_mult (Pls,w)       = Pls"
  bin_mult_Min
    "bin_mult (Min,w)       = bin_minus(w)"
    "bin_mult (Cons(v,b),w) = cond(b, bin_add(NCons(bin_mult(v,w),0),w),
				      NCons(bin_mult(v,w),0))"

end


ML

(** Concrete syntax for integers **)

local
  open Syntax;

  (* Bits *)

  fun mk_bit 0 = const "0"
    | mk_bit 1 = const "succ" $ const "0"
    | mk_bit _ = sys_error "mk_bit";

  fun dest_bit (Const ("0", _)) = 0
    | dest_bit (Const ("succ", _) $ Const ("0", _)) = 1
    | dest_bit _ = raise Match;


  (* Bit strings *)   (*we try to handle superfluous leading digits nicely*)

  fun prefix_len _ [] = 0
    | prefix_len pred (x :: xs) =
        if pred x then 1 + prefix_len pred xs else 0;

  fun mk_bin str =
    let
      val (sign, digs) =
        (case Symbol.explode str of
          "#" :: "-" :: cs => (~1, cs)
        | "#" :: cs => (1, cs)
        | _ => raise ERROR);

      val zs = prefix_len (equal "0") digs;

      fun bin_of 0  = []
        | bin_of ~1 = [~1]
        | bin_of n  = (n mod 2) :: bin_of (n div 2);

      fun term_of [] = const "Pls"
        | term_of [~1] = const "Min"
        | term_of (b :: bs) = const "Cons" $ term_of bs $ mk_bit b;
    in
      term_of (bin_of (sign * (#1 (read_int digs))))
    end;

  fun dest_bin tm =
    let
      fun bin_of (Const ("Pls", _)) = []
        | bin_of (Const ("Min", _)) = [~1]
        | bin_of (Const ("Cons", _) $ bs $ b) = dest_bit b :: bin_of bs
        | bin_of _ = raise Match;

      fun integ_of [] = 0
        | integ_of (b :: bs) = b + 2 * integ_of bs;

      val rev_digs = bin_of tm;
      val (sign, zs) =
        (case rev rev_digs of
          ~1 :: bs => ("-", prefix_len (equal 1) bs)
        | bs => ("", prefix_len (equal 0) bs));
      val num = string_of_int (abs (integ_of rev_digs));
    in
      "#" ^ sign ^ implode (replicate zs "0") ^ num
    end;


  (* translation of integer constant tokens to and from binary *)

  fun int_tr (*"_Int"*) [t as Free (str, _)] =
        (const "integ_of" $
          (mk_bin str handle ERROR => raise TERM ("int_tr", [t])))
    | int_tr (*"_Int"*) ts = raise TERM ("int_tr", ts);

  fun int_tr' (*"integ_of"*) [t] = const "_Int" $ free (dest_bin t)
    | int_tr' (*"integ_of"*) _ = raise Match;
in
  val parse_translation = [("_Int", int_tr)];
  val print_translation = [("integ_of", int_tr')];
end;
