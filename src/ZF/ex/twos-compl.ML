(*  Title: 	ZF/ex/twos-compl.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

ML code for Arithmetic on binary integers; the model for theory BinFn

   The sign Plus stands for an infinite string of leading 0's.
   The sign Minus stands for an infinite string of leading 1's.

A number can have multiple representations, namely leading 0's with sign
Plus and leading 1's with sign Minus.  See int_of_binary for the numerical
interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1

Still needs division!

print_depth 40;
System.Control.Print.printDepth := 350; 
*)

infix 5 $$ 

(*Recursive datatype of binary integers*)
datatype bin = Plus | Minus | op $$ of bin * int;

(** Conversions between bin and int **)

fun int_of_binary Plus = 0
  | int_of_binary Minus = ~1
  | int_of_binary (w$$b) = 2 * int_of_binary w + b;

fun binary_of_int 0 = Plus
  | binary_of_int ~1 = Minus
  | binary_of_int n = binary_of_int (n div 2) $$ (n mod 2);

(*** Addition ***)

(*Adding one to a number*)
fun bin_succ Plus = Plus$$1
  | bin_succ Minus = Plus
  | bin_succ (w$$1) = bin_succ(w) $$ 0
  | bin_succ (w$$0) = w$$1;

(*Subtracing one from a number*)
fun bin_pred Plus = Minus
  | bin_pred Minus = Minus$$0
  | bin_pred (w$$1) = w$$0
  | bin_pred (w$$0) = bin_pred(w) $$ 1;

(*sum of two binary integers*)
fun bin_add (Plus, w) = w
  | bin_add (Minus, w) = bin_pred w
  | bin_add (v$$x, Plus) = v$$x
  | bin_add (v$$x, Minus) = bin_pred (v$$x)
  | bin_add (v$$x, w$$y) = bin_add(v, if x+y=2 then bin_succ w else w) $$ 
                           ((x+y) mod 2);

(*** Subtraction ***)

(*Unary minus*)
fun bin_minus Plus = Plus
  | bin_minus Minus = Plus$$1
  | bin_minus (w$$1) = bin_pred (bin_minus(w) $$ 0)
  | bin_minus (w$$0) = bin_minus(w) $$ 0;

(*** Multiplication ***)

(*product of two bins*)
fun bin_mult (Plus, _) = Plus
  | bin_mult (Minus, v) = bin_minus v
  | bin_mult (w$$1, v) = bin_add(bin_mult(w,v) $$ 0,  v)
  | bin_mult (w$$0, v) = bin_mult(w,v) $$ 0;

(*** Testing ***)

(*tests addition*)
fun checksum m n =
    let val wm = binary_of_int m
        and wn = binary_of_int n
        val wsum = bin_add(wm,wn)
    in  if m+n = int_of_binary wsum then (wm, wn, wsum, m+n)
        else raise Match
    end;

fun bfact n = if n=0 then  Plus$$1  
              else  bin_mult(binary_of_int n, bfact(n-1));

(*Examples...
bfact 5;
int_of_binary it;
bfact 69;
int_of_binary it;

(*leading zeros!*)
bin_add(binary_of_int 1234, binary_of_int ~1234);
bin_mult(binary_of_int 1234, Plus);

(*leading ones!*)
bin_add(binary_of_int 1234, binary_of_int ~1235);
*)
