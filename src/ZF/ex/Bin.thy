(*  Title:      ZF/ex/Bin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Arithmetic on binary integers.

   The sign Plus stands for an infinite string of leading 0's.
   The sign Minus stands for an infinite string of leading 1's.

A number can have multiple representations, namely leading 0's with sign
Plus and leading 1's with sign Minus.  See twos-compl.ML/int_of_binary for
the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1

Division is not defined yet!
*)

Bin = Integ + Datatype + "twos_compl" +

consts
  bin_rec          :: "[i, i, i, [i,i,i]=>i] => i"
  integ_of_bin     :: "i=>i"
  norm_Bcons       :: "[i,i]=>i"
  bin_succ         :: "i=>i"
  bin_pred         :: "i=>i"
  bin_minus        :: "i=>i"
  bin_add,bin_mult :: "[i,i]=>i"

  bin              :: "i"

syntax
  "_Int"           :: "xnum => i"        ("_")

datatype
  "bin" = Plus
        | Minus
        | Bcons ("w: bin", "b: bool")
  type_intrs "[bool_into_univ]"


defs

  bin_rec_def
      "bin_rec(z,a,b,h) == 
      Vrec(z, %z g. bin_case(a, b, %w x. h(w, x, g`w), z))"

  integ_of_bin_def
      "integ_of_bin(w) == bin_rec(w, $#0, $~($#1), %w x r. $#x $+ r $+ r)"

    (** recall that cond(1,b,c)=b and cond(0,b,c)=0 **)

  (*norm_Bcons adds a bit, suppressing leading 0s and 1s*)
  norm_Bcons_def
      "norm_Bcons(w,b) ==   
       bin_case(cond(b,Bcons(w,b),w), cond(b,w,Bcons(w,b)),   
                %w' x'. Bcons(w,b), w)"

  bin_succ_def
      "bin_succ(w0) ==   
       bin_rec(w0, Bcons(Plus,1), Plus,   
               %w x r. cond(x, Bcons(r,0), norm_Bcons(w,1)))"

  bin_pred_def
      "bin_pred(w0) == 
       bin_rec(w0, Minus, Bcons(Minus,0),   
               %w x r. cond(x, norm_Bcons(w,0), Bcons(r,1)))"

  bin_minus_def
      "bin_minus(w0) == 
       bin_rec(w0, Plus, Bcons(Plus,1),   
               %w x r. cond(x, bin_pred(Bcons(r,0)), Bcons(r,0)))"

  bin_add_def
      "bin_add(v0,w0) ==                        
       bin_rec(v0,                             
         lam w:bin. w,                 
         lam w:bin. bin_pred(w),       
         %v x r. lam w1:bin.           
                  bin_rec(w1, Bcons(v,x), bin_pred(Bcons(v,x)),    
                    %w y s. norm_Bcons(r`cond(x and y, bin_succ(w), w), 
                                          x xor y)))    ` w0"

  bin_mult_def
      "bin_mult(v0,w) ==                        
       bin_rec(v0, Plus, bin_minus(w),         
         %v x r. cond(x, bin_add(norm_Bcons(r,0),w), norm_Bcons(r,0)))"
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
        (case explode str of
          "#" :: "~" :: cs => (~1, cs)
        | "#" :: cs => (1, cs)
        | _ => raise ERROR);

      val zs = prefix_len (equal "0") digs;

      fun bin_of 0 = replicate zs 0
        | bin_of ~1 = replicate zs 1 @ [~1]
        | bin_of n = (n mod 2) :: bin_of (n div 2);

      fun term_of [] = const "Plus"
        | term_of [~1] = const "Minus"
        | term_of (b :: bs) = const "Bcons" $ term_of bs $ mk_bit b;
    in
      term_of (bin_of (sign * (#1 (scan_int digs))))
    end;

  fun dest_bin tm =
    let
      fun bin_of (Const ("Plus", _)) = []
        | bin_of (Const ("Minus", _)) = [~1]
        | bin_of (Const ("Bcons", _) $ bs $ b) = dest_bit b :: bin_of bs
        | bin_of _ = raise Match;

      fun int_of [] = 0
        | int_of (b :: bs) = b + 2 * int_of bs;

      val rev_digs = bin_of tm;
      val (sign, zs) =
        (case rev rev_digs of
          ~1 :: bs => ("~", prefix_len (equal 1) bs)
        | bs => ("", prefix_len (equal 0) bs));
      val num = string_of_int (abs (int_of rev_digs));
    in
      "#" ^ sign ^ implode (replicate zs "0") ^ num
    end;


  (* translation of integer constant tokens to and from binary *)

  fun int_tr (*"_Int"*) [t as Free (str, _)] =
        (const "integ_of_bin" $
          (mk_bin str handle ERROR => raise_term "int_tr" [t]))
    | int_tr (*"_Int"*) ts = raise_term "int_tr" ts;

  fun int_tr' (*"integ_of"*) [t] = const "_Int" $ free (dest_bin t)
    | int_tr' (*"integ_of"*) _ = raise Match;
in
  val parse_translation = [("_Int", int_tr)];
  val print_translation = [("integ_of_bin", int_tr')];
end;
