(*  Title:	HOL/Integ/Bin.thy
    Authors:	Lawrence C Paulson, Cambridge University Computer Laboratory
		David Spelt, University of Twente 
    Copyright	1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.

   The sign Plus stands for an infinite string of leading F's.
   The sign Minus stands for an infinite string of leading T's.

A number can have multiple representations, namely leading F's with sign
Plus and leading T's with sign Minus.  See twos-compl.ML/int_of_binary for
the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1

Division is not defined yet!
*)

Bin = Integ + 

syntax
  "_Int"           :: xnum => int        ("_")

datatype
   bin = Plus
        | Minus
        | Bcons bin bool

consts
  integ_of_bin     :: bin=>int
  norm_Bcons       :: [bin,bool]=>bin
  bin_succ         :: bin=>bin
  bin_pred         :: bin=>bin
  bin_minus        :: bin=>bin
  bin_add,bin_mult :: [bin,bin]=>bin
  h_bin :: [bin,bool,bin]=>bin

(*norm_Bcons adds a bit, suppressing leading 0s and 1s*)

primrec norm_Bcons bin
  norm_Plus  "norm_Bcons Plus  b = (if b then (Bcons Plus b) else Plus)"
  norm_Minus "norm_Bcons Minus b = (if b then Minus else (Bcons Minus b))"
  norm_Bcons "norm_Bcons (Bcons w' x') b = Bcons (Bcons w' x') b"
 
primrec integ_of_bin bin
  iob_Plus  "integ_of_bin Plus = $#0"
  iob_Minus "integ_of_bin Minus = $~($#1)"
  iob_Bcons "integ_of_bin(Bcons w x) = (if x then $#1 else $#0) + (integ_of_bin w) + (integ_of_bin w)" 

primrec bin_succ bin
  succ_Plus  "bin_succ Plus = Bcons Plus True" 
  succ_Minus "bin_succ Minus = Plus"
  succ_Bcons "bin_succ(Bcons w x) = (if x then (Bcons (bin_succ w) False) else (norm_Bcons w True))"

primrec bin_pred bin
  pred_Plus  "bin_pred(Plus) = Minus"
  pred_Minus "bin_pred(Minus) = Bcons Minus False"
  pred_Bcons "bin_pred(Bcons w x) = (if x then (norm_Bcons w False) else (Bcons (bin_pred w) True))"
 
primrec bin_minus bin
  min_Plus  "bin_minus Plus = Plus"
  min_Minus "bin_minus Minus = Bcons Plus True"
  min_Bcons "bin_minus(Bcons w x) = (if x then (bin_pred (Bcons (bin_minus w) False)) else (Bcons (bin_minus w) False))"

primrec bin_add bin
  add_Plus  "bin_add Plus w = w"
  add_Minus "bin_add Minus w = bin_pred w"
  add_Bcons "bin_add (Bcons v x) w = h_bin v x w"

primrec bin_mult bin
  mult_Plus "bin_mult Plus w = Plus"
  mult_Minus "bin_mult Minus w = bin_minus w"
  mult_Bcons "bin_mult (Bcons v x) w = (if x then (bin_add (norm_Bcons (bin_mult v w) False) w) else (norm_Bcons (bin_mult v w) False))"

primrec h_bin bin
  h_Plus  "h_bin v x Plus =  Bcons v x"
  h_Minus "h_bin v x Minus = bin_pred (Bcons v x)"
  h_BCons "h_bin v x (Bcons w y) = norm_Bcons (bin_add v (if (x & y) then bin_succ w else w)) (x~=y)" 

end

ML

(** Concrete syntax for integers **)

local
  open Syntax;

  (* Bits *)

  fun mk_bit 0 = const "False"
    | mk_bit 1 = const "True"
    | mk_bit _ = sys_error "mk_bit";

  fun dest_bit (Const ("False", _)) = 0
    | dest_bit (Const ("True", _)) = 1
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
