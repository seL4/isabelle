(*  Title:	HOL/Integ/Bin.thy
    Authors:	Lawrence C Paulson, Cambridge University Computer Laboratory
		David Spelt, University of Twente 
    Copyright	1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.

   The sign PlusSign stands for an infinite string of leading F's.
   The sign MinusSign stands for an infinite string of leading T's.

A number can have multiple representations, namely leading F's with sign
PlusSign and leading T's with sign MinusSign.  See twos-compl.ML/int_of_binary
for the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1

Division is not defined yet!  To do it efficiently requires computing the
quotient and remainder using ML and checking the answer using multiplication
by proof.  Then uniqueness of the quotient and remainder yields theorems
quoting the previously computed values.  (Or code an oracle...)
*)

Bin = Integ + 

syntax
  "_Int"           :: xnum => int        ("_")

datatype
    bin = PlusSign
        | MinusSign
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
  norm_Plus  "norm_Bcons PlusSign  b = (if b then (Bcons PlusSign b) else PlusSign)"
  norm_Minus "norm_Bcons MinusSign b = (if b then MinusSign else (Bcons MinusSign b))"
  norm_Bcons "norm_Bcons (Bcons w' x') b = Bcons (Bcons w' x') b"
 
primrec integ_of_bin bin
  iob_Plus  "integ_of_bin PlusSign = $#0"
  iob_Minus "integ_of_bin MinusSign = $~($#1)"
  iob_Bcons "integ_of_bin(Bcons w x) = (if x then $#1 else $#0) + (integ_of_bin w) + (integ_of_bin w)" 

primrec bin_succ bin
  succ_Plus  "bin_succ PlusSign = Bcons PlusSign True" 
  succ_Minus "bin_succ MinusSign = PlusSign"
  succ_Bcons "bin_succ(Bcons w x) = (if x then (Bcons (bin_succ w) False) else (norm_Bcons w True))"

primrec bin_pred bin
  pred_Plus  "bin_pred(PlusSign) = MinusSign"
  pred_Minus "bin_pred(MinusSign) = Bcons MinusSign False"
  pred_Bcons "bin_pred(Bcons w x) = (if x then (norm_Bcons w False) else (Bcons (bin_pred w) True))"
 
primrec bin_minus bin
  min_Plus  "bin_minus PlusSign = PlusSign"
  min_Minus "bin_minus MinusSign = Bcons PlusSign True"
  min_Bcons "bin_minus(Bcons w x) = (if x then (bin_pred (Bcons (bin_minus w) False)) else (Bcons (bin_minus w) False))"

primrec bin_add bin
  add_Plus  "bin_add PlusSign w = w"
  add_Minus "bin_add MinusSign w = bin_pred w"
  add_Bcons "bin_add (Bcons v x) w = h_bin v x w"

primrec bin_mult bin
  mult_Plus "bin_mult PlusSign w = PlusSign"
  mult_Minus "bin_mult MinusSign w = bin_minus w"
  mult_Bcons "bin_mult (Bcons v x) w = (if x then (bin_add (norm_Bcons (bin_mult v w) False) w) else (norm_Bcons (bin_mult v w) False))"

primrec h_bin bin
  h_Plus  "h_bin v x PlusSign =  Bcons v x"
  h_Minus "h_bin v x MinusSign = bin_pred (Bcons v x)"
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
        (case Symbol.explode str of
          "#" :: "~" :: cs => (~1, cs)
        | "#" :: cs => (1, cs)
        | _ => raise ERROR);

      val zs = prefix_len (equal "0") digs;

      fun bin_of 0 = replicate zs 0
        | bin_of ~1 = replicate zs 1 @ [~1]
        | bin_of n = (n mod 2) :: bin_of (n div 2);

      fun term_of [] = const "PlusSign"
        | term_of [~1] = const "MinusSign"
        | term_of (b :: bs) = const "Bcons" $ term_of bs $ mk_bit b;
    in
      term_of (bin_of (sign * (#1 (read_int digs))))
    end;

  fun dest_bin tm =
    let
      fun bin_of (Const ("PlusSign", _)) = []
        | bin_of (Const ("MinusSign", _)) = [~1]
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
          (mk_bin str handle ERROR => raise TERM ("int_tr", [t])))
    | int_tr (*"_Int"*) ts = raise TERM ("int_tr", ts);

  fun int_tr' (*"integ_of"*) [t] = const "_Int" $ free (dest_bin t)
    | int_tr' (*"integ_of"*) _ = raise Match;
in
  val parse_translation = [("_Int", int_tr)];
  val print_translation = [("integ_of_bin", int_tr')]; 
end;
