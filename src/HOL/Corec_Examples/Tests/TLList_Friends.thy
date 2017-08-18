(*  Title:      HOL/Corec_Examples/Tests/TLList_Friends.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Friendly functions on terminated lists.
*)

section \<open>Friendly Functions on Terminated Lists\<close>

theory TLList_Friends
imports "HOL-Library.BNF_Corec"
begin

codatatype ('a, 'b) tllist =
  TLNil (trm: 'b)
| TLCons (tlhd: 'a) (tltl: "('a, 'b) tllist")

corec pls :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "pls s s' = TLCons (tlhd s + tlhd s') (pls (tltl s) (tltl s'))"

friend_of_corec pls where
  "pls s s' = TLCons (tlhd s + tlhd s') (pls (tltl s) (tltl s'))"
  sorry

corec prd :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "prd xs ys = TLCons (tlhd xs * tlhd ys) (pls (prd xs (tltl ys)) (prd (tltl xs) ys))"

friend_of_corec prd where
  "prd xs ys = TLCons (tlhd xs * tlhd ys) (pls (prd xs (tltl ys)) (prd (tltl xs) ys))"
  sorry

corec onetwo :: "(nat, 'b) tllist" where
  "onetwo = TLCons 1 (TLCons 2 onetwo)"

corec Exp :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "Exp xs = TLCons (2 ^^ tlhd xs) (prd (tltl xs) (Exp xs))"

friend_of_corec Exp where
  "Exp xs = TLCons (2 ^^ tlhd xs) (prd (tltl xs) (Exp xs))"
  sorry

corec prd2 :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "prd2 xs ys = TLCons (tlhd xs * tlhd ys) (pls (prd xs (tltl ys)) (prd2 (tltl xs) ys))"

text \<open>Outer if:\<close>

corec takeUntilOdd :: "(int, int) tllist \<Rightarrow> (int, int) tllist" where
  "takeUntilOdd xs =
     (if is_TLNil xs then TLNil (trm xs)
      else if tlhd xs mod 2 = 0 then TLCons (tlhd xs) (takeUntilOdd (tltl xs))
      else TLNil (tlhd xs))"

friend_of_corec takeUntilOdd where
  "takeUntilOdd xs =
     (if is_TLNil xs then TLNil (trm xs)
      else if tlhd xs mod 2 = 0 then TLCons (tlhd xs) (takeUntilOdd (tltl xs))
      else TLNil (tlhd xs))"
      sorry

corec takeUntilEven :: "(int, int) tllist \<Rightarrow> (int, int) tllist" where
  "takeUntilEven xs =
     (case xs of
        TLNil y \<Rightarrow> TLNil y
      | TLCons y ys \<Rightarrow>
        if y mod 2 = 1 then TLCons y (takeUntilEven ys)
        else TLNil y)"

friend_of_corec takeUntilEven where
  "takeUntilEven xs =
     (case xs of
        TLNil y \<Rightarrow> TLNil y
      | TLCons y ys \<Rightarrow>
        if y mod 2 = 1 then TLCons y (takeUntilEven ys)
        else TLNil y)"
        sorry

text \<open>If inside the constructor:\<close>

corec prd3 :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "prd3 xs ys = TLCons (tlhd xs * tlhd ys)
     (if undefined then pls (prd xs (tltl ys)) (prd (tltl xs) ys)
      else prd3 (tltl xs) (tltl ys))"

friend_of_corec prd3 where
  "prd3 xs ys = TLCons (tlhd xs * tlhd ys)
     (if undefined then pls (prd xs (tltl ys)) (prd (tltl xs) ys)
      else prd3 (tltl xs) (tltl ys))"
 sorry

text \<open>If inside the inner friendly operation:\<close>

corec prd4 :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "prd4 xs ys = TLCons (tlhd xs * tlhd ys)
     (pls (if undefined then prd xs (tltl ys) else xs) (prd (tltl xs) ys))"

friend_of_corec prd4 :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "prd4 xs ys = TLCons (tlhd xs * tlhd ys)
     (pls (if undefined then prd xs (tltl ys) else xs) (prd (tltl xs) ys))"
  sorry

text \<open>Lots of if's:\<close>

corec iffy :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
  "iffy xs =
   (if undefined (0::nat) then
      TLNil undefined
    else
      Exp (if undefined (1::nat) then
             Exp undefined
           else
             TLCons undefined
               (if undefined (2::nat) then
                  Exp (if undefined (3::nat) then
                         Exp (if undefined (4::nat) then
                                iffy (tltl xs)
                              else if undefined (5::nat) then
                                iffy xs
                              else
                                xs)
                       else
                         xs)
                else
                  undefined)))"

end
