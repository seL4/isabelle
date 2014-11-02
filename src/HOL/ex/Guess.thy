(*
    Author:     Makarius
*)

section {* Proof by guessing *}

theory Guess
imports Main
begin

lemma True
proof

  have 1: "\<exists>x. x = x" by simp

  from 1 guess ..
  from 1 guess x ..
  from 1 guess x :: 'a ..
  from 1 guess x :: nat ..

  have 2: "\<exists>x y. x = x & y = y" by simp
  from 2 guess apply - apply (erule exE conjE)+ done
  from 2 guess x apply - apply (erule exE conjE)+ done
  from 2 guess x y apply - apply (erule exE conjE)+ done
  from 2 guess x :: 'a and y :: 'b apply - apply (erule exE conjE)+ done
  from 2 guess x y :: nat apply - apply (erule exE conjE)+ done

qed

end
