(*  Title:      Pure/ex/Guess_Examples.thy
    Author:     Makarius
*)

section \<open>Proof by wild guessing\<close>

theory Guess_Examples
imports "Pure-Examples.Higher_Order_Logic" Guess
begin

typedecl t
instance t :: type ..

notepad
begin
  have 1: "\<exists>x :: 'a. x = x" by (intro exI refl)

  from 1 guess ..
  from 1 guess x ..
  from 1 guess x :: 'a ..
  from 1 guess x :: t ..

  have 2: "\<exists>(x::'c) (y::'d). x = x \<and> y = y" by (intro exI conjI refl)
  from 2 guess apply - apply (erule exE conjE)+ done
  from 2 guess x apply - apply (erule exE conjE)+ done
  from 2 guess x y apply - apply (erule exE conjE)+ done
  from 2 guess x :: 'a and y :: 'b apply - apply (erule exE conjE)+ done
  from 2 guess x y :: t apply - apply (erule exE conjE)+ done
end

end
