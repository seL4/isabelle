theory FP0 = PreList:

datatype 'a list = Nil                          ("[]")
                 | Cons 'a "'a list"            (infixr "#" 65)

consts app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"   (infixr "@" 65)
       rev :: "'a list \<Rightarrow> 'a list"

primrec
"[] @ ys       = ys"
"(x # xs) @ ys = x # (xs @ ys)"

primrec
"rev []        = []"
"rev (x # xs)  = (rev xs) @ (x # [])"

theorem rev_rev [simp]: "rev(rev xs) = xs"
(*<*)oops(*>*)text_raw{*\isanewline\isanewline*}

end
