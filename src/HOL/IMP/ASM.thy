header "Arithmetic Stack Machine and Compilation"

theory ASM imports AExp begin

subsection "Arithmetic Stack Machine"

datatype ainstr = LOADI val | LOAD string | ADD

type_synonym stack = "val list"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

text{* \noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist. *}

fun aexec1 :: "ainstr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"aexec1 (LOADI n) _ stk  =  n # stk" |
"aexec1 (LOAD n) s stk  =  s(n) # stk" |
"aexec1  ADD _ stk  =  (hd2 stk + hd stk) # tl2 stk"

fun aexec :: "ainstr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"aexec [] _ stk = stk" |
"aexec (i#is) s stk = aexec is s (aexec1 i s stk)"

value "aexec [LOADI 5, LOAD ''y'', ADD]
 <''x'' := 42, ''y'' := 43> [50]"

lemma aexec_append[simp]:
  "aexec (is1@is2) s stk = aexec is2 s (aexec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done


subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> ainstr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus e1 e2) = acomp e1 @ acomp e2 @ [ADD]"

value "acomp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem aexec_acomp[simp]: "aexec (acomp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

end
