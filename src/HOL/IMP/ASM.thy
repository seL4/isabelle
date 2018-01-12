section "Stack Machine and Compilation"

theory ASM imports AExp begin

subsection "Stack Machine"

text_raw\<open>\snip{ASMinstrdef}{0}{1}{%\<close>
datatype instr = LOADI val | LOAD vname | ADD
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{ASMstackdef}{1}{2}{%\<close>
type_synonym stack = "val list"
text_raw\<open>}%endsnip\<close>

text\<open>\noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist.\<close>

text_raw\<open>\snip{ASMexeconedef}{0}{1}{%\<close>
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk  =  n # stk" |
"exec1 (LOAD x) s stk  =  s(x) # stk" |
"exec1  ADD _ (j # i # stk)  =  (i + j) # stk"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{ASMexecdef}{1}{2}{%\<close>
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"
text_raw\<open>}%endsnip\<close>

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done


subsection "Compilation"

text_raw\<open>\snip{ASMcompdef}{0}{2}{%\<close>
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"
text_raw\<open>}%endsnip\<close>

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

end
