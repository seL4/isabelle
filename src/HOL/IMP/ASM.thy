header "Stack Machine and Compilation"

theory ASM imports AExp begin

subsection "Stack Machine"

text_raw{*\begin{isaverbatimwrite}\newcommand{\ASMinstrdef}{% *}
datatype instr = LOADI val | LOAD vname | ADD
text_raw{*}\end{isaverbatimwrite}*}

text_raw{*\begin{isaverbatimwrite}\newcommand{\ASMstackdef}{% *}
type_synonym stack = "val list"
text_raw{*}\end{isaverbatimwrite}*}

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

text{* \noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist. *}

text_raw{*\begin{isaverbatimwrite}\newcommand{\ASMexeconedef}{% *}
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk  =  n # stk" |
"exec1 (LOAD x) s stk  =  s(x) # stk" |
"exec1  ADD _ stk  =  (hd2 stk + hd stk) # tl2 stk"
text_raw{*}\end{isaverbatimwrite}*}

text_raw{*\begin{isaverbatimwrite}\newcommand{\ASMexecdef}{% *}
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"
text_raw{*}\end{isaverbatimwrite}*}

value "exec [LOADI 5, LOAD ''y'', ADD]
 <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done


subsection "Compilation"

text_raw{*\begin{isaverbatimwrite}\newcommand{\ASMcompdef}{% *}
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"
text_raw{*}\end{isaverbatimwrite}*}

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

end
