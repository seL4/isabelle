(*  Title:      HOL/ex/Exceptions.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2004 TU Muenchen
*)

header {* Compiling exception handling *}

theory Exceptions = List_Prefix:

text{* This is a formalization of \cite{HuttonW04}. *}

subsection{*The source language*}

datatype expr = Val int | Add expr expr | Throw | Catch expr expr

consts eval :: "expr \<Rightarrow> int option"
primrec
"eval (Val i) = Some i"
"eval (Add x y) =
 (case eval x of None \<Rightarrow> None
  | Some i \<Rightarrow> (case eval y of None \<Rightarrow> None
               | Some j \<Rightarrow> Some(i+j)))"
"eval Throw = None"
"eval (Catch x h) = (case eval x of None \<Rightarrow> eval h | Some i \<Rightarrow> Some i)"

subsection{*The target language*}

datatype instr =
  Push int | ADD | THROW | Mark nat | Unmark | Label nat | Jump nat

datatype item = VAL int | HAN nat

types code = "instr list"
      stack = "item list"

consts
  exec2 :: "bool * code * stack \<Rightarrow> stack"
  jump :: "nat * code \<Rightarrow> code"

recdef jump "measure(%(l,cs). size cs)"
"jump(l,[]) = []"
"jump(l, Label l' # cs) = (if l = l' then cs else jump(l,cs))"
"jump(l, c # cs) = jump(l,cs)"

lemma size_jump1: "size (jump (l, cs)) < Suc(size cs)"
apply(induct cs)
 apply simp
apply(case_tac a)
apply auto
done

lemma size_jump2: "size (jump (l, cs)) < size cs \<or> jump(l,cs) = cs"
apply(induct cs)
 apply simp
apply(case_tac a)
apply auto
done

syntax
  exec   :: "code \<Rightarrow> stack \<Rightarrow> stack"
  unwind :: "code \<Rightarrow> stack \<Rightarrow> stack"
translations
  "exec cs s" == "exec2(True,cs,s)"
  "unwind cs s" == "exec2(False,cs,s)"

recdef exec2
 "inv_image (measure(%cs. size cs) <*lex*> measure(%s. size s))
            (%(b,cs,s). (cs,s))"
"exec [] s = s"
"exec (Push i#cs) s = exec cs (VAL i # s)"
"exec (ADD#cs) (VAL j # VAL i # s) = exec cs (VAL(i+j) # s)"
"exec (THROW#cs) s = unwind cs s"
"exec (Mark l#cs) s = exec cs (HAN l # s)"
"exec (Unmark#cs) (v # HAN l # s) = exec cs (v # s)"
"exec (Label l#cs) s = exec cs s"
"exec (Jump l#cs) s = exec (jump(l,cs)) s"

"unwind cs [] = []"
"unwind cs (VAL i # s) = unwind cs s"
"unwind cs (HAN l # s) = exec (jump(l,cs)) s"

(hints recdef_simp: size_jump1 size_jump2)

subsection{*The compiler*}

consts
  compile :: "nat \<Rightarrow> expr \<Rightarrow> code * nat"
primrec
"compile l (Val i) = ([Push i], l)"
"compile l (Add x y) = (let (xs,m) = compile l x; (ys,n) = compile m y
                     in (xs @ ys @ [ADD], n))"
"compile l Throw = ([THROW],l)"
"compile l (Catch x h) =
  (let (xs,m) = compile (l+2) x; (hs,n) = compile m h
   in (Mark l # xs @ [Unmark, Jump (l+1), Label l] @ hs @ [Label(l+1)], n))"

syntax cmp :: "nat \<Rightarrow> expr \<Rightarrow> code"
translations "cmp l e" == "fst(compile l e)"

consts
  isFresh :: "nat \<Rightarrow> stack \<Rightarrow> bool"
primrec
"isFresh l [] = True"
"isFresh l (it#s) = (case it of VAL i \<Rightarrow> isFresh l s
                     | HAN l' \<Rightarrow> l' < l \<and> isFresh l s)"

constdefs
  conv :: "code \<Rightarrow> stack \<Rightarrow> int option \<Rightarrow> stack"
 "conv cs s io == case io of None \<Rightarrow> unwind cs s
                  | Some i \<Rightarrow> exec cs (VAL i # s)"

subsection{* The proofs*}

declare
  conv_def[simp] option.splits[split] Let_def[simp]

lemma 3:
  "(\<And>l. c = Label l \<Longrightarrow> isFresh l s) \<Longrightarrow> unwind (c#cs) s = unwind cs s"
apply(induct s)
 apply simp
apply(auto)
apply(case_tac a)
apply auto
apply(case_tac c)
apply auto
done

corollary [simp]:
  "(!!l. c \<noteq> Label l) \<Longrightarrow> unwind (c#cs) s = unwind cs s"
by(blast intro: 3)

corollary [simp]:
  "isFresh l s \<Longrightarrow> unwind (Label l#cs) s = unwind cs s"
by(blast intro: 3)


lemma 5: "\<lbrakk> isFresh l s; l \<le> m \<rbrakk> \<Longrightarrow> isFresh m s"
apply(induct s)
 apply simp
apply(auto split:item.split)
done

corollary [simp]: "isFresh l s \<Longrightarrow> isFresh (Suc l) s"
by(auto intro:5)


lemma 6: "\<And>l. l \<le> snd(compile l e)"
proof(induct e)
  case Val thus ?case by simp
next
  case (Add x y)
  have "l \<le> snd (compile l x)"
   and "snd (compile l x) \<le> snd (compile (snd (compile l x)) y)" .
  thus ?case by(simp_all add:split_def)
next
  case Throw thus ?case by simp
next
  case (Catch x h)
  have "l+2 \<le> snd (compile (l+2) x)"
   and "snd (compile (l+2) x) \<le> snd (compile (snd (compile (l+2) x)) h)" .
  thus ?case by(simp_all add:split_def)
qed

corollary [simp]: "l < m \<Longrightarrow> l < snd(compile m e)"
using 6[where l = m and e = e] by auto

corollary [simp]: "isFresh l s \<Longrightarrow> isFresh (snd(compile l e)) s"
using 5 6 by blast


text{* Contrary to the order of the lemmas in the paper, lemma 4 needs the
above corollary of 5 and 6. *}

lemma 4 [simp]: "\<And>l cs. isFresh l s \<Longrightarrow> unwind (cmp l e @ cs) s = unwind cs s"
by (induct e) (auto simp add:split_def)


lemma 7[simp]: "\<And>m cs. l < m \<Longrightarrow> jump(l, cmp m e @ cs) = jump(l, cs)"
by (induct e) (simp_all add:split_def)

text{* The compiler correctness theorem: *}

theorem "\<And>l s cs. isFresh l s \<Longrightarrow> exec (cmp l e @ cs) s = conv cs s (eval e)"
by(induct e)(auto simp add:split_def)

end
