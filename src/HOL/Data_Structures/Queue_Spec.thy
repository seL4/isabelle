(* Author: Tobias Nipkow *)

section \<open>Queue Specification\<close>

theory Queue_Spec
imports Main
begin

text \<open>The basic queue interface with \<open>list\<close>-based specification:\<close>

locale Queue =
fixes empty :: "'q"
fixes enq :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes front :: "'q \<Rightarrow> 'a"
fixes deq :: "'q \<Rightarrow> 'q"
fixes is_empty :: "'q \<Rightarrow> bool"
fixes list :: "'q \<Rightarrow> 'a list"
fixes invar :: "'q \<Rightarrow> bool"
assumes list_empty:    "list empty = []"
assumes list_enq:      "invar q \<Longrightarrow> list(enq x q) = list q @ [x]"
assumes list_deq:      "invar q \<Longrightarrow> list(deq q) = tl(list q)"
assumes list_front:    "invar q \<Longrightarrow> \<not> list q = [] \<Longrightarrow> front q = hd(list q)"
assumes list_is_empty: "invar q \<Longrightarrow> is_empty q = (list q = [])"
assumes invar_empty:   "invar empty"
assumes invar_enq:     "invar q \<Longrightarrow> invar(enq x q)"
assumes invar_deq:     "invar q \<Longrightarrow> invar(deq q)"

end
