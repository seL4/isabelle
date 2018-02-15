(*  Title:      HOL/Auth/Guard/List_Msg.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section\<open>Lists of Messages and Lists of Agents\<close>

theory List_Msg imports Extensions begin

subsection\<open>Implementation of Lists by Messages\<close>

subsubsection\<open>nil is represented by any message which is not a pair\<close>

abbreviation (input)
  cons :: "msg => msg => msg" where
  "cons x l == \<lbrace>x,l\<rbrace>"

subsubsection\<open>induction principle\<close>

lemma lmsg_induct: "[| !!x. not_MPair x ==> P x; !!x l. P l ==> P (cons x l) |]
==> P l"
by (induct l) auto

subsubsection\<open>head\<close>

primrec head :: "msg => msg" where
"head (cons x l) = x"

subsubsection\<open>tail\<close>

primrec tail :: "msg => msg" where
"tail (cons x l) = l"

subsubsection\<open>length\<close>

fun len :: "msg => nat" where
"len (cons x l) = Suc (len l)" |
"len other = 0"

lemma len_not_empty: "n < len l \<Longrightarrow> \<exists>x l'. l = cons x l'"
by (cases l) auto

subsubsection\<open>membership\<close>

fun isin :: "msg * msg => bool" where
"isin (x, cons y l) = (x=y | isin (x,l))" |
"isin (x, other) = False"

subsubsection\<open>delete an element\<close>

fun del :: "msg * msg => msg" where
"del (x, cons y l) = (if x=y then l else cons y (del (x,l)))" |
"del (x, other) = other"

lemma notin_del [simp]: "~ isin (x,l) ==> del (x,l) = l"
by (induct l) auto

lemma isin_del [rule_format]: "isin (y, del (x,l)) --> isin (y,l)"
by (induct l) auto

subsubsection\<open>concatenation\<close>

fun app :: "msg * msg => msg" where
"app (cons x l, l') = cons x (app (l,l'))" |
"app (other, l') = l'"

lemma isin_app [iff]: "isin (x, app(l,l')) = (isin (x,l) | isin (x,l'))"
by (induct l) auto

subsubsection\<open>replacement\<close>

fun repl :: "msg * nat * msg => msg" where
"repl (cons x l, Suc i, x') = cons x (repl (l,i,x'))" |
"repl (cons x l, 0, x') = cons x' l" |
"repl (other, i, M') = other"

subsubsection\<open>ith element\<close>

fun ith :: "msg * nat => msg" where
"ith (cons x l, Suc i) = ith (l,i)" |
"ith (cons x l, 0) = x" |
"ith (other, i) = other"

lemma ith_head: "0 < len l ==> ith (l,0) = head l"
by (cases l) auto

subsubsection\<open>insertion\<close>

fun ins :: "msg * nat * msg => msg" where
"ins (cons x l, Suc i, y) = cons x (ins (l,i,y))" |
"ins (l, 0, y) = cons y l"

lemma ins_head [simp]: "ins (l,0,y) = cons y l"
by (cases l) auto

subsubsection\<open>truncation\<close>

fun trunc :: "msg * nat => msg" where
"trunc (l,0) = l" |
"trunc (cons x l, Suc i) = trunc (l,i)"

lemma trunc_zero [simp]: "trunc (l,0) = l"
by (cases l) auto


subsection\<open>Agent Lists\<close>

subsubsection\<open>set of well-formed agent-list messages\<close>

abbreviation
  nil :: msg where
  "nil == Number 0"

inductive_set agl :: "msg set"
where
  Nil[intro]: "nil \<in> agl"
| Cons[intro]: "[| A \<in> agent; I \<in> agl |] ==> cons (Agent A) I \<in> agl"

subsubsection\<open>basic facts about agent lists\<close>

lemma del_in_agl [intro]: "I \<in> agl \<Longrightarrow> del (a,I) \<in> agl"
by (erule agl.induct, auto)

lemma app_in_agl [intro]: "[| I \<in> agl; J \<in> agl |] ==> app (I,J) \<in> agl"
by (erule agl.induct, auto)

lemma no_Key_in_agl: "I \<in> agl \<Longrightarrow> Key K \<notin> parts {I}"
by (erule agl.induct, auto)

lemma no_Nonce_in_agl: "I \<in> agl \<Longrightarrow> Nonce n \<notin> parts {I}"
by (erule agl.induct, auto)

lemma no_Key_in_appdel: "[| I \<in> agl; J \<in> agl |] ==>
Key K \<notin> parts {app (J, del (Agent B, I))}"
by (rule no_Key_in_agl, auto)

lemma no_Nonce_in_appdel: "[| I \<in> agl; J \<in> agl |] ==>
Nonce n \<notin> parts {app (J, del (Agent B, I))}"
by (rule no_Nonce_in_agl, auto)

lemma no_Crypt_in_agl: "I \<in> agl \<Longrightarrow> Crypt K X \<notin> parts {I}"
by (erule agl.induct, auto)

lemma no_Crypt_in_appdel: "[| I \<in> agl; J \<in> agl |] ==>
Crypt K X \<notin> parts {app (J, del (Agent B,I))}"
by (rule no_Crypt_in_agl, auto)

end
