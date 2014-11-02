(*  Title:      HOL/Auth/Guard/List_Msg.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section{*Lists of Messages and Lists of Agents*}

theory List_Msg imports Extensions begin

subsection{*Implementation of Lists by Messages*}

subsubsection{*nil is represented by any message which is not a pair*}

abbreviation (input)
  cons :: "msg => msg => msg" where
  "cons x l == {|x,l|}"

subsubsection{*induction principle*}

lemma lmsg_induct: "[| !!x. not_MPair x ==> P x; !!x l. P l ==> P (cons x l) |]
==> P l"
by (induct l) auto

subsubsection{*head*}

primrec head :: "msg => msg" where
"head (cons x l) = x"

subsubsection{*tail*}

primrec tail :: "msg => msg" where
"tail (cons x l) = l"

subsubsection{*length*}

fun len :: "msg => nat" where
"len (cons x l) = Suc (len l)" |
"len other = 0"

lemma len_not_empty: "n < len l ==> EX x l'. l = cons x l'"
by (cases l) auto

subsubsection{*membership*}

fun isin :: "msg * msg => bool" where
"isin (x, cons y l) = (x=y | isin (x,l))" |
"isin (x, other) = False"

subsubsection{*delete an element*}

fun del :: "msg * msg => msg" where
"del (x, cons y l) = (if x=y then l else cons y (del (x,l)))" |
"del (x, other) = other"

lemma notin_del [simp]: "~ isin (x,l) ==> del (x,l) = l"
by (induct l) auto

lemma isin_del [rule_format]: "isin (y, del (x,l)) --> isin (y,l)"
by (induct l) auto

subsubsection{*concatenation*}

fun app :: "msg * msg => msg" where
"app (cons x l, l') = cons x (app (l,l'))" |
"app (other, l') = l'"

lemma isin_app [iff]: "isin (x, app(l,l')) = (isin (x,l) | isin (x,l'))"
by (induct l) auto

subsubsection{*replacement*}

fun repl :: "msg * nat * msg => msg" where
"repl (cons x l, Suc i, x') = cons x (repl (l,i,x'))" |
"repl (cons x l, 0, x') = cons x' l" |
"repl (other, i, M') = other"

subsubsection{*ith element*}

fun ith :: "msg * nat => msg" where
"ith (cons x l, Suc i) = ith (l,i)" |
"ith (cons x l, 0) = x" |
"ith (other, i) = other"

lemma ith_head: "0 < len l ==> ith (l,0) = head l"
by (cases l) auto

subsubsection{*insertion*}

fun ins :: "msg * nat * msg => msg" where
"ins (cons x l, Suc i, y) = cons x (ins (l,i,y))" |
"ins (l, 0, y) = cons y l"

lemma ins_head [simp]: "ins (l,0,y) = cons y l"
by (cases l) auto

subsubsection{*truncation*}

fun trunc :: "msg * nat => msg" where
"trunc (l,0) = l" |
"trunc (cons x l, Suc i) = trunc (l,i)"

lemma trunc_zero [simp]: "trunc (l,0) = l"
by (cases l) auto


subsection{*Agent Lists*}

subsubsection{*set of well-formed agent-list messages*}

abbreviation
  nil :: msg where
  "nil == Number 0"

inductive_set agl :: "msg set"
where
  Nil[intro]: "nil:agl"
| Cons[intro]: "[| A:agent; I:agl |] ==> cons (Agent A) I :agl"

subsubsection{*basic facts about agent lists*}

lemma del_in_agl [intro]: "I:agl ==> del (a,I):agl"
by (erule agl.induct, auto)

lemma app_in_agl [intro]: "[| I:agl; J:agl |] ==> app (I,J):agl"
by (erule agl.induct, auto)

lemma no_Key_in_agl: "I:agl ==> Key K ~:parts {I}"
by (erule agl.induct, auto)

lemma no_Nonce_in_agl: "I:agl ==> Nonce n ~:parts {I}"
by (erule agl.induct, auto)

lemma no_Key_in_appdel: "[| I:agl; J:agl |] ==>
Key K ~:parts {app (J, del (Agent B, I))}"
by (rule no_Key_in_agl, auto)

lemma no_Nonce_in_appdel: "[| I:agl; J:agl |] ==>
Nonce n ~:parts {app (J, del (Agent B, I))}"
by (rule no_Nonce_in_agl, auto)

lemma no_Crypt_in_agl: "I:agl ==> Crypt K X ~:parts {I}"
by (erule agl.induct, auto)

lemma no_Crypt_in_appdel: "[| I:agl; J:agl |] ==>
Crypt K X ~:parts {app (J, del (Agent B,I))}"
by (rule no_Crypt_in_agl, auto)

end
