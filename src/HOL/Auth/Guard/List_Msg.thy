(******************************************************************************
date: november 2001
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

header{*Lists of Messages and Lists of Agents*}

theory List_Msg = Extensions:

subsection{*Implementation of Lists by Messages*}

subsubsection{*nil is represented by any message which is not a pair*}

syntax cons :: "msg => msg => msg"

translations "cons x l" => "{|x,l|}"

subsubsection{*induction principle*}

lemma lmsg_induct: "[| !!x. not_MPair x ==> P x; !!x l. P l ==> P (cons x l) |]
==> P l"
by (induct l, auto)

subsubsection{*head*}

consts head :: "msg => msg"

recdef head "measure size"
"head (cons x l) = x"

subsubsection{*tail*}

consts tail :: "msg => msg"

recdef tail "measure size"
"tail (cons x l) = l"

subsubsection{*length*}

consts len :: "msg => nat"

recdef len "measure size"
"len (cons x l) = Suc (len l)"
"len other = 0"

lemma len_not_empty: "n < len l ==> EX x l'. l = cons x l'"
by (cases l, auto)

subsubsection{*membership*}

consts isin :: "msg * msg => bool"

recdef isin "measure (%(x,l). size l)"
"isin (x, cons y l) = (x=y | isin (x,l))"
"isin (x, other) = False"

subsubsection{*delete an element*}

consts del :: "msg * msg => msg"

recdef del "measure (%(x,l). size l)"
"del (x, cons y l) = (if x=y then l else cons y (del (x,l)))"
"del (x, other) = other"

lemma notin_del [simp]: "~ isin (x,l) ==> del (x,l) = l"
by (induct l, auto)

lemma isin_del [rule_format]: "isin (y, del (x,l)) --> isin (y,l)"
by (induct l, auto)

subsubsection{*concatenation*}

consts app :: "msg * msg => msg"

recdef app "measure (%(l,l'). size l)"
"app (cons x l, l') = cons x (app (l,l'))"
"app (other, l') = l'"

lemma isin_app [iff]: "isin (x, app(l,l')) = (isin (x,l) | isin (x,l'))"
by (induct l, auto)

subsubsection{*replacement*}

consts repl :: "msg * nat * msg => msg"

recdef repl "measure (%(l,i,x'). i)"
"repl (cons x l, Suc i, x') = cons x (repl (l,i,x'))"
"repl (cons x l, 0, x') = cons x' l"
"repl (other, i, M') = other"

subsubsection{*ith element*}

consts ith :: "msg * nat => msg"

recdef ith "measure (%(l,i). i)"
"ith (cons x l, Suc i) = ith (l,i)"
"ith (cons x l, 0) = x"
"ith (other, i) = other"

lemma ith_head: "0 < len l ==> ith (l,0) = head l"
by (cases l, auto)

subsubsection{*insertion*}

consts ins :: "msg * nat * msg => msg"

recdef ins "measure (%(l,i,x). i)"
"ins (cons x l, Suc i, y) = cons x (ins (l,i,y))"
"ins (l, 0, y) = cons y l"

lemma ins_head [simp]: "ins (l,0,y) = cons y l"
by (cases l, auto)

subsubsection{*truncation*}

consts trunc :: "msg * nat => msg"

recdef trunc "measure (%(l,i). i)"
"trunc (l,0) = l"
"trunc (cons x l, Suc i) = trunc (l,i)"

lemma trunc_zero [simp]: "trunc (l,0) = l"
by (cases l, auto)


subsection{*Agent Lists*}

subsubsection{*set of well-formed agent-list messages*}

syntax nil :: msg

translations "nil" == "Number 0"

consts agl :: "msg set"

inductive agl
intros
Nil[intro]: "nil:agl"
Cons[intro]: "[| A:agent; I:agl |] ==> cons (Agent A) I :agl"

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
