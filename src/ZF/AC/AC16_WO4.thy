(*  Title:      ZF/AC/AC16_WO4.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Tidied using locales by LCP
*)

AC16_WO4 = OrderType + AC16_lemmas + Cardinal_aux +

locale AC16 =
  fixes 
    x	:: i
    y	:: i
    k	:: i
    l   :: i
    m	:: i
    t_n	:: i
    R	:: i
    MM  :: i
    LL  :: i
    GG  :: i
    s   :: i=>i
  assumes
    all_ex    "\\<forall>z \\<in> {z \\<in> Pow(x Un y) . z eqpoll succ(k)}.
	         \\<exists>! w. w \\<in> t_n & z \\<subseteq> w "
    disjoint  "x Int y = 0"
    includes  "t_n \\<subseteq> {v \\<in> Pow(x Un y). v eqpoll succ(k #+ m)}"
    WO_R      "well_ord(y,R)"
    lnat      "l \\<in> nat"
    mnat      "m \\<in> nat"
    mpos      "0<m"
    Infinite  "~ Finite(y)"
    noLepoll  "~ y lepoll {v \\<in> Pow(x). v eqpoll m}"
  defines
    k_def     "k   == succ(l)"
    MM_def    "MM  == {v \\<in> t_n. succ(k) lepoll v Int y}"
    LL_def    "LL  == {v Int y. v \\<in> MM}"
    GG_def    "GG  == \\<lambda>v \\<in> LL. (THE w. w \\<in> MM & v \\<subseteq> w) - v"
    s_def     "s(u) == {v \\<in> t_n. u \\<in> v & k lepoll v Int y}"

end
