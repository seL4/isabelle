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
    all_ex    "ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}.
	         EX! w. w:t_n & z <= w "
    disjoint  "x Int y = 0"
    includes  "t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)}"
    WO_R      "well_ord(y,R)"
    lnat      "l:nat"
    mnat      "m:nat"
    mpos      "0<m"
    Infinite  "~ Finite(y)"
    noLepoll  "~ y lepoll {v:Pow(x). v eqpoll m}"
  defines
    k_def     "k   == succ(l)"
    MM_def    "MM  == {v:t_n. succ(k) lepoll v Int y}"
    LL_def    "LL  == {v Int y. v:MM}"
    GG_def    "GG  == lam v:LL. (THE w. w:MM & v <= w) - v"
    s_def     "s(u) == {v:t_n. u:v & k lepoll v Int y}"

end
