(*  Title:      ZF/AC/AC16_WO4.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski


(*for all_in_lepoll_m and OUN_eq_x*)
*)

AC16_WO4 = OrderType + AC16_lemmas + Cardinal_aux +

consts

  s_u :: [i, i, i, i] => i
  
defs

  s_u_def "s_u(u, t_n, k, y) == {v:t_n. u:v & k lepoll v Int y}"




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
  assumes
    all_ex    "ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}.
	         EX! w. w:t_n & z <= w "
    disjoint  "x Int y = 0"
    includes  "t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)}"
    WO_R      "well_ord(y,R)"
    knat      "k:nat"
    kpos      "k = succ(l)"
    lnat      "l:nat"
    mnat      "m:nat"
    mpos      "0<m"
    Infinite  "~ Finite(y)"
    noLepoll  "~ y lepoll {v:Pow(x). v eqpoll m}"
  defines
    MM_def    "MM == {v:t_n. succ(k) lepoll v Int y}"
    LL_def    "LL == {v Int y. v:MM}"
    GG_def    "GG == lam v:LL. (THE w. w:MM & v <= w) - v"

end
