(*  Title: 	ZF/AC/AC16_WO4.thy
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski
*)

AC16_WO4 = OrderType + AC16_lemmas + Cardinal_aux +

consts

  ww  :: "[i, i] => i"
  s_u :: "[i, i, i, i] => i"
  MM  :: "[i, i, i] => i"
  LL  :: "[i, i, i] => i"
  GG  :: "[i, i, i] => i"
  
defs

  ww_def  "ww(x, k) == {u:Pow(x). u eqpoll k}"

  s_u_def "s_u(u, t_n, k, y) == {v:t_n. u:v & k lepoll v Int y}"

  MM_def  "MM(t_n, k, y) == {v:t_n. k lepoll v Int y}"

  LL_def  "LL(t_n, k, y) == {v Int y. v:MM(t_n, k, y)}"

  GG_def  "GG(t_n, k, y) == lam v:LL(t_n, k, y). 
	                    (THE w. w:MM(t_n, k, y) & v <= w) - v"

end
