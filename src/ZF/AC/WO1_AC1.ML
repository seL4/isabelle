(*  Title: 	ZF/AC/WO1_AC1.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

The proof of WO1 ==> AC1
*)

open WO1_AC1;

goalw thy [AC1_def, WO1_def] "!!Z. WO1 ==> AC1";
by (fast_tac (AC_cs addSEs [ex_choice_fun]) 1);
result();