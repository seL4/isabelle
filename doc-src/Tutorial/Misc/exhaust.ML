Goal "(case xs of [] => [] | y#ys => xs) = xs";
by(exhaust_tac "xs" 1);
