(*  Title:      HOL/Real/ex/BinEx.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Examples of performing binary arithmetic by simplification
This time we use the reals, though the representation is just of integers.
*)

(*** Addition ***)

Goal "(#1359::real)  +  #-2468 = #-1109";
by (Simp_tac 1);
result();

Goal "(#93746::real) +  #-46375 = #47371";
by (Simp_tac 1);
result();

(*** Negation ***)

Goal "- (#65745::real) = #-65745";
by (Simp_tac 1);
result();

Goal "- (#-54321::real) = #54321";
by (Simp_tac 1);
result();


(*** Multiplication ***)

Goal "(#-84::real)  *  #51 = #-4284";
by (Simp_tac 1);
result();

Goal "(#255::real)  *  #255 = #65025";
by (Simp_tac 1);
result();

Goal "(#1359::real)  *  #-2468 = #-3354012";
by (Simp_tac 1);
result();

(*** Inequalities ***)

Goal "(#89::real) * #10 ~= #889";  
by (Simp_tac 1); 
result();

Goal "(#13::real) < #18 - #4";  
by (Simp_tac 1); 
result();

Goal "(#-345::real) < #-242 + #-100";  
by (Simp_tac 1); 
result();

Goal "(#13557456::real) < #18678654";  
by (Simp_tac 1); 
result();

Goal "(#999999::real) <= (#1000001 + #1)-#2";  
by (Simp_tac 1); 
result();

Goal "(#1234567::real) <= #1234567";  
by (Simp_tac 1); 
result();
