
(*** Examples of performing binary arithmetic by simplification ***)

(** Addition **)

Goal "#13  +  #19 = #32";
by (Simp_tac 1);
result();

Goal "#1234  +  #5678 = #6912";
by (Simp_tac 1);
result();

Goal "#1359  +  #-2468 = #-1109";
by (Simp_tac 1);
result();

Goal "#93746 +  #-46375 = #47371";
by (Simp_tac 1);
result();

(** Negation **)

Goal "- #65745 = #-65745";
by (Simp_tac 1);
result();

Goal "- #-54321 = #54321";
by (Simp_tac 1);
result();


(** Multiplication **)

Goal "#13  *  #19 = #247";
by (Simp_tac 1);
result();

Goal "#-84  *  #51 = #-4284";
by (Simp_tac 1);
result();

Goal "#255  *  #255 = #65025";
by (Simp_tac 1);
result();

Goal "#1359  *  #-2468 = #-3354012";
by (Simp_tac 1);
result();

Goal "#89 * #10 ~= #889";  
by (Simp_tac 1); 
result();

Goal "#13 < #18 - #4";  
by (Simp_tac 1); 
result();

Goal "#-345 < #-242 + #-100";  
by (Simp_tac 1); 
result();

Goal "#13557456 < #18678654";  
by (Simp_tac 1); 
result();

Goal "#999999 <= (#1000001 + #1)-#2";  
by (Simp_tac 1); 
result();

Goal "#1234567 <= #1234567";  
by (Simp_tac 1); 
result();
