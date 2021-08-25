theory Examples
imports Spec_Check
begin

section \<open>List examples\<close>

ML_command \<open>
check_property "ALL xs. rev xs = xs";
\<close>

ML_command \<open>
check_property "ALL xs. rev (rev xs) = xs";
\<close>


section \<open>AList Specification\<close>

ML_command \<open>
(* map_entry applies the function to the element *)
check_property "ALL k f xs. AList.lookup (op =) (AList.map_entry (op =) k f xs) k = Option.map f (AList.lookup (op =) xs k)";
\<close>

ML_command \<open>
(* update always results in an entry *)
check_property "ALL k v xs. AList.defined (op =) (AList.update (op =) (k, v) xs) k";
\<close>

ML_command \<open>
(* update always writes the value *)
check_property "ALL k v xs. AList.lookup (op =) (AList.update (op =) (k, v) xs) k = SOME v";
\<close>

ML_command \<open>
(* default always results in an entry *)
check_property "ALL k v xs. AList.defined (op =) (AList.default (op =) (k, v) xs) k";
\<close>

ML_command \<open>
(* delete always removes the entry *)
check_property "ALL k xs. not (AList.defined (op =) (AList.delete (op =) k xs) k)";
\<close>

ML_command \<open>
(* default writes the entry iff it didn't exist *)
check_property "ALL k v xs. (AList.lookup (op =) (AList.default (op =) (k, v) xs) k = (if AList.defined (op =) xs k then AList.lookup (op =) xs k else SOME v))";
\<close>

section \<open>Examples on Types and Terms\<close>

ML_command \<open>
check_property "ALL f g t. map_types (g o f) t = (map_types f o map_types g) t";
\<close>

ML_command \<open>
check_property "ALL f g t. map_types (f o g) t = (map_types f o map_types g) t";
\<close>


text \<open>One would think this holds:\<close>

ML_command \<open>
check_property "ALL t ts. strip_comb (list_comb (t, ts)) = (t, ts)"
\<close>

text \<open>But it only holds with this precondition:\<close>

ML_command \<open>
check_property "ALL t ts. case t of _ $ _ => true | _ => strip_comb (list_comb (t, ts)) = (t, ts)"
\<close>

section \<open>Some surprises\<close>

ML_command \<open>
check_property "ALL Ts t. type_of1 (Ts, t) = fastype_of1 (Ts, t)"
\<close>


ML_command \<open>
val thy = \<^theory>;
check_property "ALL t u. if Pattern.matches thy (t, u) then Term.could_unify (t, u) else true"
\<close>

end
