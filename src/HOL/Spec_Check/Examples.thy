theory Examples
imports Spec_Check
begin

section {* List examples *}

ML {*
check_property @{context} "ALL xs. rev xs = xs";
*}

ML {*
check_property @{context} "ALL xs. rev (rev xs) = xs";
*}


section {* AList Specification *}

ML {*
(* map_entry applies the function to the element *)
check_property @{context} "ALL k f xs. AList.lookup (op =) (AList.map_entry (op =) k f xs) k = Option.map f (AList.lookup (op =) xs k)";

(* update always results in an entry *)
check_property @{context} "ALL k v xs. AList.defined (op =) (AList.update (op =) (k, v) xs) k";

(* update always writes the value *)
check_property @{context} "ALL k v xs. AList.lookup (op =) (AList.update (op =) (k, v) xs) k = SOME v";

(* default always results in an entry *)
check_property @{context} "ALL k v xs. AList.defined (op =) (AList.default (op =) (k, v) xs) k";

(* delete always removes the entry *)
check_property @{context} "ALL k xs. not (AList.defined (op =) (AList.delete (op =) k xs) k)";

(* default writes the entry iff it didn't exist *)
check_property @{context} "ALL k v xs. (AList.lookup (op =) (AList.default (op =) (k, v) xs) k = (if AList.defined (op =) xs k then AList.lookup (op =) xs k else SOME v))";
*}

section {* Examples on Types and Terms *}

ML {*
check_property @{context} "ALL f g t. map_types (g o f) t = (map_types f o map_types g) t";
*}

ML {*
check_property @{context} "ALL f g t. map_types (f o g) t = (map_types f o map_types g) t";
*}

text {* One would think this holds: *}

ML {*
check_property @{context} "ALL t ts. strip_comb (list_comb (t, ts)) = (t, ts)"
*}

text {* But it only holds with this precondition: *}

ML {*
check_property @{context} "ALL t ts. case t of _ $ _ => true | _ => strip_comb (list_comb (t, ts)) = (t, ts)"
*}

section {* Some surprises *}

ML {*
check_property @{context} "ALL Ts t. type_of1 (Ts, t) = fastype_of1 (Ts, t)"
*}



ML {* val thy = @{theory}; *}
ML {*
  check_property @{context} "ALL t u. if Pattern.matches thy (t, u) then Term.could_unify (t, u) else true"
*}

end
