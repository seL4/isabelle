(*  Title:      Integ/Int.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order
*)

theory Int = IntDef
files ("int.ML"):

instance int :: order
proof qed (assumption | rule zle_refl zle_trans zle_anti_sym int_less_le)+

instance int :: plus_ac0
proof qed (rule zadd_commute zadd_assoc zadd_0)+

instance int :: linorder
proof qed (rule zle_linear)

constdefs
 nat  :: "int => nat"
"nat(Z) == if neg Z then 0 else (THE m. Z = int m)"

defs (overloaded)
zabs_def:  "abs(i::int) == if i < 0 then -i else i"

use "int.ML"

end
