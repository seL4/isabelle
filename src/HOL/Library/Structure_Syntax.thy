(* Author: Florian Haftmann, TU Muenchen *)

header {* Index syntax for structures *}

theory Structure_Syntax
imports Pure
begin

syntax
  "_index1"  :: index    ("\<^sub>1")
translations
  (index) "\<^sub>1" => (index) "\<^bsub>\<struct>\<^esub>"

end
