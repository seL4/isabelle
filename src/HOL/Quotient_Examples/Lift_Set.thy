(*  Title:      HOL/Quotient_Examples/Lift_Set.thy
    Author:     Lukas Bulwahn and Ondrey Kuncar
*)

header {* Example of lifting definitions with the quotient infrastructure *}

theory Lift_Set
imports Main
begin

typedef 'a set = "(UNIV :: ('a => bool) => bool)"
morphisms member Set by auto

text {* Here is some ML setup that should eventually be incorporated in the typedef command. *}

local_setup {* fn lthy =>
let
  val quotients = {qtyp = @{typ "'a set"}, rtyp = @{typ "'a => bool"}, equiv_rel = @{term "dummy"}, equiv_thm = @{thm refl}}
  val qty_full_name = @{type_name "set"}

  fun qinfo phi = Quotient_Info.transform_quotients phi quotients
  in lthy
    |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Quotient_Info.update_quotients qty_full_name (qinfo phi)
       #> Quotient_Info.update_abs_rep qty_full_name (Quotient_Info.transform_abs_rep phi {abs = @{term "Set"}, rep = @{term "member"}}))
  end
*}

text {* Now, we can employ quotient_definition to lift definitions. *}

quotient_definition empty where "empty :: 'a set"
is "Set.empty"

term "Lift_Set.empty"
thm Lift_Set.empty_def

quotient_definition insert where "insert :: 'a => 'a set => 'a set"
is "Set.insert"

term "Lift_Set.insert"
thm Lift_Set.insert_def

end
