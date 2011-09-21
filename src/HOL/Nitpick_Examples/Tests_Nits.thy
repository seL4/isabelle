(*  Title:      HOL/Nitpick_Examples/Tests_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Nitpick tests.
*)

header {* Nitpick Tests *}

theory Tests_Nits
imports Main
begin

ML {* () |> getenv "KODKODI" <> "" ? Nitpick_Tests.run_all_tests *}

end
