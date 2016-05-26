(*  Title:      HOL/Nitpick_Examples/Tests_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Nitpick tests.
*)

section \<open>Nitpick Tests\<close>

theory Tests_Nits
imports Main
begin

ML \<open>() |> getenv "KODKODI" <> "" ? Nitpick_Tests.run_all_tests\<close>

end
