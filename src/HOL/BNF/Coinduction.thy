(*  Title:      HOL/BNF/Coinduction.thy
    Author:     Johannes Hölzl, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Coinduction method that avoids some boilerplate compared to coinduct.
*)

header {* Coinduction Method *}

theory Coinduction
imports BNF_Util
begin

ML_file "Tools/coinduction.ML"

setup Coinduction.setup

end
