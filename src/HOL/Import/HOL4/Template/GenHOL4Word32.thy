(*  Title:      HOL/Import/HOL4/Template/GenHOL4Word32.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Word32
imports GenHOL4Base
begin

import_segment "hol4"

setup_dump "../Generated" "HOL4Word32"

append_dump {*theory HOL4Word32
imports HOL4Base
begin
*}

import_theory "~~/src/HOL/Import/HOL4/Generated" bits;

const_renames
  BIT > bit

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" word32;

const_renames
  "==" > EQUIV;

end_import;

append_dump "end";

flush_dump;

import_segment "";

end
