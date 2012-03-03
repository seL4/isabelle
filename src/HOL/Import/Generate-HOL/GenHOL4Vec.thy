(*  Title:      HOL/Import/Generate-HOL/GenHOL4Vec.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Vec imports GenHOL4Base begin

import_segment "hol4";

setup_dump "../HOL" "HOL4Vec";

append_dump "theory HOL4Vec imports HOL4Base begin";

import_theory "~~/src/HOL/Import/HOL" res_quan;
end_import;

import_theory "~~/src/HOL/Import/HOL" word_base;

const_renames
  BIT > bit;

end_import;

import_theory "~~/src/HOL/Import/HOL" word_num;
end_import;

import_theory "~~/src/HOL/Import/HOL" word_bitop;
end_import;

import_theory "~~/src/HOL/Import/HOL" bword_num;
end_import;

import_theory "~~/src/HOL/Import/HOL" bword_arith;
end_import;

import_theory "~~/src/HOL/Import/HOL" bword_bitop;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
