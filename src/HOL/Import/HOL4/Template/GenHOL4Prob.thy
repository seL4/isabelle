(*  Title:      HOL/Import/HOL4/Template/GenHOL4Prob.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Prob
imports GenHOL4Real
begin

import_segment "hol4"

setup_dump "../Generated" "HOL4Prob"

append_dump {*theory HOL4Prob
imports HOL4Real
begin
*}

import_theory "~~/src/HOL/Import/HOL4/Generated" prob_extra;

const_moves
  COMPL > GenHOL4Base.pred_set.COMPL;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prob_canon;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" boolean_sequence;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prob_algebra;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prob;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prob_pseudo;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prob_indep;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prob_uniform;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
