theory GenHOL4Vec = GenHOL4Base:

import_segment "hol4";

setup_dump "../HOL" "HOL4Vec";

append_dump "theory HOL4Vec = HOL4Base:";

import_theory res_quan;
end_import;

import_theory word_base;

const_renames
  BIT > bit;

end_import;

import_theory word_num;
end_import;

import_theory word_bitop;
end_import;

import_theory bword_num;
end_import;

import_theory bword_arith;
end_import;

import_theory bword_bitop;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
