
theory FOL = IFOL
files ("FOL_lemmas1.ML") ("cladata.ML") ("blastdata.ML") ("simpdata.ML") ("FOL_lemmas2.ML"):

axioms
  classical: "(~P ==> P) ==> P"

use "FOL_lemmas1.ML"
use "cladata.ML"        setup Cla.setup setup clasetup
use "blastdata.ML"      setup Blast.setup
use "FOL_lemmas2.ML"
use "simpdata.ML"       setup simpsetup setup cong_attrib_setup
                        setup "Simplifier.method_setup Splitter.split_modifiers"
                        setup Splitter.setup setup Clasimp.setup

end
