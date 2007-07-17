(*  Title:      Pure/pure_setup.ML
    ID:         $Id$
    Author:     Makarius

Pure theory setup.
*)

use_thy "Pure";
structure Pure = struct val thy = theory "Pure" end;

Context.add_setup
 (Sign.del_modesyntax Syntax.default_mode Syntax.appl_syntax #>
  Sign.add_syntax Syntax.applC_syntax);
use_thy "CPure";
structure CPure = struct val thy = theory "CPure" end;

use "install_pp.ML";
val use = ThyInfo.use;
val cd = File.cd o Path.explode;
ml_prompts "ML> " "ML# ";

proofs := 0;
