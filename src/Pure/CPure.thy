(*  Title:      Pure/CPure.thy
    ID:         $Id$

The CPure theory -- Pure with alternative application syntax.
*)

theory CPure
imports Pure
begin

setup {*
  Theory.del_modesyntax Syntax.default_mode Syntax.appl_syntax #>
  Theory.add_syntax Syntax.applC_syntax
*}

end
