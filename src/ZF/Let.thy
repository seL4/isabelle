(*  Title: 	ZF/Let
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Let expressions -- borrowed from HOL
*)

Let = ZF +

types
  letbinds  letbind

consts
  Let           :: "['a, 'a => 'b] => 'b"

syntax
  "_bind"       :: "[idt, 'a] => letbind"             ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"              ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"  ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"             ("(let (_)/ in (_))" 10)

translations
  "_Let(_binds(b, bs), e)"  == "_Let(b, _Let(bs, e))"
  "let x = a in e"          == "Let(a, %x. e)"

defs
  Let_def       "Let(s, f) == f(s)"

end
