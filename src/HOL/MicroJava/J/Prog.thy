(*  Title:      HOL/MicroJava/J/Prog.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Java program = list of class declarations
*)

Prog = Decl +

types 'c prog = "'c cdecl list"

consts

  class		:: "'c prog \\<Rightarrow> (cname \\<leadsto> 'c class)"

  is_class	:: "'c prog \\<Rightarrow> cname \\<Rightarrow> bool"
  is_type	:: "'c prog \\<Rightarrow> ty    \\<Rightarrow> bool"

defs

  class_def	"class        \\<equiv> map_of"

  is_class_def	"is_class G C \\<equiv> class G C \\<noteq> None"

primrec
"is_type G (PrimT pt) = True"
"is_type G (RefT t) = (case t of NullT \\<Rightarrow> True | ClassT C \\<Rightarrow> is_class G C)"

end
