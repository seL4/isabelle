(*  Title: 	HOLCF/void.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Definition of type void with partial order. Void is the prototype for
all types in class 'po'

Type void  is defined as a set Void over type bool.
*)

Void = Holcfb +

types void 0

arities void :: term

consts
  Void		:: "bool set"
  UU_void_Rep	:: "bool"	
  Rep_Void	:: "void => bool"
  Abs_Void	:: "bool => void"
  UU_void	:: "void"
  less_void	:: "[void,void] => bool"	

rules

  (* The unique element in Void is False:bool *)

  UU_void_Rep_def	"UU_void_Rep == False"
  Void_def		"Void == {x. x = UU_void_Rep}"

  (*faking a type definition... *)
  (* void is isomorphic to Void *)

  Rep_Void		"Rep_Void(x):Void"		
  Rep_Void_inverse	"Abs_Void(Rep_Void(x)) = x"	
  Abs_Void_inverse	"y:Void ==> Rep_Void(Abs_Void(y)) = y"

   (*defining the abstract constants*)

  UU_void_def	"UU_void == Abs_Void(UU_void_Rep)"  
  less_void_def "less_void(x,y) == (Rep_Void(x) = Rep_Void(y))"  
end




