(*  Title:      HOL/BCV/JType.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The type system of the JVM
*)

JType = Err +

types cname
arities cname :: term

types subclass = "(cname*cname)set"

datatype ty = Void | Integer | NullT | Class cname

constdefs
 is_Class :: ty => bool
"is_Class T == case T of Void => False | Integer => False | NullT => False
               | Class C => True"

 is_ref :: ty => bool
"is_ref T == T=NullT | is_Class T"

 subtype :: subclass => ty ord
"subtype S T1 T2 ==
 (T1=T2) | T1=NullT & is_Class T2 |
 (? C D. T1 = Class C & T2 = Class D & (C,D) : S^*)"

 sup :: "subclass => ty => ty => ty err"
"sup S T1 T2 ==
 case T1 of Void => (case T2 of Void    => OK Void
                              | Integer => Err
                              | NullT   => Err
                              | Class D => Err)
          | Integer => (case T2 of Void    => Err
                                 | Integer => OK Integer
                                 | NullT   => Err
                                 | Class D => Err)
          | NullT => (case T2 of Void    => Err
                               | Integer => Err
                               | NullT   => OK NullT
                               | Class D => OK(Class D))
          | Class C => (case T2 of Void    => Err
                                 | Integer => Err
                                 | NullT   => OK(Class C)
                                 | Class D => OK(Class(some_lub (S^*) C D)))"

 Object :: cname
"Object == arbitrary"

 is_type :: subclass => ty => bool
"is_type S T == case T of Void => True | Integer => True | NullT => True
                | Class C => (C,Object):S^*"

syntax
 "types" :: subclass => ty set
 "@subty" :: ty => subclass => ty => bool  ("(_ /[='__ _)" [50, 1000, 51] 50)
translations
 "types S" == "Collect(is_type S)"
 "x [=_S y"  == "x <=_(subtype S) y"

constdefs
 esl :: "subclass => ty esl"
"esl S == (types S, subtype S, sup S)"

end
