(*  Title:      isabelle/Bali/Example.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen

The following example Bali program includes:
 class declarations with inheritance, hiding of fields, and overriding of
  methods (with refined result type), 
 instance creation, local assignment, sequential composition,
 method call with dynamic binding, literal values,
 expression statement, local access, type cast, field assignment (in part), skip

class Base {
  boolean vee;
  Base foo(Base x) {return x;}
}

class Ext extends Base {
  int vee;
  Ext foo(Base x) {((Ext)x).vee=1; return null;}
}

class Example {
  public static void main (String args[]) {
    Base e=new Ext();
    e.foo(null);
  }
}
*)

Example = Eval + 

datatype cnam_ = Base_ | Ext_
datatype vnam_ = vee_ | x_ | e_

consts

  cnam_ :: "cnam_ => cname"
  vnam_ :: "vnam_ => vnam"

rules (* cnam_ and vnam_ are intended to be isomorphic to cnam and vnam *)

  inj_cnam_  "(cnam_ x = cnam_ y) = (x = y)"
  inj_vnam_  "(vnam_ x = vnam_ y) = (x = y)"

  surj_cnam_ "\\<exists>m. n = cnam_ m"
  surj_vnam_ "\\<exists>m. n = vnam_ m"

syntax

  Base,  Ext	:: cname
  vee, x, e	:: vname

translations

  "Base" == "cnam_ Base_"
  "Ext"	 == "cnam_ Ext_"
  "vee"  == "VName (vnam_ vee_)"
  "x"	 == "VName (vnam_ x_)"
  "e"	 == "VName (vnam_ e_)"

rules
  Base_not_Object "Base \\<noteq> Object"
  Ext_not_Object  "Ext  \\<noteq> Object"

consts

  foo_Base       :: java_mb
  foo_Ext        :: java_mb
  BaseC, ExtC    :: java_mb cdecl
  test		 :: stmt
  foo	         :: mname
  a,b		 :: loc

defs

  foo_Base_def "foo_Base == ([x],[],Skip,LAcc x)"
  BaseC_def "BaseC == (Base, (Object, 
			     [(vee, PrimT Boolean)], 
			     [((foo,[Class Base]),Class Base,foo_Base)]))"
  foo_Ext_def "foo_Ext == ([x],[],Expr( {Ext}Cast Ext
				       (LAcc x)..vee:=Lit (Intg #1)),
				   Lit Null)"
  ExtC_def  "ExtC  == (Ext,  (Base  , 
			     [(vee, PrimT Integer)], 
			     [((foo,[Class Base]),Class Ext,foo_Ext)]))"

  test_def "test == Expr(e::=NewC Ext);; 
                    Expr({Base}LAcc e..foo({[Class Base]}[Lit Null]))"


syntax

  NP		:: xcpt
  tprg 	 	:: java_mb prog
  obj1, obj2	:: obj
  s0,s1,s2,s3,s4:: state

translations

  "NP"   == "NullPointer"
  "tprg" == "[ObjectC, BaseC, ExtC]"
  "obj1"    <= "(Ext, empty((vee, Base)\\<mapsto>Bool False)
			   ((vee, Ext )\\<mapsto>Intg #0))"
  "s0" == " Norm    (empty, empty)"
  "s1" == " Norm    (empty(a\\<mapsto>obj1),empty(e\\<mapsto>Addr a))"
  "s2" == " Norm    (empty(a\\<mapsto>obj1),empty(x\\<mapsto>Null)(This\\<mapsto>Addr a))"
  "s3" == "(Some NP, empty(a\\<mapsto>obj1),empty(e\\<mapsto>Addr a))"
end
