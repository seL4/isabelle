(*  Title:      HOL/MicroJava/J/State.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

State for evaluation of Java expressions and statements
*)

State = WellType +

constdefs

  the_Bool	:: "val \\<Rightarrow> bool"
 "the_Bool v  \\<equiv> \\<epsilon>b. v = Bool b"

  the_Int	:: "val \\<Rightarrow> int"
 "the_Int  v  \\<equiv> \\<epsilon>i. v = Intg i"

  the_Addr	:: "val \\<Rightarrow> loc"
 "the_Addr  v  \\<equiv> \\<epsilon>a. v = Addr a"

consts

  defpval	:: "prim_ty \\<Rightarrow> val"	(* default value for primitive types *)
  default_val	:: "ty \\<Rightarrow> val"		(* default value for all types *)

primrec
	"defpval Void    = Unit"
	"defpval Boolean = Bool False"
	"defpval Integer = Intg (#0)"

primrec
	"default_val (PrimT pt) = defpval pt"
	"default_val (RefT  r ) = Null"

types	fields_
	= "(vname \\<times> cname \\<leadsto> val)" (* field name, defining class, value *)

types obj = "cname \\<times> fields_"	(* class instance with class name and fields *)

constdefs

  obj_ty	:: "obj \\<Rightarrow> ty"
 "obj_ty obj  \\<equiv> Class (fst obj)"

  init_vars	:: "('a \\<times> ty) list \\<Rightarrow> ('a \\<leadsto> val)"
 "init_vars	\\<equiv> map_of o map (\\<lambda>(n,T). (n,default_val T))"
  
datatype xcpt		(* exceptions *)
	= NullPointer
	| ClassCast
	| OutOfMemory

types	aheap  = "loc \\<leadsto> obj" (* "heap" used in a translation below *)
        locals = "vname \\<leadsto> val"	

        state		(* simple state, i.e. variable contents *)
	= "aheap \\<times> locals"
	(* heap, local parameter including This *)

	xstate		(* state including exception information *)
	 = "xcpt option \\<times> state"

syntax
  heap		:: "state \\<Rightarrow> aheap"
  locals	:: "state \\<Rightarrow> locals"
  Norm		:: "state \\<Rightarrow> xstate"

translations
  "heap"	=> "fst"
  "locals"	=> "snd"
  "Norm s"      == "(None,s)"  

constdefs

  new_Addr	:: "aheap \\<Rightarrow> loc \\<times> xcpt option"
 "new_Addr h \\<equiv> \\<epsilon>(a,x). (h a = None \\<and>  x = None) |  x = Some OutOfMemory"

  raise_if	:: "bool \\<Rightarrow> xcpt \\<Rightarrow> xcpt option \\<Rightarrow> xcpt option"
 "raise_if c x xo \\<equiv> if c \\<and>  (xo = None) then Some x else xo"

  np		:: "val \\<Rightarrow> xcpt option \\<Rightarrow> xcpt option"
 "np v \\<equiv> raise_if (v = Null) NullPointer"

  c_hupd	:: "aheap \\<Rightarrow> xstate \\<Rightarrow> xstate"
 "c_hupd h'\\<equiv> \\<lambda>(xo,(h,l)). if xo = None then (None,(h',l)) else (xo,(h,l))"

  cast_ok	:: "'c prog \\<Rightarrow> ty \\<Rightarrow> aheap \\<Rightarrow> val \\<Rightarrow> bool"
 "cast_ok G T h v \\<equiv> ((\\<exists>pt. T = PrimT pt) | (v=Null) | G\\<turnstile>obj_ty (the (h (the_Addr v)))\\<preceq>T)"

end
