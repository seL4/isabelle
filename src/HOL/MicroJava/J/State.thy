(*  Title:      HOL/MicroJava/J/State.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

State for evaluation of Java expressions and statements
*)

State = TypeRel + Value +

types	fields_
	= "(vname \\<times> cname \\<leadsto> val)" (* field name, defining class, value *)

        obj = "cname \\<times> fields_"	(* class instance with class name and fields *)

constdefs

  obj_ty	:: "obj => ty"
 "obj_ty obj  == Class (fst obj)"

  init_vars	:: "('a \\<times> ty) list => ('a \\<leadsto> val)"
 "init_vars	== map_of o map (\\<lambda>(n,T). (n,default_val T))"
  
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
  heap		:: "state => aheap"
  locals	:: "state => locals"
  Norm		:: "state => xstate"

translations
  "heap"	=> "fst"
  "locals"	=> "snd"
  "Norm s"      == "(None,s)"  

constdefs

  new_Addr	:: "aheap => loc \\<times> xcpt option"
 "new_Addr h == SOME (a,x). (h a = None \\<and>  x = None) |  x = Some OutOfMemory"

  raise_if	:: "bool => xcpt => xcpt option => xcpt option"
 "raise_if c x xo == if c \\<and>  (xo = None) then Some x else xo"

  np		:: "val => xcpt option => xcpt option"
 "np v == raise_if (v = Null) NullPointer"

  c_hupd	:: "aheap => xstate => xstate"
 "c_hupd h'== \\<lambda>(xo,(h,l)). if xo = None then (None,(h',l)) else (xo,(h,l))"

  cast_ok	:: "'c prog => cname => aheap => val => bool"
 "cast_ok G C h v == v = Null \\<or> G\\<turnstile>obj_ty (the (h (the_Addr v)))\\<preceq> Class C"

end
