(*  Title: 	symtab
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1989  University of Cambridge
*)

(*Unbalanced binary trees indexed by strings
  No way to delete an entry
  could generalize alist_of to a traversal functional
*)

signature SYMTAB = 
sig
   type 'a table
   val alist_of : 'a table -> (string*'a) list
   val balance : 'a table -> 'a table
   val lookup : 'a table * string -> 'a option
   val null : 'a table
   val is_null : 'a table -> bool
   val st_of_alist : (string*'a)list * 'a table -> 'a table
   val st_of_declist : (string list * 'a)list * 'a table -> 'a table
   val update : (string*'a) * 'a table -> 'a table
   val update_new : (string*'a) * 'a table -> 'a table
   exception DUPLICATE of string
end;


functor SymtabFun () : SYMTAB = 
struct

(*symbol table errors, such as from update_new*)
exception DUPLICATE of string;

datatype 'a table = Tip  |  Branch of (string * 'a * 'a table * 'a table);


val null = Tip;

fun is_null Tip = true
  | is_null _ = false;


fun lookup (symtab: 'a table, key: string) : 'a option = 
  let fun look  Tip  = None
	| look (Branch (key',entry,left,right)) =
	    if      key < key' then look left
	    else if key' < key then look right
	    else  Some entry
  in look symtab end;

(*update, allows overwriting of an entry*)
fun update ((key: string, entry: 'a), symtab : 'a table)
  : 'a table =
  let fun upd  Tip  = Branch (key,entry,Tip,Tip)
	| upd (Branch(key',entry',left,right)) =
	    if      key < key' then Branch (key',entry', upd left, right)
	    else if key' < key then Branch (key',entry',left, upd right)
	    else                    Branch (key,entry,left,right)
  in  upd symtab  end;

(*Like update but fails if key is already defined in table.
  Allows st_of_alist, etc. to detect multiple definitions*)
fun update_new ((key: string, entry: 'a), symtab : 'a table)
  : 'a table =
  let fun upd Tip = Branch (key,entry,Tip,Tip)
	| upd (Branch(key',entry',left,right)) =
	    if      key < key' then Branch (key',entry', upd left, right)
	    else if key' < key then Branch (key',entry',left, upd right)
	    else  raise DUPLICATE(key)
  in  upd symtab  end;

(*conversion of symbol table to sorted association list*)
fun alist_of (symtab : 'a table) : (string * 'a) list =
  let fun ali (symtab,cont) = case symtab of
		Tip => cont
	| Branch (key,entry,left,right) =>
	    ali(left, (key,entry) :: ali(right,cont))
  in  ali (symtab,[])  end;


(*Make a balanced tree of the first n members of the sorted alist (sal).
  Utility for the function balance.*)
fun bal_of (sal, 0) = Tip
  | bal_of (sal, n) =
      let val mid = n div 2
      in  case  drop (mid,sal) of
	    [] => bal_of (sal, mid)   (*should not occur*)
	  | ((key,entry):: pairs) =>
		Branch(key,entry, bal_of(sal,mid), bal_of(pairs, n-mid-1))
      end;


fun balance symtab =
  let val sal = alist_of symtab
  in  bal_of (sal, length sal)  end;


(*Addition of association list to a symbol table*)
fun st_of_alist (al, symtab) =
    foldr update_new (al, symtab);

(*A "declaration" associates the same entry with a list of keys;
  does not allow overwriting of an entry*)
fun decl_update_new ((keys : string list, entry: 'a), symtab)
  : 'a table =
  let fun decl (key,symtab) = update_new((key,entry), symtab)
  in  foldr decl (keys, symtab)  end;

(*Addition of a list of declarations to a symbol table*)
fun st_of_declist (dl, symtab) =
    balance (foldr decl_update_new (dl, symtab))

end;

