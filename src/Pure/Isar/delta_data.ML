(*  Author: Jia Meng, Cambridge University Computer Laboratory (06/01/05)
    Copyright 2004 University of Cambridge

Used for delta_simpset and delta_claset
*)

signature DELTA_DATA_ARGS =
sig
  val name: string 
  type T
  val empty: T
end;

signature DELTA_DATA =
sig
  type T
  val get: ProofContext.context -> T
  val put: T -> ProofContext.context -> ProofContext.context
end;

functor DeltaDataFun(Args: DELTA_DATA_ARGS): DELTA_DATA =
struct

type T = Args.T; 

exception Data of T; 

val key = Args.name; 

fun get ctxt =
    let val delta_tab = ProofContext.get_delta ctxt
	val delta_data = Symtab.lookup(delta_tab,key) 
    in
	case delta_data of (Some (Data d)) => d 
			 | None => (Args.empty)
    end;

fun put delta_data ctxt = 
    let val delta_tab = ProofContext.get_delta ctxt 
	val new_tab = Symtab.update((key,Data delta_data),delta_tab)
    in
	ProofContext.put_delta new_tab ctxt
    end;

end;


