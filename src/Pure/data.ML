(*  Title:      Pure/data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Arbitrarily typed data.  Fools the ML type system via exception
constructors.
*)

signature DATA =
sig
  type T
  val empty: T
  val merge: T * T -> T
  val print: T -> unit
  val init: T -> string -> exn -> (exn * exn -> exn) -> (string -> exn -> Pretty.T) -> T
  val get: T -> string -> exn
  val put: T -> string -> exn -> T
end;


structure Data: DATA =
struct

(* datatype T *)

datatype T = Data of (*value, merge method, pp method*)
  (exn * ((exn * exn -> exn) * (string -> exn -> Pretty.T))) Symtab.table;


(* errors *)

fun err_msg_merge kind =
  error_msg ("Error while trying to merge " ^ quote kind ^ " data");

fun err_dup_init kind =
  error ("Duplicate initialization of " ^ quote kind ^ " data");

fun err_uninit kind =
  error ("Tried to access uninitialized " ^ quote kind ^ " data");


(* operations *)

val empty = Data Symtab.null;


fun merge (Data tab1, Data tab2) =
  let
    val data1 = Symtab.dest tab1;
    val data2 = Symtab.dest tab2;
    val all_data = data1 @ data2;
    val kinds = distinct (map fst all_data);

   fun entry data kind =
     (case assoc (data, kind) of
       None => []
     | Some x => [(kind, x)]);

    fun merge_entries [x] = x
      | merge_entries [(kind, (e1, mths as (mrg, _))), (_, (e2, _))] =
          (kind, (mrg (e1, e2) handle exn => (err_msg_merge kind; raise exn), mths))
      | merge_entries _ = sys_error "merge_entries";

    val data = map (fn k => merge_entries (entry data1 k @ entry data2 k)) kinds;
  in Data (Symtab.make data) end;


fun print (Data tab) =
  let fun prnt (kind, (e, (_, prt))) = Pretty.writeln (prt kind e) in
    seq prnt (Symtab.dest tab)
  end;


fun init (Data tab) kind e mrg prt =
  Data (Symtab.update_new ((kind, (e, (mrg, prt))), tab))
    handle Symtab.DUPLICATE _ => err_dup_init kind;


fun get (Data tab) kind =
  (case Symtab.lookup (tab, kind) of
    Some (e, _) => e
  | None => err_uninit kind);


fun put (Data tab) kind e =
  (case Symtab.lookup (tab, kind) of
    Some (_, meths) => Data (Symtab.update ((kind, (e, meths)), tab))
  | None => err_uninit kind);


end;
