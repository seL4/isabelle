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
  val prep_ext: T -> T
  val kinds: T -> string list
  val init: T -> string -> exn -> (exn -> exn) -> (exn * exn -> exn) -> (exn -> unit) -> T
  val get: T -> string -> exn
  val put: T -> string -> exn -> T
  val print: T -> string -> unit
end;


structure Data: DATA =
struct


(* datatype T *)

datatype T = Data of
  (exn *				(*value*)
   ((exn -> exn) *			(*prepare extend method*)
    (exn * exn -> exn) *		(*merge and prepare extend method*)
    (exn -> unit)))			(*print method*)
  Symtab.table;

val empty = Data Symtab.null;

fun kinds (Data tab) = map fst (Symtab.dest tab);


(* errors *)

fun err_method name kind =
  error ("Error while invoking " ^ name ^ " method of " ^ quote kind ^ " data");

fun err_dup_init kind =
  error ("Duplicate initialization of " ^ quote kind ^ " data");

fun err_uninit kind =
  error ("Tried to access uninitialized " ^ quote kind ^ " data");


(* prepare data *)

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

    fun merge_entries [(kind, (e, mths as (ext, _, _)))] =
          (kind, (ext e handle exn => err_method "prep_ext" kind, mths))
      | merge_entries [(kind, (e1, mths as (_, mrg, _))), (_, (e2, _))] =
          (kind, (mrg (e1, e2) handle exn => (err_method "merge" kind; raise exn), mths))
      | merge_entries _ = sys_error "merge_entries";

    val data = map (fn k => merge_entries (entry data1 k @ entry data2 k)) kinds;
  in Data (Symtab.make data) end;


fun prep_ext data = merge (data, empty);

fun init (Data tab) kind e ext mrg prt =
  Data (Symtab.update_new ((kind, (e, (ext, mrg, prt))), tab))
    handle Symtab.DUPLICATE _ => err_dup_init kind;


(* access data *)

fun lookup tab kind =
  (case Symtab.lookup (tab, kind) of
    Some x => x
  | None => err_uninit kind);

fun get (Data tab) kind = fst (lookup tab kind);

fun put (Data tab) kind e =
  Data (Symtab.update ((kind, (e, snd (lookup tab kind))), tab));

fun print (Data tab) kind =
  let val (e, (_, _, prt)) = lookup tab kind
  in prt e handle exn => err_method "print" kind end;


end;
