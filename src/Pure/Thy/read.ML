(*  Title:      Pure/Thy/read
    ID:         $Id$
    Author:     Sonia Mahjoub / Tobias Nipkow / L C Paulson
    Copyright   1992  TU Muenchen

Reading and writing the theory definition files.

For theory XXX, the  input file is called XXX.thy
                the output file is called .XXX.thy.ML
                and it then tries to read XXX.ML
*)

signature READTHY =
sig
  val split_filename : string -> string * string
  val time_use_thy   : string -> unit
  val use_thy        : string -> unit
end;


functor ReadthyFUN (ThySyn: THYSYN): READTHY =
struct

(*Convert Unix filename of the form path/file to "path/" and "file" ;
  if filename contains no slash, then it returns "" and "file" *)
fun split_filename name =
  let val (file,path) = take_prefix (apr(op<>,"/")) (rev (explode name))
  in  (implode(rev path), implode(rev file)) end;

(*create name of the output ML file for the theory*)
fun out_name thy = "." ^ thy ^ ".thy.ML";

fun read_thy path thy =
    let val instream  = open_in (path ^ thy ^ ".thy")
        val outstream = open_out (path ^ out_name thy)
    in  output (outstream, ThySyn.read (explode(input(instream, 999999))));
        close_out outstream;
        close_in instream
    end;

fun file_exists file =
  let val instream = open_in file in close_in instream; true end
    handle Io _ => false;

(*Use the file if it exists*)
fun try_use file =
  if file_exists file then use file else ();

(*Read and convert the theory to a .XXX.thy.ML file and also try to read XXX.ML*)
fun use_thy name =
    let val (path,thy) = split_filename name
    in  read_thy path thy;
        use (path ^ out_name thy);
        try_use (path ^ thy ^ ".ML")
    end;

fun time_use_thy tname = timeit(fn()=>
   (writeln("\n**** Starting Theory " ^ tname ^ " ****");  use_thy tname;
    writeln("\n**** Finished Theory " ^ tname ^ " ****")));

end;
