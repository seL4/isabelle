
(* FIXME get rid of this!! *)


(*Read a term from string "b", with expected type T*)
fun readtm sign T b = 
    read_cterm sign (b,T) |> term_of
    handle ERROR => error ("The error(s) above occurred for " ^ b);


(* FIXME broken! *)

(*Skipping initial blanks, find the first identifier*)
fun scan_to_id s =
    s |> Symbol.explode
    |> Scan.error (Scan.finite Symbol.stopper
      (!! (fn _ => "Expected to find an identifier in " ^ s)
        (Scan.any Symbol.is_blank |-- Syntax.scan_id)))
    |> #1;
