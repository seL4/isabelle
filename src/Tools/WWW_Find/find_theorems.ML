(*  Title:      Tools/WWW_Find/find_theorems.ML
    Author:     Timothy Bourke, NICTA

Simple find_theorems server.
*)

local

val default_limit = 20;
val all_thy_names = sort string_ord (Thy_Info.get_names ());

fun app_index f xs = fold_index (fn x => K (f x)) xs ();

fun find_theorems arg_data send =
  let
    val args = Symtab.lookup arg_data;

    val query_str = the_default "" (args "query");
    fun get_query () = Find_Theorems.read_query Position.none query_str;

    val limit = case args "limit" of
        NONE => default_limit
      | SOME str => the_default default_limit (Int.fromString str);
    val thy_name = the_default "Main" (args "theory");
    val with_dups = is_some (args "with_dups");
    
    val ctxt = Proof_Context.init_global (Thy_Info.get_theory thy_name);

    fun do_find query =
      let
        val (othmslen, thms) =
          Find_Theorems.find_theorems_cmd ctxt NONE (SOME limit) with_dups query
          ||> rev;
      in
        Xhtml.write send
          (HTML_Templates.find_theorems_summary (othmslen, length thms, arg_data));
        if null thms then ()
        else Xhtml.write_enclosed send HTML_Templates.find_theorems_table (fn send =>
               HTML_Unicode.print_mode (app_index (Xhtml.write send o HTML_Templates.html_thm ctxt)) thms)
      end;
  in
    send Xhtml.doctype_xhtml1_0_strict;
    Xhtml.write_enclosed send
      (HTML_Templates.header thy_name (args "query", limit, with_dups, all_thy_names))
      (fn send => 
        if query_str = "" then ()
        else
          do_find (get_query ())
          handle ERROR msg => Xhtml.write send (HTML_Templates.error msg))
  end;
in

val () = ScgiServer.register ("find_theorems", SOME Mime.html, ScgiServer.simple_handler find_theorems);

end;

