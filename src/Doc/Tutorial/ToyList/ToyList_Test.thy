theory ToyList_Test
imports Datatype
begin

ML {*  (* FIXME somewhat non-standard, fragile *)
  let
    val texts =
      map (File.read o Path.append (Resources.master_directory @{theory}) o Path.explode)
        ["ToyList1", "ToyList2"];
    val trs = Outer_Syntax.parse Position.start (implode texts);
    val end_state = fold (Toplevel.command_exception false) trs Toplevel.toplevel;
  in @{assert} (Toplevel.is_toplevel end_state) end;
*}

end

