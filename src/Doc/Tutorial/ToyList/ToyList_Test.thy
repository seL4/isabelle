theory ToyList_Test
imports Old_Datatype
begin

ML {*
  map (File.read o Path.append (Resources.master_directory @{theory}) o Path.explode)
    ["ToyList1.txt", "ToyList2.txt"]
  |> implode
  |> Thy_Info.script_thy Position.start
*}

end
