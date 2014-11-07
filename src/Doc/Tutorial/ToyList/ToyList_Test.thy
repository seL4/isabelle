theory ToyList_Test
imports Main
begin

ML {*
  let val text =
    map (File.read o Path.append (Resources.master_directory @{theory}) o Path.explode)
      ["ToyList1.txt", "ToyList2.txt"]
    |> implode
  in Thy_Info.script_thy Position.start text @{theory} end
*}

end
