theory ToyList_Test
imports Main
begin

ML \<open>
  let val text =
    map (File.read o Path.append \<^master_dir>) [\<^path>\<open>ToyList1.txt\<close>, \<^path>\<open>ToyList2.txt\<close>]
    |> implode
  in Thy_Info.script_thy Position.start text @{theory} end
\<close>

end
