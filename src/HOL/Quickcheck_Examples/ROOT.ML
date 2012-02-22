use_thys [
  "Find_Unused_Assms",
  "Quickcheck_Examples",
  "Quickcheck_Lattice_Examples"
];

if getenv "ISABELLE_GHC" = "" then ()
else use_thy "Quickcheck_Narrowing_Examples";

