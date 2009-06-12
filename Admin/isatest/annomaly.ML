(*  Title:      Admin/isatest/annomaly.ML
    Author:     Martin von Gagern <martin@von-gagern.net>
*)

use "ML-Systems/smlnj.ML";

local

  val smlnj_use_text = use_text

  val smlnj_use_file = use_file

  val smlnj_forget_structure = forget_structure

  fun mkAbsolute path =
      OS.Path.mkAbsolute { path = path, relativeTo = OS.FileSys.getDir () }

  fun toArcs path = #arcs (OS.Path.fromString path)

  val isabelleHome =
      case OS.Process.getEnv "ISABELLE_HOME"
       of  NONE => OS.FileSys.getDir ()
	 | SOME home => mkAbsolute home

  fun noparent [] = []
    | noparent (n :: ns) =
      if n = OS.Path.parentArc then noparent ns else n :: noparent ns

  fun isabellePath [] = []
    | isabellePath ("src" :: name) = "Isabelle" :: name
    | isabellePath (name as (n :: ns)) =
      if n = OS.Path.parentArc then noparent ns else "Isabelle" :: name

  fun rewrite defPrefix name =
      let val abs = mkAbsolute name
	  val rel = OS.Path.mkRelative { path = abs, relativeTo = isabelleHome }
	  val exists = (OS.FileSys.access(abs, nil)
			handle OS.SysErr _ => false)
      in  if exists andalso rel <> ""
	  then isabellePath (toArcs rel)
	  else defPrefix @ noparent (toArcs name)
      end handle OS.Path.Path => defPrefix @ noparent (toArcs name)

in

  fun use_text tune str_of_pos name_space (line, name) p v t =
    let val name = case name of "" => "unnamed" | name => name
        val arcs = rewrite ["use_text"] name
        (* should we have different files for different line numbers? *
        val arcs = if line <= 1 then arcs
                   else arcs @ [ "l." ^ Int.toString line ]
	*)
	val arcs = if t = "structure Isabelle =\nstruct\nend;"
		      andalso name = "ML"
		   then ["empty_Isabelle", "empty" ] else arcs
        val _    = AnnoMaLy.nameNextStream arcs
    in  smlnj_use_text tune str_of_pos name_space (line, name) p v t  end;

  fun use_file tune str_of_pos name_space output verbose name =
      let val arcs = rewrite ["use_file"] name
          val _    = AnnoMaLy.nameNextStream arcs
      in  smlnj_use_file tune str_of_pos name_space output verbose name  end;

  fun forget_structure name =
      let val arcs = [ "forget_structure", name ]
          val _    = AnnoMaLy.nameNextStream arcs
      in  smlnj_forget_structure name  end;

end;
