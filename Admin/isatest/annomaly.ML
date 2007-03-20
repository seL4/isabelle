use "ML-Systems/smlnj.ML";                                      

local

  val smlnj_use_text = use_text

  fun strip ([], "src" :: name, _) = name
    | strip (["Distribution"], name, _) = name
    | strip ([], name, _) = name
    | strip (h1 :: t1, h2 :: t2, def) =
      if h1 = h2 then strip (t1, t2, def) else def

  fun rewrite (NONE, name) = "use_text" :: name
    | rewrite (SOME home, name) =
      strip (#arcs (OS.Path.fromString home), name, "use_text" :: name)

in

  fun use_text name p v t = 
      let val name = case name of "" => "unnamed" | name => name
	  val arcs = rewrite (OS.Process.getEnv "ISABELLE_HOME",
			      #arcs (OS.Path.fromString name))
	  val _    = AnnoMaLy.nameNextStream ("isabelle" :: arcs)
      in  smlnj_use_text name p v t
      end

end;
