/*  Title:      Pure/Admin/isabelle_devel.scala
    Author:     Makarius

Website for Isabelle development resources.
*/

package isabelle


object Isabelle_Devel {
  val isabelle_devel: Path = Path.explode("~/html-data/devel")


  /* index */

  def make_index(): Unit = {
    val redirect = "https://isabelle-dev.sketis.net/home/menu/view/20"

    HTML.write_document(isabelle_devel, "index.html",
      List(
        XML.Elem(Markup("meta",
          List("http-equiv" -> "Refresh", "content" -> ("0; url=" + redirect))), Nil)),
      List(HTML.link(redirect, HTML.text("Isabelle Development Resources"))))
  }


  /* release snapshot */

  def release_snapshot(options: Options, rev: String, afp_rev: String,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_dir("isadist") { target_dir =>
      Isabelle_System.update_directory(isabelle_devel + Path.explode("release_snapshot"),
        { website_dir =>
          val context = Build_Release.Release_Context(target_dir, progress = progress)
          Build_Release.build_release_archive(context, rev)
          Build_Release.build_release(options, context, afp_rev = afp_rev,
            build_sessions = List(Isabelle_System.getenv("ISABELLE_LOGIC")),
            website = Some(website_dir))
        }
      )
    }
  }


  /* present build status */

  def build_status(options: Options): Unit = {
    Isabelle_System.update_directory(isabelle_devel + Path.explode("build_status"),
      dir => Build_Status.build_status(options, target_dir = dir, ml_statistics = true))
  }
}
