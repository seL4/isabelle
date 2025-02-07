/*  Title:      Pure/Admin/component_find_facts_web.scala
    Author:     Fabian Huch, TU Muenchen

Build Isabelle component for find_facts web app, including external resources.
*/

package isabelle


import find_facts.Find_Facts


object Component_Find_Facts_Web {
  /* roboto font */

  val default_roboto_url = "https://r2.fontsource.org/fonts/roboto"
  val default_roboto_version = "5.1.1"


  /* material components web elm */

  val default_mcwe_url = "https://unpkg.com/material-components-web-elm"
  val default_mcwe_version = "9.1.0"


  /* build find facts web app */

  def build_find_facts_web(
    roboto_base_url: String = default_roboto_url,
    roboto_version: String = default_roboto_version,
    mcwe_base_url: String = default_mcwe_url,
    mcwe_version: String = default_mcwe_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "find_facts_web-" + Date.Format.alt_date(Date.now())
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    val web_dir = Isabelle_System.make_directory(component_dir.path + Path.basic("web"))


    /* roboto */

    val roboto_download =  roboto_base_url + "@" + roboto_version + "/download.zip"
    val roboto_fonts =
      List(300, 400, 500).map(weight => weight -> ("roboto-latin-" + weight + "-normal.woff"))

    Isabelle_System.with_tmp_dir("download") { download_dir =>
      val archive_path = download_dir + Path.basic("download.zip")

      Isabelle_System.download_file(roboto_download, archive_path)
      Isabelle_System.extract(archive_path, download_dir)

      roboto_fonts.foreach((_, name) =>
        Isabelle_System.copy_file(download_dir + Path.make(List("webfonts", name)), web_dir))
      Isabelle_System.copy_file(
        download_dir + Path.basic("LICENSE"),
        component_dir.path + Path.basic("LICENSE-roboto"))

      File.write(web_dir + Path.basic("roboto.css"), roboto_fonts.map((weight, name) => """
@font-face {
  font-family: 'Roboto';
  font-weight: """ + weight + """;
  src: url('./""" + name + """') format('woff');
}
""").mkString)
    }

    val roboto_css = "roboto.css" -> HTTP.Content.mime_type_css
    val roboto_assets = roboto_css :: roboto_fonts.map((_, name) => name -> "font/woff")


    /* mcwe */

    def mcwe_file(path: String): String = mcwe_base_url + "@" + mcwe_version + "/" + path

    val mcwe_assets =
      List(
        "material-components-web-elm.min.js" -> HTTP.Content.mime_type_js,
        "material-components-web-elm.min.css" -> HTTP.Content.mime_type_css)

    for ((name, _) <- mcwe_assets)
      Isabelle_System.download_file(mcwe_file("dist/" + name), web_dir + Path.basic(name))


    /* settings */

    val assets =
      (roboto_assets ::: mcwe_assets).map((name, mime_type) => name + ":" + mime_type).mkString(",")
    component_dir.write_settings("""
FIND_FACTS_WEB_ASSETS_DIR="$COMPONENT/web"
FIND_FACTS_WEB_ASSETS="""" + assets + """"
""")

    /* README */

    File.write(component_dir.README,
      """This component contains web assets (downloaded from recommended CDNs) for the Find_Facts
web application, and its compiled index.html.

Sources can be found in $FIND_FACTS_HOME/web.

        Fabian Huch
""")


    /* pre-compiled web app */

    Isabelle_System.with_tmp_dir("find_facts") { dir =>
      Find_Facts.build_html(web_dir + Find_Facts.web_html, dir, assets, progress = progress)
    }


    /* license */

    File.write(
      component_dir.path + Path.basic("LICENSE-material-components-web-elm"),
      Url.read(mcwe_file("LICENSE")))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool(
      "component_find_facts_web",
      "build Find_Facts web component from elm sources and external resources",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current

        val getopts = Getopts("""
Usage: isabelle component_find_facts_web [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")

  Build Find_Facts web component from the specified url and elm sources.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_find_facts_web(target_dir = target_dir, progress = progress)
      })
}