/*  Title:      Pure/Admin/component_fonts.scala
    Author:     Makarius

Build standard Isabelle fonts: DejaVu base + Isabelle symbols.
*/

package isabelle


object Component_Fonts {
  /* relevant codepoint ranges */

  object Range {
    def base_font: Seq[Int] =
      (0x0020 to 0x007e) ++  // ASCII
      (0x00a0 to 0x024f) ++  // Latin Extended-A/B
      (0x0400 to 0x04ff) ++  // Cyrillic
      (0x0600 to 0x06ff) ++  // Arabic
      Seq(
        0x02dd,  // hungarumlaut
        0x2018,  // single quote
        0x2019,  // single quote
        0x201a,  // single quote
        0x201c,  // double quote
        0x201d,  // double quote
        0x201e,  // double quote
        0x2022,  // regular bullet
        0x2023,  // triangular bullet
        0x2039,  // single guillemet
        0x203a,  // single guillemet
        0x204b,  // FOOTNOTE
        0x20ac,  // Euro
        0x2710,  // pencil
        0xfb01,  // ligature fi
        0xfb02,  // ligature fl
        0xfffd,  // replacement character
      )

    def isabelle_font: Seq[Int] =
      Seq(
        0x05,  // X
        0x06,  // Y
        0x07,  // EOF
        0x7f,  // DEL
        0xaf,  // INVERSE
        0xac,  // logicalnot
        0xb0,  // degree
        0xb1,  // plusminus
        0xb7,  // periodcentered
        0xd7,  // multiply
        0xf7,  // divide
      ) ++
      (0x0370 to 0x03ff) ++  // Greek (pseudo math)
      (0x0590 to 0x05ff) ++  // Hebrew (non-mono)
      Seq(
        0x2010,  // hyphen
        0x2013,  // dash
        0x2014,  // dash
        0x2015,  // dash
        0x2016,  // big parallel
        0x2020,  // dagger
        0x2021,  // double dagger
        0x2026,  // ellipsis
        0x2030,  // perthousand
        0x2032,  // minute
        0x2033,  // second
        0x2038,  // caret
        0x2040,  // sequence concatenation
        0x20cd,  // currency symbol
      ) ++
      (0x2100 to 0x214f) ++  // Letterlike Symbols
      (0x2190 to 0x21ff) ++  // Arrows
      (0x2200 to 0x22ff) ++  // Mathematical Operators
      (0x2300 to 0x23ff) ++  // Miscellaneous Technical
      Seq(
        0x2423,  // graphic for space
        0x2500,  // box drawing
        0x2501,  // box drawing
        0x2508,  // box drawing
        0x2509,  // box drawing
        0x2550,  // box drawing
      ) ++
      (0x25a0 to 0x25ff) ++  // Geometric Shapes
      Seq(
        0x261b,  // ACTION
        0x2660,  // spade suit
        0x2661,  // heart suit
        0x2662,  // diamond suit
        0x2663,  // club suit
        0x266d,  // musical flat
        0x266e,  // musical natural
        0x266f,  // musical sharp
        0x2713,  // check mark
        0x2717,  // ballot X
        0x2756,  // UNDEFINED
        0x2759,  // BOLD
        0x27a7,  // DESCR
        0x27e6,  // left white square bracket
        0x27e7,  // right white square bracket
        0x27e8,  // left angle bracket
        0x27e9,  // right angle bracket
        0x27ea,  // left double angle bracket
        0x27eb,  // right double angle bracket
      ) ++
      (0x27f0 to 0x27ff) ++  // Supplemental Arrows-A
      (0x2900 to 0x297f) ++  // Supplemental Arrows-B
      (0x2980 to 0x29ff) ++  // Miscellaneous Mathematical Symbols-B
      (0x2a00 to 0x2aff) ++  // Supplemental Mathematical Operators
      Seq(0x2b1a) ++  // VERBATIM
      (0x1d400 to 0x1d7ff) ++  // Mathematical Alphanumeric Symbols
      Seq(
        0x1f310,  // globe with meridians (Symbola font)
        0x1f4d3,  // notebook (Symbola font)
        0x1f5c0,  // folder (Symbola font)
        0x1f5cf,  // page (Symbola font)
      )

    def isabelle_math_font: Seq[Int] =
      (0x21 to 0x2f) ++  // bang .. slash
      (0x3a to 0x40) ++  // colon .. atsign
      (0x5b to 0x5f) ++  // leftbracket .. underscore
      (0x7b to 0x7e) ++  // leftbrace .. tilde
      Seq(
        0xa9,  // copyright
        0xae,  // registered
      )

    val vacuous_font: Seq[Int] =
      Seq(0x3c)  // "<" as template
  }


  /* font families */

  sealed case class Family(
    plain: String = "",
    bold: String = "",
    italic: String = "",
    bold_italic: String = ""
  ) {
    val fonts: List[String] =
      proper_string(plain).toList :::
      proper_string(bold).toList :::
      proper_string(italic).toList :::
      proper_string(bold_italic).toList

    def get(index: Int): String = fonts(index % fonts.length)
  }

  object Family {
    def isabelle_symbols: Family =
      Family(
        plain = "IsabelleSymbols.sfd",
        bold = "IsabelleSymbolsBold.sfd")

    def deja_vu_sans_mono: Family =
      Family(
        plain = "DejaVuSansMono.ttf",
        bold = "DejaVuSansMono-Bold.ttf",
        italic = "DejaVuSansMono-Oblique.ttf",
        bold_italic = "DejaVuSansMono-BoldOblique.ttf")

    def deja_vu_sans: Family =
      Family(
        plain = "DejaVuSans.ttf",
        bold = "DejaVuSans-Bold.ttf",
        italic = "DejaVuSans-Oblique.ttf",
        bold_italic = "DejaVuSans-BoldOblique.ttf")

    def deja_vu_serif: Family =
      Family(
        plain = "DejaVuSerif.ttf",
        bold = "DejaVuSerif-Bold.ttf",
        italic = "DejaVuSerif-Italic.ttf",
        bold_italic = "DejaVuSerif-BoldItalic.ttf")

    def vacuous: Family = Family(plain = "Vacuous.sfd")
  }


  /* hinting */

  // see https://www.freetype.org/ttfautohint/doc/ttfautohint.html
  private def auto_hint(source: Path, target: Path): Unit = {
    Isabelle_System.bash("ttfautohint -i " +
      File.bash_path(source) + " " + File.bash_path(target)).check
  }

  private def make_path(hinted: Boolean = false): Path =
    if (hinted) Path.basic("ttf-hinted") else Path.basic("ttf")

  private val hinting = List(false, true)


  /* build fonts */

  private def find_file(dirs: List[Path], name: String): Path = {
    val path = Path.explode(name)
    dirs.collectFirst({ case dir if (dir + path).is_file => dir + path }) match {
      case Some(file) => file
      case None =>
        error(cat_lines(
          ("Failed to find font file " + path + " in directories:") ::
            dirs.map(dir => "  " + dir.toString)))
    }
  }

  val default_download_url =
    "https://github.com/dejavu-fonts/dejavu-fonts/releases/download/version_2_37/dejavu-fonts-ttf-2.37.zip"

  val default_sources: List[Family] =
    List(Family.deja_vu_sans_mono, Family.deja_vu_sans, Family.deja_vu_serif)

  def build_fonts(
    download_url: String = default_download_url,
    target_dir: Path = Path.current,
    target_prefix: String = "Isabelle",
    sources: List[Family] = default_sources,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.require_command("ttfautohint")

    Isabelle_System.with_tmp_file("download", ext = "zip") { download_file =>
      Isabelle_System.with_tmp_dir("download") { download_dir =>


        /* download */

        Isabelle_System.download_file(download_url, download_file, progress = progress)
        Isabelle_System.extract(download_file, download_dir)

        val dejavu_dir = File.get_dir(download_dir, title = download_url) + Path.basic("ttf")


        /* component */

        val component_date = Date.Format.alt_date(Date.now())
        val component_name = "isabelle_fonts-" + component_date
        val component_dir =
          Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

        for (hinted <- hinting) {
          Isabelle_System.make_directory(component_dir.path + make_path(hinted = hinted))
        }

        val font_dirs = List(dejavu_dir, Path.explode("~~/Admin/isabelle_fonts"))
        for (dir <- font_dirs if !dir.is_dir) error("Bad source directory: " + dir)


        // Isabelle fonts

        val fonts =
          for { source <- sources; (source_font, index) <- source.fonts.zipWithIndex }
          yield {
            val isabelle_file = find_file(font_dirs, Family.isabelle_symbols.get(index))

            val source_file = find_file(font_dirs, source_font)
            val source_names = Fontforge.font_names(source_file)

            val font_names = source_names.update(prefix = target_prefix, version = component_date)

            Isabelle_System.with_tmp_file("font", "ttf") { tmp_file =>
              for (hinted <- hinting) {
                val font_file = component_dir.path + make_path(hinted = hinted) + font_names.ttf
                progress.echo("Font " + font_file + " ...")

                if (hinted) auto_hint(source_file, tmp_file)
                else Isabelle_System.copy_file(source_file, tmp_file)

                Fontforge.execute(
                  Fontforge.commands(
                    Fontforge.open(isabelle_file),
                    Fontforge.select(Range.isabelle_font),
                    Fontforge.copy,
                    Fontforge.close,

                    Fontforge.open(tmp_file),
                    Fontforge.select(Range.base_font),
                    Fontforge.select_invert,
                    Fontforge.clear,
                    Fontforge.select(Range.isabelle_font),
                    Fontforge.paste,

                    font_names.set,
                    Fontforge.generate(font_file),
                    Fontforge.close)
                ).check
              }
            }

            (font_names.ttf, index)
          }


        // Vacuous font

        {
          val vacuous_file = find_file(font_dirs, Family.vacuous.get(0))

          val font_dir = component_dir.path + make_path()
          val font_names = Fontforge.font_names(vacuous_file)
          val font_file = font_dir + font_names.ttf

          progress.echo("Font " + font_file + " ...")

          val domain =
            (for ((name, index) <- fonts if index == 0)
              yield Fontforge.font_domain(font_dir + name))
            .flatten.distinct.sorted

          Fontforge.execute(
            Fontforge.commands(
              Fontforge.open(vacuous_file),
              Fontforge.select(Range.vacuous_font),
              Fontforge.copy) +

            domain.map(code =>
                Fontforge.commands(
                  Fontforge.select(Seq(code)),
                  Fontforge.paste))
              .mkString("\n", "\n", "\n") +

            Fontforge.commands(
              Fontforge.generate(font_file),
              Fontforge.close)
          ).check
        }


        /* settings */

        def make_settings(hinted: Boolean = false): String =
          "\n  isabelle_fonts \\\n" +
          (for ((ttf, _) <- fonts) yield
            """    "$COMPONENT/""" + make_path(hinted = hinted).file_name + "/" + ttf.file_name + "\"")
          .mkString(" \\\n")

        component_dir.write_settings("""
if grep "isabelle_fonts_hinted.*=.*false" "$ISABELLE_HOME_USER/etc/preferences" >/dev/null 2>/dev/null
then""" + make_settings() + """
else""" + make_settings(hinted = true) + """
fi

isabelle_fonts_hidden "$COMPONENT/""" + make_path().file_name + """/Vacuous.ttf"
""")


        /* README */

        Isabelle_System.copy_file(
          Path.explode("~~/Admin/isabelle_fonts/README"), component_dir.README)
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_fonts", "construct Isabelle fonts", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url

        val getopts = Getopts("""
Usage: isabelle component_fonts [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_download_url + """")

  Construct Isabelle fonts from DejaVu font families and Isabelle symbols.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_fonts(download_url = download_url, target_dir = target_dir, progress = progress)
      })
}
