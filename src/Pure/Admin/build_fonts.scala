/*  Title:      Pure/Admin/build_fonts.scala
    Author:     Makarius

Build of Isabelle fonts: DejaVu + special symbols.
*/

package isabelle


object Build_Fonts
{
  /* relevant codepoint ranges */

  object Range
  {
    def base_font: Seq[Int] =
      (0x0020 to 0x007e) ++  // ASCII
      (0x00a0 to 0x024f) ++  // Latin Extended-A/B
      (0x0400 to 0x04ff) ++  // Cyrillic
      (0x0600 to 0x06ff) ++  // Arabic
      Seq(
        0x2018,  // single quote
        0x2019,  // single quote
        0x201a,  // single quote
        0x201c,  // double quote
        0x201d,  // double quote
        0x201e,  // double quote
        0x2039,  // single guillemet
        0x203a,  // single guillemet
        0x204b,  // FOOTNOTE
        0x20ac,  // Euro
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
        0x2020,  // dagger
        0x2021,  // double dagger
        0x2022,  // bullet
        0x2026,  // ellipsis
        0x2030,  // perthousand
        0x2032,  // minute
        0x2033,  // second
        0x2038,  // caret
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
        0x2756,  // UNDEFINED
        0x2759,  // BOLD
        0x27a7,  // DESCR
        0x27e6,  // left white square bracket
        0x27e7,  // right white square bracket
        0x27e8,  // left angle bracket
        0x27e9,  // right angle bracket
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
  }


  /* font families */

  sealed case class Family(
    plain: String = "",
    bold: String = "",
    italic: String = "",
    bold_italic: String = "")
  {
    val fonts: List[String] =
      proper_string(plain).toList :::
      proper_string(bold).toList :::
      proper_string(italic).toList :::
      proper_string(bold_italic).toList

    def get(index: Int): String = fonts(index % fonts.length)
  }

  object Family
  {
    def isabelle_text: Family =
      Family(
        plain = "IsabelleText.sfd",
        bold = "IsabelleTextBold.sfd")

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
  }


  /* build fonts */

  private def find_file(dirs: List[Path], name: String): Path =
  {
    val path = Path.explode(name)
    dirs.collectFirst({ case dir if (dir + path).is_file => dir + path }) match {
      case Some(file) => file
      case None =>
        error(cat_lines(
          ("Failed to find font file " + path + " in directories:") ::
            dirs.map(dir => "  " + dir.toString)))
    }
  }

  val default_sources: List[Family] =
    List(Family.deja_vu_sans_mono, Family.deja_vu_sans, Family.deja_vu_serif)

  def build_fonts(
    sources: List[Family] = default_sources,
    source_dirs: List[Path] = Nil,
    target_prefix: String = "Isabelle",
    target_version: String = "",
    target_dir: Path = Path.current,
    progress: Progress = No_Progress)
  {
    Isabelle_System.mkdirs(target_dir)

    val font_dirs = source_dirs ::: List(Path.explode("~~/lib/fonts"))

    for { source <- sources; (source_font, index) <- source.fonts.zipWithIndex } {
      val isabelle_file = find_file(font_dirs, Family.isabelle_text.get(index))

      val source_file = find_file(font_dirs, source_font)
      val source_names = Fontforge.font_names(source_file)

      val target_names = source_names.update(prefix = target_prefix, version = target_version)
      val target_file = target_dir + target_names.ttf

      progress.echo("Creating " + target_file.toString + " ...")
      Fontforge.execute(
        Fontforge.commands(
          Fontforge.open(isabelle_file),
          Fontforge.select(Range.isabelle_font),
          Fontforge.copy,
          Fontforge.close,

          Fontforge.open(source_file),
          Fontforge.select(Range.base_font),
          Fontforge.select_invert,
          Fontforge.clear,
          Fontforge.select(Range.isabelle_font),
          Fontforge.paste,

          target_names.set,
          Fontforge.generate(target_file),
          Fontforge.close)
      ).check
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_fonts", "construct Isabelle fonts", args =>
    {
      var source_dirs: List[Path] = Nil
      var target_dir = Path.current

      val getopts = Getopts("""
Usage: isabelle build_fonts [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -d DIR       additional source directory

  Construct Isabelle fonts from DejaVu font families and Isabelle symbols.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "d:" -> (arg => source_dirs = source_dirs ::: List(Path.explode(arg))))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress

      build_fonts(source_dirs = source_dirs, target_dir = target_dir, progress = progress)
    })
}
