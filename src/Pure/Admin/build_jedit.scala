/*  Title:      Pure/Admin/build_jedit.scala
    Author:     Makarius

Build auxiliary jEdit component.
*/

package isabelle


object Build_JEdit
{
  /* modes */

  object Mode
  {
    val empty: Mode = new Mode("", "", Nil)

    val init: Mode =
      empty +
        ("noWordSep" -> """_'?⇩\^<>""") +
        ("unalignedOpenBrackets" -> "{[(«‹⟨⌈⌊⦇⟦⦃⦉") +
        ("unalignedCloseBrackets" -> "⦊⦄⟧⦈⌋⌉⟩›»)]}") +
        ("tabSize" -> "2") +
        ("indentSize" -> "2")

    val list: List[Mode] =
    {
      val isabelle_news: Mode = init.define("isabelle-news", "Isabelle NEWS")

      val isabelle: Mode =
        init.define("isabelle", "Isabelle theory") +
          ("commentStart" -> "(*") +
          ("commentEnd" -> "*)")

      val isabelle_ml: Mode = isabelle.define("isabelle-ml", "Isabelle/ML")

      val isabelle_root: Mode = isabelle.define("isabelle-root", "Isabelle session root")

      val isabelle_options: Mode = isabelle.define("isabelle-options", "Isabelle options")

      val sml: Mode =
        init.define("sml", "Standard ML") +
          ("commentStart" -> "(*") +
          ("commentEnd" -> "*)") +
          ("noWordSep" -> "_'")

      List(isabelle_news, isabelle, isabelle_ml, isabelle_root, isabelle_options, sml)
    }
  }

  final case class Mode private(name: String, description: String, rev_props: Properties.T)
  {
    override def toString: String = name

    def define(a: String, b: String): Mode = new Mode(a, b, rev_props)

    def + (entry: Properties.Entry): Mode =
      new Mode(name, description, Properties.put(rev_props, entry))

    def write(dir: Path): Unit =
    {
      require(name.nonEmpty && description.nonEmpty, "Bad Isabelle/jEdit mode content")

      val properties =
        rev_props.reverse.map(p =>
          Symbol.spaces(4) +
          XML.string_of_tree(XML.elem(Markup("PROPERTY", List("NAME" -> p._1, "VALUE" -> p._2)))))

      File.write(dir + Path.basic(name).xml,
"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE MODE SYSTEM "xmode.dtd">

<!-- """ + XML.text(description) + """ mode -->
<MODE>
  <PROPS>""" + properties.mkString("\n", "\n", "\n") + """
  </PROPS>
</MODE>
""")
    }
  }


  /* build jEdit component */

  private val download_jars: List[(String, String)] =
    List(
      "https://repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2/jsr305-3.0.2.jar" ->
      "jsr305-3.0.2.jar")

  private val download_plugins: List[(String, String)] =
    List(
      "Code2HTML" -> "0.7",
      "CommonControls" -> "1.7.4",
      "Console" -> "5.1.4",
      "ErrorList" -> "2.4.0",
      "Highlight" -> "2.2",
      "Navigator" -> "2.7",
      "SideKick" -> "1.8")

  def build_jedit(
    component_dir: Path,
    version: String,
    original: Boolean = false,
    java_home: Path = default_java_home,
    progress: Progress = new Progress): Unit =
  {
    Isabelle_System.require_command("ant", test = "-version")
    Isabelle_System.require_command("patch")
    Isabelle_System.require_command("unzip", test = "-h")

    Isabelle_System.new_directory(component_dir)


    /* jEdit directory */

    val jedit = "jedit" + version
    val jedit_patched = jedit + "-patched"

    val jedit_dir = Isabelle_System.make_directory(component_dir + Path.basic(jedit))
    val jedit_patched_dir = component_dir + Path.basic(jedit_patched)

    def download_jedit(dir: Path, name: String, target_name: String = ""): Path =
    {
      val jedit_name = jedit + name
      val url =
        "https://sourceforge.net/projects/jedit/files/jedit/" +
          version + "/" + jedit_name + "/download"
      val path = dir + Path.basic(proper_string(target_name) getOrElse jedit_name)
      Isabelle_System.download_file(url, path, progress = progress)
      path
    }

    Isabelle_System.with_tmp_dir("tmp")(tmp_dir =>
    {
      /* original version */

      val install_path = download_jedit(tmp_dir, "install.jar")
      Isabelle_System.bash("""export CLASSPATH=""
isabelle_java java -Duser.home=""" + File.bash_platform_path(tmp_dir) +
        " -jar " + File.bash_platform_path(install_path) + " auto " +
        File.bash_platform_path(jedit_dir) + " unix-script=off unix-man=off").check

      val source_path = download_jedit(tmp_dir, "source.tar.bz2")
      Isabelle_System.gnutar("-xjf " + File.bash_path(source_path), dir = jedit_dir).check


      /* patched version */

      Isabelle_System.copy_dir(jedit_dir, jedit_patched_dir)

      val source_dir = jedit_patched_dir + Path.basic("jEdit")
      val tmp_source_dir = tmp_dir + Path.basic("jEdit")

      progress.echo("Patching jEdit sources ...")
      for {
        file <- File.find_files(Path.explode("~~/src/Tools/jEdit/patches").file).iterator
        name = file.getName
        if !name.endsWith("~") && !name.endsWith(".orig")
      } {
        progress.bash("patch -p2 < " + File.bash_path(File.path(file)),
          cwd = source_dir.file, echo = true).check
      }

      for { theme <- List("classic", "tango") } {
        val path = Path.explode("org/gjt/sp/jedit/icons/themes/" + theme + "/32x32/apps/isabelle.gif")
        Isabelle_System.copy_file(Path.explode("~~/lib/logo/isabelle_transparent-32.gif"),
          source_dir + path)
      }

      progress.echo("Building jEdit ...")
      Isabelle_System.copy_dir(source_dir, tmp_source_dir)
      progress.bash("env JAVA_HOME=" + File.bash_platform_path(java_home) + " ant",
        cwd = tmp_source_dir.file, echo = true).check
      Isabelle_System.copy_file(tmp_source_dir + Path.explode("build/jedit.jar"), jedit_patched_dir)
    })


    /* jars */

    val jars_dir = Isabelle_System.make_directory(jedit_patched_dir + Path.basic("jars"))

    for { (url, name) <- download_jars } {
      Isabelle_System.download_file(url, jars_dir + Path.basic(name), progress = progress)
    }

    for { (name, vers) <- download_plugins } {
      Isabelle_System.with_tmp_file("tmp", ext = "zip")(zip_path =>
      {
        val url =
          "https://sourceforge.net/projects/jedit-plugins/files/" + name + "/" + vers + "/" +
            name + "-" + vers + "-bin.zip/download"
        Isabelle_System.download_file(url, zip_path, progress = progress)
        Isabelle_System.bash("unzip -x " + File.bash_path(zip_path), cwd = jars_dir.file).check
      })
    }


    /* resources */

    File.write(jedit_patched_dir + Path.explode("properties/jEdit.props"),
"""#jEdit properties
autoReloadDialog=false
buffer.deepIndent=false
buffer.encoding=UTF-8-Isabelle
buffer.indentSize=2
buffer.lineSeparator=\n
buffer.maxLineLen=100
buffer.noTabs=true
buffer.sidekick.keystroke-parse=false
buffer.tabSize=2
buffer.undoCount=1000
close-docking-area.shortcut2=C+e C+CIRCUMFLEX
complete-word.shortcut=
console.dock-position=floating
console.encoding=UTF-8
console.font=Isabelle DejaVu Sans Mono
console.fontsize=14
delete-line.shortcut=A+d
delete.shortcut2=C+d
encoding.opt-out.Big5-HKSCS=true
encoding.opt-out.Big5=true
encoding.opt-out.COMPOUND_TEXT=true
encoding.opt-out.EUC-JP=true
encoding.opt-out.EUC-KR=true
encoding.opt-out.GB2312=true
encoding.opt-out.GB18030=true
encoding.opt-out.GBK=true
encoding.opt-out.IBM-Thai=true
encoding.opt-out.IBM00858=true
encoding.opt-out.IBM037=true
encoding.opt-out.IBM01140=true
encoding.opt-out.IBM01141=true
encoding.opt-out.IBM01142=true
encoding.opt-out.IBM01143=true
encoding.opt-out.IBM01144=true
encoding.opt-out.IBM01145=true
encoding.opt-out.IBM01146=true
encoding.opt-out.IBM01147=true
encoding.opt-out.IBM01148=true
encoding.opt-out.IBM01149=true
encoding.opt-out.IBM273=true
encoding.opt-out.IBM277=true
encoding.opt-out.IBM278=true
encoding.opt-out.IBM280=true
encoding.opt-out.IBM284=true
encoding.opt-out.IBM285=true
encoding.opt-out.IBM297=true
encoding.opt-out.IBM420=true
encoding.opt-out.IBM424=true
encoding.opt-out.IBM437=true
encoding.opt-out.IBM500=true
encoding.opt-out.IBM775=true
encoding.opt-out.IBM850=true
encoding.opt-out.IBM852=true
encoding.opt-out.IBM855=true
encoding.opt-out.IBM857=true
encoding.opt-out.IBM860=true
encoding.opt-out.IBM861=true
encoding.opt-out.IBM862=true
encoding.opt-out.IBM863=true
encoding.opt-out.IBM864=true
encoding.opt-out.IBM865=true
encoding.opt-out.IBM866=true
encoding.opt-out.IBM868=true
encoding.opt-out.IBM869=true
encoding.opt-out.IBM870=true
encoding.opt-out.IBM871=true
encoding.opt-out.IBM918=true
encoding.opt-out.IBM1026=true
encoding.opt-out.IBM1047=true
encoding.opt-out.ISO-2022-CN=true
encoding.opt-out.ISO-2022-JP-2=true
encoding.opt-out.ISO-2022-JP=true
encoding.opt-out.ISO-2022-KR=true
encoding.opt-out.ISO-8859-2=true
encoding.opt-out.ISO-8859-3=true
encoding.opt-out.ISO-8859-4=true
encoding.opt-out.ISO-8859-5=true
encoding.opt-out.ISO-8859-6=true
encoding.opt-out.ISO-8859-7=true
encoding.opt-out.ISO-8859-8=true
encoding.opt-out.ISO-8859-9=true
encoding.opt-out.ISO-8859-13=true
encoding.opt-out.JIS_X0201=true
encoding.opt-out.JIS_X0212-1990=true
encoding.opt-out.KOI8-R=true
encoding.opt-out.KOI8-U=true
encoding.opt-out.Shift_JIS=true
encoding.opt-out.TIS-620=true
encoding.opt-out.UTF-16=true
encoding.opt-out.UTF-16BE=true
encoding.opt-out.UTF-16LE=true
encoding.opt-out.UTF-32=true
encoding.opt-out.UTF-32BE=true
encoding.opt-out.UTF-32LE=true
encoding.opt-out.X-UTF-32BE-BOM=true
encoding.opt-out.X-UTF-32LE-BOM=true
encoding.opt-out.windows-31j=true
encoding.opt-out.windows-1250=true
encoding.opt-out.windows-1251=true
encoding.opt-out.windows-1253=true
encoding.opt-out.windows-1254=true
encoding.opt-out.windows-1255=true
encoding.opt-out.windows-1256=true
encoding.opt-out.windows-1257=true
encoding.opt-out.windows-1258=true
encoding.opt-out.x-Big5-Solaris=true
encoding.opt-out.x-EUC-TW=true
encoding.opt-out.x-IBM737=true
encoding.opt-out.x-IBM834=true
encoding.opt-out.x-IBM856=true
encoding.opt-out.x-IBM874=true
encoding.opt-out.x-IBM875=true
encoding.opt-out.x-IBM921=true
encoding.opt-out.x-IBM922=true
encoding.opt-out.x-IBM930=true
encoding.opt-out.x-IBM933=true
encoding.opt-out.x-IBM935=true
encoding.opt-out.x-IBM937=true
encoding.opt-out.x-IBM939=true
encoding.opt-out.x-IBM942=true
encoding.opt-out.x-IBM942C=true
encoding.opt-out.x-IBM943=true
encoding.opt-out.x-IBM943C=true
encoding.opt-out.x-IBM948=true
encoding.opt-out.x-IBM949=true
encoding.opt-out.x-IBM949C=true
encoding.opt-out.x-IBM950=true
encoding.opt-out.x-IBM964=true
encoding.opt-out.x-IBM970=true
encoding.opt-out.x-IBM1006=true
encoding.opt-out.x-IBM1025=true
encoding.opt-out.x-IBM1046=true
encoding.opt-out.x-IBM1097=true
encoding.opt-out.x-IBM1098=true
encoding.opt-out.x-IBM1112=true
encoding.opt-out.x-IBM1122=true
encoding.opt-out.x-IBM1123=true
encoding.opt-out.x-IBM1124=true
encoding.opt-out.x-IBM1381=true
encoding.opt-out.x-IBM1383=true
encoding.opt-out.x-IBM33722=true
encoding.opt-out.x-ISCII91=true
encoding.opt-out.x-ISO-2022-CN-CNS=true
encoding.opt-out.x-ISO-2022-CN-GB=true
encoding.opt-out.x-JIS0208=true
encoding.opt-out.x-JISAutoDetect=true
encoding.opt-out.x-Johab=true
encoding.opt-out.x-MS932_0213=true
encoding.opt-out.x-MS950-HKSCS=true
encoding.opt-out.x-MacArabic=true
encoding.opt-out.x-MacCentralEurope=true
encoding.opt-out.x-MacCroatian=true
encoding.opt-out.x-MacCyrillic=true
encoding.opt-out.x-MacDingbat=true
encoding.opt-out.x-MacGreek=true
encoding.opt-out.x-MacHebrew=true
encoding.opt-out.x-MacIceland=true
encoding.opt-out.x-MacRoman=true
encoding.opt-out.x-MacRomania=true
encoding.opt-out.x-MacSymbol=true
encoding.opt-out.x-MacThai=true
encoding.opt-out.x-MacTurkish=true
encoding.opt-out.x-MacUkraine=true
encoding.opt-out.x-PCK=true
encoding.opt-out.x-SJIS_0213=true
encoding.opt-out.x-UTF-16LE-BOM=true
encoding.opt-out.x-euc-jp-linux=true
encoding.opt-out.x-eucJP-Open=true
encoding.opt-out.x-iso-8859-11=true
encoding.opt-out.x-mswin-936=true
encoding.opt-out.x-windows-874=true
encoding.opt-out.x-windows-949=true
encoding.opt-out.x-windows-950=true
encoding.opt-out.x-windows-50220=true
encoding.opt-out.x-windows-50221=true
encoding.opt-out.x-windows-iso2022jp=true
encodingDetectors=BOM XML-PI buffer-local-property
end.shortcut=
expand-abbrev.shortcut2=CA+SPACE
expand-folds.shortcut=
fallbackEncodings=UTF-8 ISO-8859-15 US-ASCII
firstTime=false
focus-buffer-switcher.shortcut2=A+CIRCUMFLEX
foldPainter=Circle
gatchan.highlight.overview=false
helpviewer.font=Isabelle DejaVu Serif
helpviewer.fontsize=12
home.shortcut=
hypersearch-results.dock-position=right
insert-newline-indent.shortcut=
insert-newline.shortcut=
isabelle-debugger.dock-position=floating
isabelle-documentation.dock-position=left
isabelle-export-browser.label=Browse theory exports
isabelle-output.dock-position=bottom
isabelle-output.height=174
isabelle-output.width=412
isabelle-query.dock-position=bottom
isabelle-session-browser.label=Browse session information
isabelle-simplifier-trace.dock-position=floating
isabelle-sledgehammer.dock-position=bottom
isabelle-state.dock-position=right
isabelle-symbols.dock-position=bottom
isabelle-theories.dock-position=right
isabelle.antiquoted_cartouche.label=Make antiquoted cartouche
isabelle.complete-word.label=Complete word
isabelle.complete.label=Complete Isabelle text
isabelle.complete.shortcut2=C+b
isabelle.control-bold.label=Control bold
isabelle.control-bold.shortcut=C+e RIGHT
isabelle.control-emph.label=Control emphasized
isabelle.control-emph.shortcut=C+e LEFT
isabelle.control-reset.label=Control reset
isabelle.control-reset.shortcut=C+e BACK_SPACE
isabelle.control-sub.label=Control subscript
isabelle.control-sub.shortcut=C+e DOWN
isabelle.control-sup.label=Control superscript
isabelle.control-sup.shortcut=C+e UP
isabelle.decrease-font-size.label=Decrease font size
isabelle.decrease-font-size.shortcut2=C+SUBTRACT
isabelle.decrease-font-size.shortcut=C+MINUS
isabelle.decrease-font-size2.label=Decrease font size (clone)
isabelle.draft.label=Show draft in browser
isabelle.exclude-word-permanently.label=Exclude word permanently
isabelle.exclude-word.label=Exclude word
isabelle.first-error.label=Go to first error
isabelle.first-error.shortcut=CS+a
isabelle.goto-entity.label=Go to definition of formal entity at caret
isabelle.goto-entity.shortcut=CS+d
isabelle.include-word-permanently.label=Include word permanently
isabelle.include-word.label=Include word
isabelle.increase-font-size.label=Increase font size
isabelle.increase-font-size.shortcut2=C+ADD
isabelle.increase-font-size.shortcut=C+PLUS
isabelle.increase-font-size2.label=Increase font size (clone)
isabelle.increase-font-size2.shortcut=C+EQUALS
isabelle.java-monitor.label=Java/VM monitor
isabelle.last-error.label=Go to last error
isabelle.last-error.shortcut=CS+z
isabelle.message.label=Show message
isabelle.message.shortcut=CS+m
isabelle.newline.label=Newline with indentation of Isabelle keywords
isabelle.newline.shortcut=ENTER
isabelle.next-error.label=Go to next error
isabelle.next-error.shortcut=CS+n
isabelle.options.label=Isabelle options
isabelle.prev-error.label=Go to previous error
isabelle.prev-error.shortcut=CS+p
isabelle.preview.label=Show preview in browser
isabelle.reset-continuous-checking.label=Reset continuous checking
isabelle.reset-font-size.label=Reset font size
isabelle.reset-node-required.label=Reset node required
isabelle.reset-words.label=Reset non-permanent words
isabelle.select-entity.label=Select all occurences of formal entity at caret
isabelle.select-entity.shortcut=CS+ENTER
isabelle.set-continuous-checking.label=Set continuous checking
isabelle.set-node-required.label=Set node required
isabelle.toggle-breakpoint.label=Toggle Breakpoint
isabelle.toggle-continuous-checking.label=Toggle continuous checking
isabelle.toggle-continuous-checking.shortcut=C+e ENTER
isabelle.toggle-node-required.label=Toggle node required
isabelle.toggle-node-required.shortcut=C+e SPACE
isabelle.tooltip.label=Show tooltip
isabelle.tooltip.shortcut=CS+b
isabelle.update-state.label=Update state output
isabelle.update-state.shortcut=S+ENTER
lang.usedefaultlocale=false
largefilemode=full
line-end.shortcut=END
line-home.shortcut=HOME
logo.icon.medium=32x32/apps/isabelle.gif
lookAndFeel=com.formdev.flatlaf.FlatLightLaf
match-bracket.shortcut2=C+9
metal.primary.font=Isabelle DejaVu Sans
metal.primary.fontsize=12
metal.secondary.font=Isabelle DejaVu Sans
metal.secondary.fontsize=12
navigator.showOnToolbar=true
new-file-in-mode.shortcut=
next-bracket.shortcut2=C+e C+9
options.shortcuts.deletekeymap.label=Delete
options.shortcuts.duplicatekeymap.dialog.title=Keymap name
options.shortcuts.duplicatekeymap.label=Duplicate
options.shortcuts.resetkeymap.dialog.title=Reset keymap
options.shortcuts.resetkeymap.label=Reset
options.textarea.lineSpacing=1
plugin-blacklist.MacOSX.jar=true
plugin.MacOSXPlugin.altDispatcher=false
plugin.MacOSXPlugin.disableOption=true
prev-bracket.shortcut2=C+e C+8
print.font=Isabelle DejaVu Sans Mono
print.glyphVector=true
recent-buffer.shortcut2=C+CIRCUMFLEX
restore.remote=false
restore=false
search.subdirs.toggle=true
select-block.shortcut2=C+8
sidekick-tree.dock-position=right
sidekick.auto-complete-popup-get-focus=true
sidekick.buffer-save-parse=true
sidekick.complete-delay=0
sidekick.complete-instant.toggle=false
sidekick.complete-popup.accept-characters=\\t
sidekick.complete-popup.insert-characters=
sidekick.persistentFilter=true
sidekick.showFilter=true
sidekick.splitter.location=721
systrayicon=false
tip.show=false
toggle-full-screen.shortcut2=S+F11
toggle-multi-select.shortcut2=C+NUMBER_SIGN
toggle-rect-select.shortcut2=A+NUMBER_SIGN
twoStageSave=false
vfs.browser.dock-position=left
vfs.favorite.0.type=1
vfs.favorite.0=$ISABELLE_HOME
vfs.favorite.1.type=1
vfs.favorite.1=$ISABELLE_HOME_USER
vfs.favorite.2.type=1
vfs.favorite.2=$JEDIT_HOME
vfs.favorite.3.type=1
vfs.favorite.3=$JEDIT_SETTINGS
vfs.favorite.4.type=1
vfs.favorite.4=isabelle-export:
vfs.favorite.5.type=1
vfs.favorite.5=isabelle-session:
view.antiAlias=subpixel HRGB
view.blockCaret=true
view.caretBlink=false
view.docking.framework=PIDE
view.eolMarkers=false
view.extendedState=0
view.font=Isabelle DejaVu Sans Mono
view.fontsize=18
view.fracFontMetrics=false
view.gutter.font=Isabelle DejaVu Sans Mono
view.gutter.fontsize=12
view.gutter.lineNumbers=false
view.gutter.selectionAreaWidth=18
view.height=850
view.middleMousePaste=true
view.showToolbar=true
view.status.memory.background=#666699
view.status=( mode , fold , encoding ) locked wrap multiSelect rectSelect overwrite lineSep buffersets task-monitor java-status ml-status errors clock
view.thickCaret=true
view.width=1200
xml-insert-closing-tag.shortcut=
""")

    val modes_dir = jedit_patched_dir + Path.basic("modes")

    Mode.list.foreach(_.write(modes_dir))

    File.change_lines(modes_dir + Path.basic("catalog"),
      _.flatMap(line =>
          if (line.containsSlice("FILE=\"ml.xml\"") ||
            line.containsSlice("FILE_NAME_GLOB=\"*.{sml,ml}\"") ||
            line.containsSlice("FILE_NAME_GLOB=\"*.ftl\"")) Nil
          else if (line.containsSlice("NAME=\"jamon\"")) {
            List(
              """<MODE NAME="isabelle" FILE="isabelle.xml" FILE_NAME_GLOB="{*.thy,ROOT0.ML,ROOT.ML}"/>""",
              "",
              """<MODE NAME="isabelle-ml" FILE="isabelle-ml.xml" FILE_NAME_GLOB="*.ML"/>""",
              "",
              """<MODE NAME="isabelle-news" FILE="isabelle-news.xml"/>""",
              "",
              """<MODE NAME="isabelle-options" FILE="isabelle-options.xml"/>""",
              "",
              """<MODE NAME="isabelle-root" FILE="isabelle-root.xml" FILE_NAME_GLOB="ROOT"/>""",
              "",
              line)
          }
          else if (line.containsSlice("NAME=\"sqr\"")) {
            List(
              """<MODE NAME="sml" FILE="sml.xml" FILE_NAME_GLOB="*.{sml,sig}"/>""",
              "",
              line)
          }
          else List(line)))


    /* doc */

    val doc_dir = jedit_patched_dir + Path.basic("doc")

    download_jedit(doc_dir, "manual-a4.pdf", target_name = "jedit-manual.pdf")

    Isabelle_System.copy_file(
      doc_dir + Path.basic("CHANGES.txt"), doc_dir + Path.basic("jedit-changes"))

    File.write(doc_dir + Path.basic("Contents"),
"""Original jEdit Documentation
  jedit-manual    jEdit User's Guide
  jedit-changes   jEdit Version History

""")


    /* diff */

    Isabelle_System.bash(
      "diff -ru " + Bash.string(jedit) + " " + Bash.string(jedit_patched) +
        " > " + Bash.string(jedit + ".patch"),
      cwd = component_dir.file).check_rc(_ <= 1)

    if (!original) Isabelle_System.rm_tree(jedit_dir)


    /* etc */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.explode("etc"))

    File.write(etc_dir + Path.explode("settings"),
      """# -*- shell-script -*- :mode=shellscript:

ISABELLE_JEDIT_BUILD_HOME="$COMPONENT"
ISABELLE_JEDIT_BUILD_VERSION=""" + quote(jedit_patched) + """
""")


    /* README */

    File.write(component_dir + Path.basic("README"),
"""This is a slightly patched version of jEdit """ + version + """ from
https://sourceforge.net/projects/jedit/files/jedit with some
additional plugins jars from
https://sourceforge.net/projects/jedit-plugins/files


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }



  /** Isabelle tool wrappers **/

  val default_version = "5.6.0"
  def default_java_home: Path = Path.explode("$JAVA_HOME").expand

  val isabelle_tool =
    Isabelle_Tool("build_jedit", "build auxiliary jEdit component", Scala_Project.here, args =>
    {
      var target_dir = Path.current
      var java_home = default_java_home
      var original = false
      var version = default_version

      val getopts = Getopts("""
Usage: isabelle build_jedit [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -J JAVA_HOME Java version for building jedit.jar (e.g. version 11)
    -O           retain copy of original jEdit directory
    -V VERSION   jEdit version (default: """ + quote(default_version) + """)

  Build auxiliary jEdit component from original sources, with some patches.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "J:" -> (arg => java_home = Path.explode(arg)),
        "O" -> (arg => original = true),
        "V:" -> (arg => version = arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val component_dir =
        target_dir + Path.basic("jedit_build-" + Date.Format.alt_date(Date.now()))

      val progress = new Console_Progress()

      build_jedit(component_dir, version, original = original,
        java_home = java_home, progress = progress)
    })
}
