# Isabelle Prover IDE support

This extension connects VSCode to the Isabelle Prover IDE infrastructure: it
requires Isabelle2021.

The implementation is centered around the VSCode Language Server protocol, but
with many add-ons that are specific to VSCode and Isabelle/PIDE.

See also:

  * <https://isabelle.in.tum.de/website-Isabelle2021>
  * <https://isabelle.in.tum.de/repos/isabelle/file/Isabelle2021/src/Tools/VSCode>
  * <https://github.com/Microsoft/language-server-protocol>


## Screenshot

![[Isabelle/VSCode]](https://isabelle.in.tum.de/repos/isabelle/raw-file/b565a39627bb/src/Tools/VSCode/extension/isabelle_vscode.png)


## Notable Features

  * Static syntax tables for Isabelle `.thy` and `.ML` files.

  * Implicit dependency management of sources, subject to changes of theory
  files within the editor, as well as external file-system events.

  * Implicit formal checking of theory files, using the *cursor position* of the
  active editor panel as indication for relevant spots.

  * Text overview lane with formal status of prover commands (unprocessed,
  running, error, warning).

  * Prover messages within the source text (errors/warnings and information
  messages).

  * Semantic text decorations: colors for free/bound variables, inferred types
  etc.

  * Visual indication of formal scopes and hyperlinks for formal entities.

  * Implicit proof state output via the VSCode message channel "Isabelle
  Output".

  * Explicit proof state output via separate GUI panel (command
  `isabelle.state`).

  * HTML preview via separate GUI panel (command `isabelle.preview`).

  * Rich completion information: Isabelle symbols (e.g. `\forall` or
  `\<forall>`), outer syntax keywords, formal entities, file-system paths,
  BibTeX entries etc.

  * Spell-checking of informal texts, including dictionary operations: via the
  regular completion dialog.


## Requirements

### Isabelle/VSCode Installation

  * Download Isabelle2021 from <https://isabelle.in.tum.de/website-Isabelle2021>
    or any of its mirror sites.

  * Unpack and run the main Isabelle/jEdit application as usual, to ensure that
  the logic image is built properly and Isabelle works as expected.

  * Download and install VSCode from <https://code.visualstudio.com>

  * Open the VSCode *Extensions* view and install the following:

      + *Isabelle2021* (needs to fit to the underlying Isabelle release).

      + *Prettify Symbols Mode* (important for display of Isabelle symbols).

      + *bibtexLanguage* (optional): it gives `.bib` a formal status, thus
        `@{cite}` antiquotations become active for completion and hyperlinks.

  * Open the dialog *Preferences / User settings* and provide the following
    entries in the second window, where local user additions are stored:

      + On all platforms: `isabelle.home` needs to point to the main Isabelle
      directory (`$ISABELLE_HOME`).

      + On Windows: use drive-letter and backslashes for `isabelle.home` above.
      When running from a bare repository clone (not a development snapshot),
      `isabelle.cygwin_home` needs to point to a suitable Cygwin installation.

    Examples:

      + Linux:
        ```
        "isabelle.home": "/home/makarius/Isabelle2021"
        ```

      + Mac OS X:
        ```
        "isabelle.home": "/Users/makarius/Isabelle.app/Isabelle2021"
        ```

      + Windows:
        ```
        "isabelle.home": "C:\\Users\\makarius\\Isabelle2021"
        ```

  * Restart the VSCode application to ensure that all extensions are properly
  initialized and user settings are updated. Afterwards VSCode should know about
  `.thy` files (Isabelle theories) and `.ML` files (Isabelle/ML modules).

  The Isabelle extension is initialized when the first Isabelle file is opened.
  It requires a few seconds to start up: a small popup window eventually says
  *"Welcome to Isabelle ..."*. If that fails, there might be something wrong
  with `isabelle.home` from above, or the Isabelle distribution does not fit to
  the version of the VSCode extension from the Marketplace.


### Support for Isabelle symbols

Isabelle symbols like `\<forall>` are rendered using the extension *Prettify
Symbols Mode*, which needs to be installed separately.

In addition, the following user settings should be changed in the *Preferences /
User settings* dialog of VSCode:

```
"prettifySymbolsMode.substitutions": [
  {
    "language": "isabelle",
    "revealOn": "none",
    "adjustCursorMovement": true,
    "prettyCursor": "none",
    "substitutions": []
  },
  {
    "language": "isabelle-ml",
    "revealOn": "none",
    "adjustCursorMovement": true,
    "prettyCursor": "none",
    "substitutions": []
  }]
```

Actual symbol replacement tables are provided by the prover process on startup,
based on the usual `etc/symbols` specifications of the Isabelle installation.


### Further Preferences

  * Preferred Color Theme: `Light+ (default light)`

  * Alternative Color Theme: `Dark+ (default dark)` – with restrictions: some
  color combinations don't work out properly.

  * Recommended changes to default VSCode settings:

    ```
    "editor.acceptSuggestionOnEnter": "off",
    "editor.lineNumbers": "off",
    "editor.renderIndentGuides": false,
    "editor.rulers": [80, 100],
    "editor.wordBasedSuggestions": true,
    ```

## Known Limitations of Isabelle/VSCode

  * Lack of specific support for the Isabelle fonts: these need to be
  manually installed on the system and configured for VSCode (see also
  `$ISABELLE_FONTS` within the Isabelle environment).

    **Note:** As the Isabelle fonts continue to evolve, installed versions need
    to be updated according to each new Isabelle version.

  * Isabelle symbols are merely an optical illusion: it would be better to make
    them a first-class Unicode charset as in Isabelle/jEdit.

  * Isabelle symbol abbreviations like "-->" are not accepted by VSCode.

  * Lack of formal editor perspective in VSCode: only the cursor position is
  used (with some surrounding lines of text).

  * Lack of formal markup in prover messages and popups.

  * Lack of pretty-printing (logical line breaks) according to window and font
  dimensions.

  * Lack of GUI panels for Sledgehammer, Query operations etc.

  * Big theory files may cause problems to the VSCode rendering engine, since
  messages and text decorations are applied to the text as a whole (cf. the
  minimap view).
