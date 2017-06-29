# Isabelle Prover IDE support

This extension connects to the Isabelle Prover IDE infrastructure, using the
VSCode Language Server protocol. This requires a recent development version of
Isabelle from 2017, see also:

  * <http://isabelle.in.tum.de/devel/release_snapshot>
  * <http://isabelle.in.tum.de/repos/isabelle/file/tip/src/Tools/VSCode>


## Prerequisites ##

### Important User Settings ###

  * On Linux and Mac OS X: `isabelle.home` points to the main Isabelle
    directory (`$ISABELLE_HOME`).

  * On Windows: `isabelle.home` as above, but in Windows path notation with
    drive-letter and backslashes.

### Support for Isabelle symbols ###

Isabelle symbols like `\<forall>` are rendered using the extension "Prettify
Symbols Mode", which needs to be installed separately.

In addition, the following user settings should be changed:

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


## Further Preferences ##

  * Preferred Color Theme: `Light+ (default light)`

  * Alternative Color Theme: `Dark+ (default dark)` – with restrictions: some color
    combinations don't work out properly.

  * Recommended changes to default VSCode settings:

    ```
    "editor.acceptSuggestionOnEnter": false
    "editor.lineNumbers": "off"
    "editor.rulers": [100]
    "editor.wordBasedSuggestions": true
    ```
