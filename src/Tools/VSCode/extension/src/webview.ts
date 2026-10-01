/*  Author:     Fabian Huch

Base functionality for web views.
*/

"use strict";

import {Uri, Webview} from "vscode"

import * as Path from "path"

import * as Decorations from "./decorations"
import * as VSCode_Lib from "./vscode_lib"


const vscode_css = Path.join("media", "vscode.css")
const codicons_css = Path.join("node_modules", "@vscode", "codicons", "dist", "codicon.css")
const isabelle_font = Path.join("fonts", "IsabelleDejaVuSansMono.ttf")
function element_css(name: string) {
  return Path.join(
    "node_modules", "@vscode-elements", "elements-lite", "components", name, `${name}.css`)
}

export function get_html(
  webview: Webview,
  extension_path: string,
  title: string,
  script_name: string,
): string {
  function uri(path: string): Uri {
    return webview.asWebviewUri(Uri.file(Path.join(extension_path, path)))
  }
  const vscode_elements = ["action-button", "button", "checkbox", "label", "textfield"]

  return `<!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <link href="${uri(codicons_css)}" rel="stylesheet" type="text/css">
        ${vscode_elements.map(name =>
    `<link href="${uri(element_css(name))}" rel="stylesheet" type="text/css">`).join("\n") }
        <link href="${uri(vscode_css)}" rel="stylesheet" type="text/css">
        <style>
            @font-face {
                font-family: "Isabelle DejaVu Sans Mono";
                src: url(${uri(isabelle_font)});
            }
            ${_get_decorations()}
        </style>
        <title>${title}</title>
      </head>
      <body>
        <script type="module" src="${uri(Path.join("media", script_name))}"></script>
      </body>
    </html>`
}

function _get_decorations(): string {
  let style: string[] = []
  for (const key of Decorations.text_colors) {
    style.push(`body.vscode-light .${key} { color: ${VSCode_Lib.get_color(key, true)} }\n`)
    style.push(`body.vscode-dark .${key} { color: ${VSCode_Lib.get_color(key, false)} }\n`)
  }
  return style.join("")
}
