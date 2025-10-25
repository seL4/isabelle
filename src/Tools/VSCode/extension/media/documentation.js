(function () {
    const vscode = acquireVsCodeApi();

    window.addEventListener("message", event => {
      const message = event.data;

      if (message.command === "update" && Array.isArray(message.sections)) {
        renderDocumentation(message.sections);
      }
    });

    function renderDocumentation(sections) {
      const container = document.getElementById("documentation-container");
      if (!container) return;
      container.innerHTML = "";

      vscode.setState({ sections: sections });

      const list = document.createElement("ul");
      list.classList.add("doc-list");

      let selectedEntry = null;

      sections.forEach(section => {
        const sectionItem = document.createElement("li");
        sectionItem.classList.add("doc-section");

        const titleElement = document.createElement("span");
        titleElement.textContent = section.title;
        titleElement.classList.add("section-title");

        const subList = document.createElement("ul");
        subList.classList.add("doc-sublist");
        subList.style.display = section.important ? "block" : "none";

        titleElement.addEventListener("click", () => {
          subList.style.display = subList.style.display === "none" ? "block" : "none";
        });

        section.entries.forEach(entry => {
          const entryItem = document.createElement("li");
          entryItem.classList.add("doc-entry");

          let cleanedPath = entry.path.replace(/["]/g, "");
          if (section.title.includes("Examples")) {
            cleanedPath = cleanedPath.replace(/^.*?src\//, "src/");
          }
          if (section.title.includes("Release Notes")) {
            cleanedPath = cleanedPath.replace(/^\$ISABELLE_HOME\//, "");
          }

          let displayText = cleanedPath;
          const match = cleanedPath.match(/([^\/]+?)(?:\.pdf)?$/);
          if (match) {
            const filename = match[1];
            const cleanTitle = entry.title.replace(/["']/g, "").trim();
            displayText = `<b>${filename}</b>${cleanTitle ? ': ' + cleanTitle : ''}`;
          }

          const entryLink = document.createElement("a");
          entryLink.innerHTML = displayText;
          entryLink.href = "#";
          entryLink.classList.add("doc-link");

          entryLink.addEventListener("click", event => {
            event.preventDefault();

            if (selectedEntry && selectedEntry !== entryItem) {
              selectedEntry.classList.remove("selected");
            }

            if (selectedEntry === entryItem) {
              selectedEntry.classList.remove("selected");
              selectedEntry = null;
            } else {
              selectedEntry = entryItem;
              entryItem.classList.add("selected");
              open_document(entry.path);
            }
          });

          entryItem.appendChild(entryLink);
          subList.appendChild(entryItem);
        });

        sectionItem.appendChild(titleElement);
        sectionItem.appendChild(subList);
        list.appendChild(sectionItem);
      });

      container.appendChild(list);
    }

    function open_document(path) {
      vscode.postMessage({ command: "open_document", path: path });
    }

    window.onload = function () {
        const savedState = vscode.getState();
        if (savedState && savedState.sections) {
          renderDocumentation(savedState.sections);
        }
      };
  })();
