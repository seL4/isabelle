(function () {
    const vscode = acquireVsCodeApi();

    window.addEventListener("message", event => {
      const message = event.data;
      if (message.command === "update" && Array.isArray(message.sections)) {
        update(message.sections);
      }
    });

    function update(sections) {
      const container = document.getElementById("documentation-container");
      if (!container) return;
      container.innerHTML = "";

      vscode.setState({ sections: sections });

      const list = document.createElement("ul");
      list.classList.add("doc-list");

      let selected_entry = null;

      sections.forEach(section => {
        const section_item = document.createElement("li");
        section_item.classList.add("doc-section");

        const title_element = document.createElement("span");
        title_element.textContent = section.title;
        title_element.classList.add("section-title");

        const sub_list = document.createElement("ul");
        sub_list.classList.add("doc-sublist");
        sub_list.style.display = section.important ? "block" : "none";

        title_element.addEventListener("click", () => {
          sub_list.style.display = sub_list.style.display === "none" ? "block" : "none";
        });

        section.entries.forEach(entry => {
          const entry_item = document.createElement("li");
          entry_item.classList.add("doc-entry");

          const entry_link = document.createElement("a");
          entry_link.innerHTML = entry.print_html;
          entry_link.href = "#";
          entry_link.classList.add("doc-link");

          entry_link.addEventListener("click", event => {
            event.preventDefault();

            if (selected_entry && selected_entry !== entry_item) {
              selected_entry.classList.remove("selected");
            }

            if (selected_entry === entry_item) {
              selected_entry.classList.remove("selected");
              selected_entry = null;
            }
            else {
              selected_entry = entry_item;
              entry_item.classList.add("selected");
              open_document(entry.platform_path);
            }
          });

          entry_item.appendChild(entry_link);
          sub_list.appendChild(entry_item);
        });

        section_item.appendChild(title_element);
        section_item.appendChild(sub_list);
        list.appendChild(section_item);
      });

      container.appendChild(list);
    }

    function open_document(platform_path) {
      vscode.postMessage({ command: "open_document", platform_path: platform_path });
    }

    window.onload = function () {
        const state = vscode.getState();
        if (state && state.sections) {
          update(state.sections);
        }
      };
  })();
