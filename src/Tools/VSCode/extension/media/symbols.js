(function () {
  const vscode = acquireVsCodeApi();
  let all_symbols = {};
  let all_abbrevs_from_thy = [];
  let control_sup = "";
  let control_sub = "";

  function decode_html_entity(code) {
    try {
      return String.fromCodePoint(code);
    } catch (error) {
      return "?";
    }
  }

  function format_group_name(group) {
    const group_name_map = {
      "Z_Notation": "Z Notation",
      "Control_Block": "Control Block",
      "Arrow": "Arrow",
      "Control": "Control",
      "Digit": "Digit",
      "Document": "Document",
      "Greek": "Greek",
      "Icon": "Icon",
      "Letter": "Letter",
      "Logic": "Logic",
      "Operator": "Operator",
      "Punctuation": "Punctuation",
      "Relation": "Relation",
      "Unsorted": "Unsorted",
      "Search": "Search"
    };

    return group_name_map[group] || group.replace(/_/g, " ").replace(/\b\w/g, c => c.toUpperCase());
  }

  function create_search_field() {
    const search_container = document.createElement("div");
    search_container.classList.add("search-container");

    const search_input = document.createElement("input");
    search_input.type = "text";
    search_input.classList.add("search-input");

    const search_results = document.createElement("div");
    search_results.classList.add("search-results");

    search_input.addEventListener("input", () => filterSymbols(search_input.value, search_results));

    search_container.appendChild(search_input);
    search_container.appendChild(search_results);
    return { search_container, search_results };
  }

  function filterSymbols(query, results_container) {
    const normalized_query = query.toLowerCase().trim();
    results_container.innerHTML = "";

    if (normalized_query === "") return;

    const matching_symbols = [];
    Object.values(all_symbols).forEach(symbolList => {
      symbolList.forEach(symbol => {
        if (!symbol.code) return;

        if (
          symbol.symbol.toLowerCase().includes(normalized_query) ||
          (symbol.abbrevs && symbol.abbrevs.some(abbr => abbr.toLowerCase().includes(normalized_query)))
        ) {
          matching_symbols.push(symbol);
        }
      });
    });

    const search_limit = 50;
    if (matching_symbols.length === 0) {
      results_container.innerHTML = "<p>No symbols found</p>";
    }
    else {
      matching_symbols.slice(0, search_limit).forEach(symbol => {
        const decoded_symbol = decode_html_entity(symbol.code);
        if (!decoded_symbol) return;

        const button = document.createElement("div");
        button.classList.add("symbol-button");
        button.textContent = decoded_symbol;
        button.setAttribute("data-tooltip", `${symbol.symbol}\nAbbreviations: ${symbol.abbrevs.join(", ")}`);

        button.addEventListener("click", () => {
          vscode.postMessage({ command: "insert_symbol", symbol: decoded_symbol });
        });

        results_container.appendChild(button);
      });

      if (matching_symbols.length > search_limit) {
        const more_results = document.createElement("div");
        more_results.classList.add("more-results");
        more_results.textContent = `(${matching_symbols.length - search_limit} more...)`;
        results_container.appendChild(more_results);
      }
    }
  }

  function render_with_effects(symbol) {
    if (!symbol) return "";

    let result = "";
    let i = 0;
    while (i < symbol.length) {
      const char = symbol[i];
      if (char === "\u21e7") {
        i++;
        if (i < symbol.length) result += "<sup>" + symbol[i] + "</sup>";
      }
      else if (char === "\u21e9") { 
        i++;
        if (i < symbol.length) result += "<sub>" + symbol[i] + "</sub>";
      }
      else {
        result += char;
      }
      i++;
    }
    return result;
  }

  function convert_symbol_with_effects(symbol) {
  let result = "";
  let i = 0;
  while (i < symbol.length) {
    const char = symbol[i];
    if (char === "\u21e7") {
      i++;
      if (i < symbol.length) {
        if (control_sup) result += control_sup + symbol[i];
        else result += symbol[i];
      }
    }
    else if (char === "\u21e9") {
      i++;
      if (i < symbol.length) {
        if (control_sub) result += control_sub + symbol[i];
        else result += symbol[i];
      }
    }
    else {
      result += char;
    }
    i++;
  }
  return result;
}

  function sanitize_symbol_for_insert(symbol) {
    return symbol.replace(/\u0007/g, "");
  }

  function extract_control_symbols(symbol_groups) {
    if (!symbol_groups || !symbol_groups["control"]) return;
    symbol_groups["control"].forEach(symbol => {
      if (symbol.name === "sup") control_sup = String.fromCodePoint(symbol.code);
      if (symbol.name === "sub") control_sub = String.fromCodePoint(symbol.code);
    });
  }

  function render_symbols(grouped_symbols, abbrevs_from_thy) {
    const container = document.getElementById("symbols-container");
    container.innerHTML = "";

    all_symbols = grouped_symbols;
    all_abbrevs_from_thy = abbrevs_from_thy || [];

    extract_control_symbols(grouped_symbols);

    vscode.setState({ symbols: grouped_symbols, abbrevs_from_Thy: all_abbrevs_from_thy });

    if (!grouped_symbols || Object.keys(grouped_symbols).length === 0) {
      container.innerHTML = "<p>No symbols available.</p>";
      return;
    }

    const tabs = document.createElement("div");
    tabs.classList.add("tabs");

    const content = document.createElement("div");
    content.classList.add("content");

    Object.keys(grouped_symbols).forEach((group, index) => {
      const tab = document.createElement("button");
      tab.classList.add("tab");
      tab.textContent = format_group_name(group);
      if (index === 0) tab.classList.add("active");

      tab.addEventListener("click", () => {
        document.querySelectorAll(".tab").forEach(t => t.classList.remove("active"));
        tab.classList.add("active");
        document.querySelectorAll(".tab-content").forEach(c => c.classList.add("hidden"));
        document.getElementById(`content-${group}`).classList.remove("hidden");
      });

      tabs.appendChild(tab);

      const group_content = document.createElement("div");
      group_content.classList.add("tab-content");
      group_content.id = `content-${group}`;
      if (index !== 0) group_content.classList.add("hidden");

      if (group === "control") {
        const reset_button = document.createElement("button");
        reset_button.classList.add("reset-button");
        reset_button.textContent = "Reset";

        reset_button.addEventListener("click", () => {
          vscode.postMessage({ command: "reset_control_symbols" });
        });
        group_content.appendChild(reset_button);

        const control_buttons = ["sup", "sub", "bold"];
        control_buttons.forEach(action => {
          const control_symbol = grouped_symbols[group].find(s => s.name === action);
          if (control_symbol) {
            const decoded_symbol = decode_html_entity(control_symbol.code);
            const button = document.createElement("button");
            button.classList.add("control-button");
            button.textContent = decoded_symbol;
            button.title = action.charAt(0).toUpperCase() + action.slice(1);
            button.addEventListener("click", () => {
              vscode.postMessage({ command: "apply_control", action: action });
            });
            group_content.appendChild(button);
          }
        });
      }

      grouped_symbols[group].forEach(symbol => {
        if (!symbol.code) return;
        if (["sup", "sub", "bold"].includes(symbol.name)) return;
        const decoded_symbol = decode_html_entity(symbol.code);
        if (!decoded_symbol) return;

        const button = document.createElement("div");
        if (group === "arrow") {
          button.classList.add("arrow-button"); // special class for arrows
        }
        else {
          button.classList.add("symbol-button");
        }
        button.textContent = decoded_symbol;
        button.setAttribute("data-tooltip", `${symbol.symbol}\nAbbreviations: ${symbol.abbrevs.join(", ")}`);

        button.addEventListener("click", () => {
          vscode.postMessage({ command: "insert_symbol", symbol: decoded_symbol });
        });

        group_content.appendChild(button);
      });

      content.appendChild(group_content);
    });

    const abbrevs_tab = document.createElement("button");
    abbrevs_tab.classList.add("tab");
    abbrevs_tab.textContent = "Abbrevs";
    abbrevs_tab.addEventListener("click", () => {
      document.querySelectorAll(".tab").forEach(t => t.classList.remove("active"));
      abbrevs_tab.classList.add("active");
      document.querySelectorAll(".tab-content").forEach(c => c.classList.add("hidden"));
      document.getElementById("abbrevs-tab-content").classList.remove("hidden");
    });
    tabs.appendChild(abbrevs_tab);

    const abbrevs_content = document.createElement("div");
    abbrevs_content.classList.add("tab-content", "hidden");
    abbrevs_content.id = "abbrevs-tab-content";

    all_abbrevs_from_thy
      .filter(([abbr, symbol]) => symbol && symbol.trim() !== "" && !/^[a-zA-Z0-9 _-]+$/.test(symbol)) 
      .forEach(([abbr, symbol]) => {
        const btn = document.createElement("div");
        btn.classList.add("abbrevs-button");
        btn.innerHTML = render_with_effects(symbol); 
        btn.title = abbr;
        btn.addEventListener("click", () => {
          vscode.postMessage({ command: "insert_symbol", symbol: convert_symbol_with_effects(sanitize_symbol_for_insert(symbol)) });
        });

        abbrevs_content.appendChild(btn);
      });

    content.appendChild(abbrevs_content);

    const search_tab = document.createElement("button");
    search_tab.classList.add("tab");
    search_tab.textContent = "Search";
    search_tab.addEventListener("click", () => {
      document.querySelectorAll(".tab").forEach(t => t.classList.remove("active"));
      search_tab.classList.add("active");
      document.querySelectorAll(".tab-content").forEach(c => c.classList.add("hidden"));
      document.getElementById("search-tab-content").classList.remove("hidden");
    });
    tabs.appendChild(search_tab);

    const { search_container, search_results } = create_search_field();
    const search_content = document.createElement("div");
    search_content.classList.add("tab-content", "hidden");
    search_content.id = "search-tab-content";
    search_content.appendChild(search_container);

    content.appendChild(search_content);
    container.appendChild(tabs);
    container.appendChild(content);

    const tooltip = document.createElement("div");
    tooltip.className = "tooltip";
    document.body.appendChild(tooltip);

    document.querySelectorAll(".symbol-button, .arrow-button, .abbrevs-button").forEach(button => {
       button.addEventListener("mouseenter", (e) => {
       const rect = button.getBoundingClientRect();
       const text = button.getAttribute("data-tooltip");

       if (text) {
        tooltip.textContent = text;
        tooltip.style.left = `${rect.left + window.scrollX}px`;
        tooltip.style.top = `${rect.bottom + 6 + window.scrollY}px`;
        tooltip.classList.add("visible");
       }
       });

       button.addEventListener("mouseleave", () => {
       tooltip.classList.remove("visible");
       tooltip.textContent = "";
       });
    });

  }

  window.addEventListener("message", event => {
    if (event.data.command === "update" && event.data.symbols) {
      render_symbols(event.data.symbols, event.data.abbrevs_from_Thy);
    }
  });

  window.onload = function () {
    const state = vscode.getState();
    if (state && state.symbols) {
      render_symbols(state.symbols, state.abbrevs_from_Thy);
    }
  };

})();
