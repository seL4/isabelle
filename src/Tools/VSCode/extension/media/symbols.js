(function () {
  const vscode = acquireVsCodeApi();
  let allSymbols = {};
  let allAbbrevsFromThy = [];
  let controlSup = "";
  let controlSub = "";

  function decodeHtmlEntity(code) {
    try {
      return String.fromCodePoint(code);
    } catch (error) {
      return "?";
    }
  }

  function formatGroupName(group) {
    const groupNameMap = {
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

    return groupNameMap[group] || group.replace(/_/g, " ").replace(/\b\w/g, c => c.toUpperCase());
  }

  function createSearchField() {
    const searchContainer = document.createElement('div');
    searchContainer.classList.add('search-container');

    const searchInput = document.createElement('input');
    searchInput.type = "text";
    searchInput.classList.add('search-input');

    const searchResults = document.createElement('div');
    searchResults.classList.add('search-results');

    searchInput.addEventListener('input', () => filterSymbols(searchInput.value, searchResults));

    searchContainer.appendChild(searchInput);
    searchContainer.appendChild(searchResults);
    return { searchContainer, searchResults };
  }

  function filterSymbols(query, resultsContainer) {
    const normalizedQuery = query.toLowerCase().trim();
    resultsContainer.innerHTML = '';

    if (normalizedQuery === "") return;

    const matchingSymbols = [];
    Object.values(allSymbols).forEach(symbolList => {
      symbolList.forEach(symbol => {
        if (!symbol.code) return;

        if (
          symbol.symbol.toLowerCase().includes(normalizedQuery) ||
          (symbol.abbrevs && symbol.abbrevs.some(abbr => abbr.toLowerCase().includes(normalizedQuery)))
        ) {
          matchingSymbols.push(symbol);
        }
      });
    });

    const searchLimit = 50;
    if (matchingSymbols.length === 0) {
      resultsContainer.innerHTML = "<p>No symbols found</p>";
    } else {
      matchingSymbols.slice(0, searchLimit).forEach(symbol => {
        const decodedSymbol = decodeHtmlEntity(symbol.code);
        if (!decodedSymbol) return;

        const button = document.createElement('div');
        button.classList.add('symbol-button');
        button.textContent = decodedSymbol;
        button.setAttribute("data-tooltip", `${symbol.symbol}\nAbbreviations: ${symbol.abbrevs.join(', ')}`);

        button.addEventListener('click', () => {
          vscode.postMessage({ command: 'insertSymbol', symbol: decodedSymbol });
        });

        resultsContainer.appendChild(button);
      });

      if (matchingSymbols.length > searchLimit) {
        const moreResults = document.createElement('div');
        moreResults.classList.add('more-results');
        moreResults.textContent = `(${matchingSymbols.length - searchLimit} more...)`;
        resultsContainer.appendChild(moreResults);
      }
    }
  }

  function renderWithEffects(symbol) {
    if (!symbol) return "";

    let result = "";
    let i = 0;
    while (i < symbol.length) {
      const char = symbol[i];
      if (char === "⇧") {
        i++;
        if (i < symbol.length) result += "<sup>" + symbol[i] + "</sup>";
      } else if (char === "⇩") { 
        i++;
        if (i < symbol.length) result += "<sub>" + symbol[i] + "</sub>";
      } else {
        result += char;
      }
      i++;
    }
    return result;
  }

  function convertSymbolWithEffects(symbol) {
  let result = "";
  let i = 0;
  while (i < symbol.length) {
    const char = symbol[i];
    if (char === "⇧") {
      i++;
      if (i < symbol.length) {
        if (controlSup) result += controlSup + symbol[i];
        else result += symbol[i];
      }
    } else if (char === "⇩") {
      i++;
      if (i < symbol.length) {
        if (controlSub) result += controlSub + symbol[i];
        else result += symbol[i];
      }
    } else {
      result += char;
    }
    i++;
  }
  return result;
}

  function sanitizeSymbolForInsert(symbol) {
    return symbol.replace(/\u0007/g, '');
  }

  function extractControlSymbols(symbolGroups) {
    if (!symbolGroups || !symbolGroups["control"]) return;
    symbolGroups["control"].forEach(symbol => {
      if (symbol.name === "sup") controlSup = String.fromCodePoint(symbol.code);
      if (symbol.name === "sub") controlSub = String.fromCodePoint(symbol.code);
    });
  }

  function renderSymbols(groupedSymbols, abbrevsFromThy) {
    const container = document.getElementById('symbols-container');
    container.innerHTML = '';

    allSymbols = groupedSymbols;
    allAbbrevsFromThy = abbrevsFromThy || [];

    extractControlSymbols(groupedSymbols);

    vscode.setState({ symbols: groupedSymbols, abbrevs_from_Thy: allAbbrevsFromThy });

    if (!groupedSymbols || Object.keys(groupedSymbols).length === 0) {
      container.innerHTML = "<p>No symbols available.</p>";
      return;
    }

    const tabs = document.createElement('div');
    tabs.classList.add('tabs');

    const content = document.createElement('div');
    content.classList.add('content');

    Object.keys(groupedSymbols).forEach((group, index) => {
      const tab = document.createElement('button');
      tab.classList.add('tab');
      tab.textContent = formatGroupName(group);
      if (index === 0) tab.classList.add('active');

      tab.addEventListener('click', () => {
        document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
        tab.classList.add('active');
        document.querySelectorAll('.tab-content').forEach(c => c.classList.add('hidden'));
        document.getElementById(`content-${group}`).classList.remove('hidden');
      });

      tabs.appendChild(tab);

      const groupContent = document.createElement('div');
      groupContent.classList.add('tab-content');
      groupContent.id = `content-${group}`;
      if (index !== 0) groupContent.classList.add('hidden');

      if (group === "control") {
        const resetButton = document.createElement('button');
        resetButton.classList.add('reset-button');
        resetButton.textContent = "Reset";


        resetButton.addEventListener('click', () => {
          vscode.postMessage({ command: 'resetControlSymbols' });
        });
        groupContent.appendChild(resetButton);

        const controlButtons = ["sup", "sub", "bold"];
        controlButtons.forEach(action => {
          const controlSymbol = groupedSymbols[group].find(s => s.name === action);
          if (controlSymbol) {
            const decodedSymbol = decodeHtmlEntity(controlSymbol.code);
            const button = document.createElement('button');
            button.classList.add('control-button');
            button.textContent = decodedSymbol;
            button.title = action.charAt(0).toUpperCase() + action.slice(1);
            button.addEventListener('click', () => {
              vscode.postMessage({ command: 'applyControl', action: action });
            });
            groupContent.appendChild(button);
          }
        });
      }

      groupedSymbols[group].forEach(symbol => {
        if (!symbol.code) return;
        if (["sup", "sub", "bold"].includes(symbol.name)) return;
        const decodedSymbol = decodeHtmlEntity(symbol.code);
        if (!decodedSymbol) return;

        const button = document.createElement('div');
        if (group === "arrow") {
          button.classList.add('arrow-button'); // special class for arrows
        } else {
          button.classList.add('symbol-button');
        }
        button.textContent = decodedSymbol;
        button.setAttribute("data-tooltip", `${symbol.symbol}\nAbbreviations: ${symbol.abbrevs.join(', ')}`);

        button.addEventListener('click', () => {
          vscode.postMessage({ command: 'insertSymbol', symbol: decodedSymbol });
        });

        groupContent.appendChild(button);
      });

      content.appendChild(groupContent);
    });

    const abbrevsTab = document.createElement('button');
    abbrevsTab.classList.add('tab');
    abbrevsTab.textContent = "Abbrevs";
    abbrevsTab.addEventListener('click', () => {
      document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
      abbrevsTab.classList.add('active');
      document.querySelectorAll('.tab-content').forEach(c => c.classList.add('hidden'));
      document.getElementById("abbrevs-tab-content").classList.remove('hidden');
    });
    tabs.appendChild(abbrevsTab);

    const abbrevsContent = document.createElement('div');
    abbrevsContent.classList.add('tab-content', 'hidden');
    abbrevsContent.id = "abbrevs-tab-content";

    allAbbrevsFromThy
      .filter(([abbr, symbol]) => symbol && symbol.trim() !== "" && !/^[a-zA-Z0-9 _-]+$/.test(symbol)) 
      .forEach(([abbr, symbol]) => {
        const btn = document.createElement('div');
        btn.classList.add('abbrevs-button');
        btn.innerHTML = renderWithEffects(symbol); 
        btn.title = abbr;
        btn.addEventListener('click', () => {
          vscode.postMessage({ command: 'insertSymbol', symbol: convertSymbolWithEffects(sanitizeSymbolForInsert(symbol)) });
        });

        abbrevsContent.appendChild(btn);
      });

    content.appendChild(abbrevsContent);

    const searchTab = document.createElement('button');
    searchTab.classList.add('tab');
    searchTab.textContent = "Search";
    searchTab.addEventListener('click', () => {
      document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
      searchTab.classList.add('active');
      document.querySelectorAll('.tab-content').forEach(c => c.classList.add('hidden'));
      document.getElementById("search-tab-content").classList.remove('hidden');
    });
    tabs.appendChild(searchTab);

    const { searchContainer, searchResults } = createSearchField();
    const searchContent = document.createElement('div');
    searchContent.classList.add('tab-content', 'hidden');
    searchContent.id = "search-tab-content";
    searchContent.appendChild(searchContainer);

    content.appendChild(searchContent);
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

  window.addEventListener('message', event => {
    if (event.data.command === 'update' && event.data.symbols) {
      renderSymbols(event.data.symbols, event.data.abbrevs_from_Thy);
    }
  });

  window.onload = function () {
    const savedState = vscode.getState();
    if (savedState && savedState.symbols) {
      renderSymbols(savedState.symbols, savedState.abbrevs_from_Thy);
    }
  };

})();
