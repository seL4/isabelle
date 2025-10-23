(function () {
  const vscode = acquireVsCodeApi();
  let wasCancelled = false;
  let kannbeCancelled = false;

  let history = []; 

  const container = document.createElement('div');
  container.id = 'sledgehammer-container';

  const topRow = document.createElement('div');
  topRow.classList.add('top-row');

  const proversLabel = document.createElement('label');
  proversLabel.textContent = 'Provers: ';

  const proversInputWrapper = document.createElement('div');
  proversInputWrapper.className = 'provers-input-wrapper';

  const proversInput = document.createElement('input');
  proversInput.type = 'text';
  proversInput.id = 'provers';
  proversInput.size = 30;
  proversInput.value = '';
  proversInput.autocomplete = 'off';

  proversInputWrapper.appendChild(proversInput);

  const chevronBtn = document.createElement('button');
  chevronBtn.type = 'button';
  chevronBtn.className = 'provers-dropdown-toggle';
  chevronBtn.setAttribute('aria-label', 'Show provers history');
  chevronBtn.tabIndex = -1;
  chevronBtn.innerHTML = '\u25bc';
  proversInputWrapper.appendChild(chevronBtn);

  proversLabel.appendChild(proversInputWrapper);

  const dropdown = document.createElement('div');
  dropdown.className = 'provers-dropdown';
  proversInputWrapper.appendChild(dropdown);

  function showDropdown() {
    dropdown.classList.add('visible');
  }
  function hideDropdown() {
    dropdown.classList.remove('visible');
  }

  function renderDropdown(open = false) {
    dropdown.innerHTML = '';
    const header = document.createElement('div');
    header.textContent = 'Previously entered strings:';
    header.className = 'history-header';
    dropdown.appendChild(header);
    if (history.length === 0) {
      const noEntry = document.createElement('div');
      noEntry.className = 'history-header';
    } else {
      history.forEach(item => {
        const row = document.createElement('div');
        row.tabIndex = 0;
        row.textContent = item;

        const delBtn = document.createElement('span');
        delBtn.textContent = '\u2716';
        delBtn.className = 'delete-btn';
        delBtn.title = 'Delete entry';
        delBtn.addEventListener('mousedown', function (ev) {
          ev.preventDefault();
          ev.stopPropagation();
          history = history.filter(h => h !== item);
          renderDropdown(false);
          showDropdown();

          vscode.postMessage({
            command: 'delete_prover_history',
            entry: item
          });
        });

        row.appendChild(delBtn);
        row.addEventListener('mousedown', function (e) {
          e.preventDefault();
          proversInput.value = item;
          hideDropdown();
          proversInput.focus();
        });
        dropdown.appendChild(row);
      });
    }
    if (open) showDropdown(); else hideDropdown();
  }


  chevronBtn.addEventListener('mousedown', function (e) {
    e.preventDefault();
    if (dropdown.classList.contains('visible')) {
      hideDropdown();
    } else {
      renderDropdown(true);
      showDropdown();
      proversInput.focus();
    }
  });

  proversInput.addEventListener('input', () => { });

  proversInput.addEventListener('focus', function () {
    renderDropdown(true);
    showDropdown();
  });
  proversInput.addEventListener('blur', () => {
    setTimeout(() => {
      if (!dropdown.contains(document.activeElement)) hideDropdown();
    }, 150);
  });

  proversInput.addEventListener('keydown', (e) => {
    if (e.key === 'ArrowDown' && dropdown.childNodes.length) {
      dropdown.firstChild && dropdown.firstChild.focus && dropdown.firstChild.focus();
    }
  });

  function setHistory(newHistory) {
    history = Array.isArray(newHistory) ? newHistory : [];
    saveState();
    renderDropdown(false);
  }

  function saveState() {
    vscode.setState({
      history,
      provers: proversInput.value,
      isar: isarCheckbox.checked,
      try0: try0Checkbox.checked
    });
  }

  function addToHistory(entry) {
    if (!entry.trim()) return;
    history = [entry, ...history.filter((h) => h !== entry)].slice(0, 10);
    saveState();
    renderDropdown();
  }

  const isarLabel = document.createElement('label');
  const isarCheckbox = document.createElement('input');
  isarCheckbox.type = 'checkbox';
  isarCheckbox.id = 'isar';
  isarLabel.appendChild(isarCheckbox);
  isarLabel.appendChild(document.createTextNode(' Isar proofs'));

  const try0Label = document.createElement('label');
  const try0Checkbox = document.createElement('input');
  try0Checkbox.type = 'checkbox';
  try0Checkbox.id = 'try0';
  try0Checkbox.checked = true;
  try0Label.appendChild(try0Checkbox);
  try0Label.appendChild(document.createTextNode(' Try methods'));


  proversInput.addEventListener('input', saveState);
  isarCheckbox.addEventListener('change', saveState);
  try0Checkbox.addEventListener('change', saveState);
  const spinner = document.createElement('div');
  spinner.id = 'sledgehammer-spinner';

  const applyBtn = document.createElement('button');
  applyBtn.textContent = 'Apply';
  applyBtn.id = 'apply-btn';
  applyBtn.addEventListener('click', () => {
    wasCancelled = false;
    kannbeCancelled = true;
    result.innerHTML = '';
    addToHistory(proversInput.value); 
    hideDropdown();
    vscode.postMessage({
      command: 'apply',
      provers: proversInput.value,
      isar: isarCheckbox.checked,
      try0: try0Checkbox.checked
    });
  });

  const cancelBtn = document.createElement('button');
  cancelBtn.textContent = 'Cancel';
  cancelBtn.addEventListener('click', () => {
    vscode.postMessage({ command: 'cancel' });
    if (wasCancelled) return;
    if (!kannbeCancelled) return;
    wasCancelled = true;
    spinner.classList.remove('loading');
    const div = document.createElement("div");
    div.classList.add("interrupt");
    div.textContent = "Interrupt";
    result.appendChild(div);
  });

  const locateBtn = document.createElement('button');
  locateBtn.textContent = 'Locate';
  locateBtn.addEventListener('click', () => {
    vscode.postMessage({
      command: 'locate',
      provers: proversInput.value,
      isar: isarCheckbox.checked,
      try0: try0Checkbox.checked
    });
  });

  topRow.appendChild(proversLabel);
  topRow.appendChild(isarLabel);
  topRow.appendChild(try0Label);
  topRow.appendChild(spinner);
  topRow.appendChild(applyBtn);
  topRow.appendChild(cancelBtn);
  topRow.appendChild(locateBtn);
  container.appendChild(topRow);

  const result = document.createElement('div');
  result.id = 'result';
  container.appendChild(result);

  document.body.appendChild(container);

  renderDropdown();

  window.addEventListener('message', event => {
    const message = event.data;
    if (message.command === 'status') {
      spinner.classList.toggle('loading', message.message !== "Beendet");
    }
    else if (message.command === 'provers') {
      setHistory(message.history);
      if (message.provers) {
        proversInput.value = message.provers;
      } else if (message.history && message.history.length > 0) {
        proversInput.value = message.history[0];
      }
    }

    else if (message.command === 'no_proof_context') {
      const div = document.createElement("div");
      div.classList.add("interrupt");
      div.textContent = "Unknown proof context";
      result.appendChild(div);
    }
    else if (message.command === 'no_provers') {
      const div = document.createElement("div");
      div.classList.add("interrupt");
      div.textContent = "No such provers";
      result.appendChild(div);
    }
    else if (message.command === 'result') {
      if (wasCancelled) return;
      result.innerHTML = '';
      const parser = new DOMParser();
      const xmlDoc = parser.parseFromString(`<root>${message.content}</root>`, 'application/xml');
      const messages = xmlDoc.getElementsByTagName('writeln_message');
      for (const msg of messages) {
        const div = document.createElement('div');
        const inner = msg.innerHTML;
        if (inner.includes('<sendback')) {
          const tempContainer = document.createElement('div');
          tempContainer.innerHTML = inner;
          tempContainer.childNodes.forEach(node => {
            if (node.nodeType === Node.TEXT_NODE) {
              const text = node.textContent.trim();
              if (text) {
                const span = document.createElement('span');
                span.textContent = text;
                div.appendChild(span);
              }
            } else if (node.nodeName.toLowerCase() === 'sendback') {
              const button = document.createElement('button');
              button.textContent = node.textContent.trim();
              button.addEventListener('click', () => {
                vscode.postMessage({
                  command: 'insert_text',
                  provers: proversInput.value,
                  isar: isarCheckbox.checked,
                  try0: try0Checkbox.checked,
                  text: node.textContent.trim()
                });
              });
              div.appendChild(button);
            } else {
              const span = document.createElement('span');
              span.textContent = node.textContent.trim();
              div.appendChild(span);
            }
          });
        } else {
          div.textContent = msg.textContent.trim();
        }
        result.appendChild(div);
      }
      if (/Unknown proof context/i.test(message.content)) {
        result.classList.add('error');
      } else {
        result.classList.remove('error');
      }
      kannbeCancelled = false;
    }
  });

  window.onload = function () {
    const saved = vscode.getState();
    if (saved) {
      history = Array.isArray(saved.history) ? saved.history : [];
      proversInput.value = saved.provers || '';
      isarCheckbox.checked = !!saved.isar;
      try0Checkbox.checked = saved.try0 !== undefined ? saved.try0 : true;
      renderDropdown(false);
    }
  };
})();
