(function () {
  const vscode = acquireVsCodeApi();
  let was_cancelled = false;
  let can_be_cancelled = false;

  let history = [];

  const container = document.createElement('div');
  container.id = 'sledgehammer-container';

  const top_row = document.createElement('div');
  top_row.classList.add('top-row');

  const provers_label = document.createElement('label');
  provers_label.textContent = 'Provers: ';

  const provers_input_wrapper = document.createElement('div');
  provers_input_wrapper.className = 'provers-input-wrapper';

  const provers_input = document.createElement('input');
  provers_input.type = 'text';
  provers_input.id = 'provers';
  provers_input.size = 30;
  provers_input.value = '';
  provers_input.autocomplete = 'off';

  provers_input_wrapper.appendChild(provers_input);

  const chevron_button = document.createElement('button');
  chevron_button.type = 'button';
  chevron_button.className = 'provers-dropdown-toggle';
  chevron_button.setAttribute('aria-label', 'Show provers history');
  chevron_button.tabIndex = -1;
  chevron_button.innerHTML = '\u25bc';
  provers_input_wrapper.appendChild(chevron_button);

  provers_label.appendChild(provers_input_wrapper);

  const dropdown = document.createElement('div');
  dropdown.className = 'provers-dropdown';
  provers_input_wrapper.appendChild(dropdown);

  function show_dropdown() {
    dropdown.classList.add('visible');
  }
  function hide_dropdown() {
    dropdown.classList.remove('visible');
  }

  function render_dropdown(open = false) {
    dropdown.innerHTML = '';
    const header = document.createElement('div');
    header.textContent = 'Previously entered strings:';
    header.className = 'history-header';
    dropdown.appendChild(header);
    if (history.length === 0) {
      const no_entry = document.createElement('div');
      no_entry.className = 'history-header';
    }
    else {
      history.forEach(item => {
        const row = document.createElement('div');
        row.tabIndex = 0;
        row.textContent = item;

        const delete_button = document.createElement('span');
        delete_button.textContent = '\u2716';
        delete_button.className = 'delete-btn';
        delete_button.title = 'Delete entry';
        delete_button.addEventListener('mousedown', function (ev) {
          ev.preventDefault();
          ev.stopPropagation();
          history = history.filter(h => h !== item);
          render_dropdown(false);
          show_dropdown();
          vscode.postMessage({ command: 'delete_prover_history', entry: item });
        });

        row.appendChild(delete_button);
        row.addEventListener('mousedown', function (e) {
          e.preventDefault();
          provers_input.value = item;
          hide_dropdown();
          provers_input.focus();
        });
        dropdown.appendChild(row);
      });
    }
    if (open) show_dropdown(); else hide_dropdown();
  }


  chevron_button.addEventListener('mousedown', function (e) {
    e.preventDefault();
    if (dropdown.classList.contains('visible')) {
      hide_dropdown();
    }
    else {
      render_dropdown(true);
      show_dropdown();
      provers_input.focus();
    }
  });

  provers_input.addEventListener('input', () => { });

  provers_input.addEventListener('focus', function () {
    render_dropdown(true);
    show_dropdown();
  });
  provers_input.addEventListener('blur', () => {
    setTimeout(() => {
      if (!dropdown.contains(document.activeElement)) hide_dropdown();
    }, 150);
  });

  provers_input.addEventListener('keydown', (e) => {
    if (e.key === 'ArrowDown' && dropdown.childNodes.length) {
      dropdown.firstChild && dropdown.firstChild.focus && dropdown.firstChild.focus();
    }
  });

  function set_history(newHistory) {
    history = Array.isArray(newHistory) ? newHistory : [];
    save_state();
    render_dropdown(false);
  }

  function save_state() {
    vscode.setState({
      history,
      provers: provers_input.value,
      isar: isar_checkbox.checked,
      try0: try0_checkbox.checked
    });
  }

  function add_to_history(entry) {
    if (!entry.trim()) return;
    history = [entry, ...history.filter((h) => h !== entry)].slice(0, 10);
    save_state();
    render_dropdown();
  }

  const isar_label = document.createElement('label');
  const isar_checkbox = document.createElement('input');
  isar_checkbox.type = 'checkbox';
  isar_checkbox.id = 'isar';
  isar_label.appendChild(isar_checkbox);
  isar_label.appendChild(document.createTextNode(' Isar proofs'));

  const try0_label = document.createElement('label');
  const try0_checkbox = document.createElement('input');
  try0_checkbox.type = 'checkbox';
  try0_checkbox.id = 'try0';
  try0_checkbox.checked = true;
  try0_label.appendChild(try0_checkbox);
  try0_label.appendChild(document.createTextNode(' Try methods'));


  provers_input.addEventListener('input', save_state);
  isar_checkbox.addEventListener('change', save_state);
  try0_checkbox.addEventListener('change', save_state);
  const spinner = document.createElement('div');
  spinner.id = 'sledgehammer-spinner';

  const apply_button = document.createElement('button');
  apply_button.textContent = 'Apply';
  apply_button.id = 'apply-btn';
  apply_button.addEventListener('click', () => {
    was_cancelled = false;
    can_be_cancelled = true;
    result.innerHTML = '';
    add_to_history(provers_input.value);
    hide_dropdown();
    vscode.postMessage({
      command: 'apply',
      provers: provers_input.value,
      isar: isar_checkbox.checked,
      try0: try0_checkbox.checked
    });
  });

  const cancel_button = document.createElement('button');
  cancel_button.textContent = 'Cancel';
  cancel_button.addEventListener('click', () => {
    vscode.postMessage({ command: 'cancel' });
    if (was_cancelled) return;
    if (!can_be_cancelled) return;
    was_cancelled = true;
    spinner.classList.remove('loading');
    const div = document.createElement("div");
    div.classList.add("interrupt");
    div.textContent = "Interrupt";
    result.appendChild(div);
  });

  const locate_button = document.createElement('button');
  locate_button.textContent = 'Locate';
  locate_button.addEventListener('click', () => {
    vscode.postMessage({
      command: 'locate',
      provers: provers_input.value,
      isar: isar_checkbox.checked,
      try0: try0_checkbox.checked
    });
  });

  top_row.appendChild(provers_label);
  top_row.appendChild(isar_label);
  top_row.appendChild(try0_label);
  top_row.appendChild(spinner);
  top_row.appendChild(apply_button);
  top_row.appendChild(cancel_button);
  top_row.appendChild(locate_button);
  container.appendChild(top_row);

  const result = document.createElement('div');
  result.id = 'result';
  container.appendChild(result);

  document.body.appendChild(container);

  render_dropdown();

  window.addEventListener('message', event => {
    const message = event.data;
    if (message.command === 'status') {
      spinner.classList.toggle('loading', message.message !== "Finished");
    }
    else if (message.command === 'provers') {
      set_history(message.history);
      if (message.provers) {
        provers_input.value = message.provers;
      }
      else if (message.history && message.history.length > 0) {
        provers_input.value = message.history[0];
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
      if (was_cancelled) return;
      result.innerHTML = '';
      const parser = new DOMParser();
      const xml_doc = parser.parseFromString(`<root>${message.content}</root>`, 'application/xml');
      const messages = xml_doc.getElementsByTagName('writeln_message');
      for (const msg of messages) {
        const div = document.createElement('div');
        const inner = msg.innerHTML;
        if (inner.includes('<sendback')) {
          const temp_container = document.createElement('div');
          temp_container.innerHTML = inner;
          temp_container.childNodes.forEach(node => {
            if (node.nodeType === Node.TEXT_NODE) {
              const text = node.textContent.trim();
              if (text) {
                const span = document.createElement('span');
                span.textContent = text;
                div.appendChild(span);
              }
            }
            else if (node.nodeName.toLowerCase() === 'sendback') {
              const button = document.createElement('button');
              button.textContent = node.textContent.trim();
              button.addEventListener('click', () => {
                vscode.postMessage({
                  command: 'insert_text',
                  provers: provers_input.value,
                  isar: isar_checkbox.checked,
                  try0: try0_checkbox.checked,
                  text: node.textContent.trim()
                });
              });
              div.appendChild(button);
            }
            else {
              const span = document.createElement('span');
              span.textContent = node.textContent.trim();
              div.appendChild(span);
            }
          });
        }
        else {
          div.textContent = msg.textContent.trim();
        }
        result.appendChild(div);
      }
      if (/Unknown proof context/i.test(message.content)) {
        result.classList.add('error');
      }
      else {
        result.classList.remove('error');
      }
      can_be_cancelled = false;
    }
  });

  window.onload = function () {
    const saved = vscode.getState();
    if (saved) {
      history = Array.isArray(saved.history) ? saved.history : [];
      provers_input.value = saved.provers || '';
      isar_checkbox.checked = !!saved.isar;
      try0_checkbox.checked = saved.try0 !== undefined ? saved.try0 : true;
      render_dropdown(false);
    }
  };
})();
