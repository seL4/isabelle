(function () {
    const vscode = acquireVsCodeApi();

    for (const link of document.querySelectorAll('a[href^="file:"]')) {
        link.addEventListener('click', () => {
            vscode.postMessage({
                command: "open",
                link: link.getAttribute('href'),
            });
        });
    }

    const auto_update = document.getElementById('auto_update');
    auto_update && auto_update.addEventListener('change', e => {
            vscode.postMessage({'command': 'auto_update', 'enabled': e.target.checked}) ;
        });

    const update_button = document.getElementById('update_button');
    update_button && update_button.addEventListener('click', e => {
            vscode.postMessage({'command': 'update'})
        });

    const locate_button = document.getElementById('locate_button');
    locate_button && locate_button.addEventListener('click', e => {
            vscode.postMessage({'command': 'locate'});
        });

    const get_window_margin = () => {
        const test_string = "mix";
        const test_span = document.createElement("span");
        test_span.textContent = test_string;
        document.body.appendChild(test_span);
        const symbol_width = test_span.getBoundingClientRect().width / test_string.length;
        document.body.removeChild(test_span);

        const width = window.innerWidth / symbol_width;
        const result = Math.max(width - 16, 1); // extra headroom
        return result;
    }

    const update_window_width = () => {
        vscode.postMessage({'command': 'resize', 'margin': get_window_margin()})
    };

    var timeout;
    window.onresize = function() {
        clearTimeout(timeout);
        timeout = setTimeout(update_window_width, 500);
    };
    window.onload = update_window_width;
}());
