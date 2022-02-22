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
    auto_update && auto_update.addEventListener('change', (e) => {
            vscode.postMessage({'command': 'auto_update', 'enabled': e.target.checked}) ;
        });

    const update_button = document.getElementById('update_button');
    update_button && update_button.addEventListener('click', (e) => {
            vscode.postMessage({'command': 'update'}) 
        });
        
    const locate_button = document.getElementById('locate_button');
    locate_button && locate_button.addEventListener('click', (e) => {
            vscode.postMessage({'command': 'locate'});
        });
}());