const { app, BrowserWindow } = require('electron')

const createWindow = () => {
  const win = new BrowserWindow({
    width: 800,
    height: 600
  })

  win.loadURL(process.env.URL || 'https://isabelle.in.tum.de')
}

app.whenReady().then(() => {
  createWindow()
})
