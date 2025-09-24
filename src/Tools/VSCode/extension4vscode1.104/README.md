# Isabelle2025 Extension for Visual Studio Code 1.104

This repository contains the Isabelle2025 extension for Visual Studio Code, including symbol snippets and configuration files.

## English Installation Guide

1. Install the `isabelle-vscode-2.0.0.vsix` extension file in VS Code
   - Open VS Code
   - Go to Extensions view (Ctrl+Shift+X)
   - Click the "..." menu and select "Install from VSIX..."
   - Select the `isabelle-vscode-2.0.0.vsix` file

2. Copy the `isabelle-symbols.code-snippets` file to your workspace's `.vscode` folder
   - Create a `.vscode` folder in your project root if it doesn't exist
   - Place the snippets file inside this folder

3. Configure the Isabelle extension settings:
   - Open VS Code settings (Ctrl+,)
   - Search for "Isabelle: Home"
   - Set the path to your Isabelle installation directory: `<installation-directory>\Isabelle2025`

4. For Windows users only:
   - Add the environment variable `CYGWIN_ROOT` with value: `<installation-directory>\Isabelle2025\contrib\cygwin`
   - This step is not required for macOS users

## 中文安装指南

1. 将 vsix 安装至 vscode
   - 打开 VS Code
   - 进入扩展视图 (Ctrl+Shift+X)
   - 点击 "..." 菜单并选择 "从 VSIX 安装..."
   - 选择 `isabelle-vscode-2.0.0.vsix` 文件

2. 在工作目录的 .vscode 文件夹中放入 isabelle-symbols.code-snippets 文件
   - 如果项目根目录没有 `.vscode` 文件夹，请先创建
   - 将代码片段文件放入该文件夹

3. 进入 Isabelle/VSCode 插件设置，将 Isabelle: Home 设置为你的 Isabelle 安装目录：`<安装目录>\Isabelle2025`

4. Windows 需要在环境变量中手动添加 `CYGWIN_ROOT : <安装目录>\Isabelle2025\contrib\cygwin`，MacOS 似乎不需要这一步

## Files Included

- `isabelle-vscode-2.0.0.vsix` - The Isabelle extension package for VS Code
- `.vscode/isabelle-symbols.code-snippets` - Symbol snippets for Isabelle syntax

## Requirements

- Visual Studio Code 1.104 or later
- Isabelle2025 installation
