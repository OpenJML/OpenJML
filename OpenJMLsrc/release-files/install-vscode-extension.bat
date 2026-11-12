@echo off
:: Keep in sync with install-vscode-extension (bash equivalent).
:: Installs the OpenJML VS Code extension and points it at this folder's openjml-lsp.bat;
:: the work is done by install-vscode-extension.ps1.
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0install-vscode-extension.ps1"
exit /b %ERRORLEVEL%
