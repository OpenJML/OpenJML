## Keep in sync with install-vscode-extension (bash equivalent); run by install-vscode-extension.bat.
## Installs the OpenJML VS Code extension and sets openjml.serverPath in the VS Code user settings to
## this folder's openjml-lsp.bat. Set VSCODE_CLI to use a particular code (or codium) command.
## Edits settings.json as text, since it may hold comments, which a JSON parser rejects.

$ErrorActionPreference = 'Stop'
$dir    = $PSScriptRoot
$vsix   = Join-Path $dir 'openjml.vsix'
$server = Join-Path $dir 'openjml-lsp.bat'
$code   = if ($env:VSCODE_CLI) { $env:VSCODE_CLI } else { 'code' }

if (-not (Test-Path $vsix)) { Write-Error "openjml.vsix not found in $dir" }
if (-not $env:VSCODE_CLI -and -not (Get-Command code -ErrorAction SilentlyContinue)) {
    Write-Error ("Could not find the VS Code 'code' command. Reinstall VS Code with 'Add to PATH', " +
                 "or set VSCODE_CLI to the full path of code.cmd (or codium.cmd).")
}

Write-Host "Installing the OpenJML VS Code extension with $code ..."
& $code --install-extension $vsix --force
if ($LASTEXITCODE -ne 0) { Write-Error "'$code --install-extension' failed (exit $LASTEXITCODE)" }

$settings = Join-Path $env:APPDATA 'Code\User\settings.json'
$entry    = '"openjml.serverPath": ' + ($server | ConvertTo-Json)
$pattern  = '"openjml\.serverPath"\s*:\s*"(?:[^"\\]|\\.)*"'
if (Test-Path $settings) {
    $text = [IO.File]::ReadAllText($settings)
} else {
    New-Item -ItemType Directory -Force (Split-Path $settings) | Out-Null
    $text = '{}'
}
if ($text -match $pattern) {
    $text = [regex]::Replace($text, $pattern, [Text.RegularExpressions.MatchEvaluator]{ param($m) $entry })
} elseif ($text -match '\{') {
    # VS Code accepts the trailing comma this leaves in a settings file holding just {}
    $text = ([regex]'\{').Replace($text, [Text.RegularExpressions.MatchEvaluator]{ param($m) "{`n    $entry," }, 1)
} else {
    $text = "{`n    $entry`n}`n"
}
[IO.File]::WriteAllText($settings, $text)

Write-Host ""
Write-Host "Done."
Write-Host "  Extension : openjml.vsix installed"
Write-Host "  Server    : $server (openjml.serverPath in $settings)"
Write-Host "Restart VS Code, or run Ctrl+Shift+P > 'Developer: Reload Window', to activate the extension."
