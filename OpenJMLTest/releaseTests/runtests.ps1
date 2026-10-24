## Tests a Windows release through its .bat launchers, natively (#1036); runtests (bash, run from WSL)
## covers the rest. Unzips the release into $Dest, whose name should contain a space, since installs
## often do (C:\Program Files, user names). Exits non-zero if a test fails.
##   Usage: pwsh runtests.ps1 <openjml.zip> <folder to unzip into>
param([Parameter(Mandatory)][string]$Zip, [Parameter(Mandatory)][string]$Dest)

$ErrorActionPreference = 'Stop'
$res   = 0
$tests = $PSScriptRoot

# Setup is fatal: if we cannot unzip the release there is nothing to test.
New-Item -ItemType Directory -Path $Dest -Force | Out-Null
Expand-Archive -Path $Zip -DestinationPath $Dest -Force
$env:OJBIN = (Resolve-Path $Dest).Path
$ojbin     = $env:OJBIN
Write-Host "Testing the .bat launchers of $Zip, unzipped into '$ojbin'"

# Normalize output for comparison: strip \r, convert \ to /, trim trailing
# whitespace per line, drop Note: lines — mirrors releaseTestHelper.
function Normalize([string[]]$lines) {
    if (-not $lines) { return '' }
    ($lines | Where-Object { $_ -notmatch '^Note: ' } |
              ForEach-Object { ($_ -replace '\\', '/').TrimEnd() }) -join "`n"
}

# Compare output AND exit code ($null: not checked); report both kinds of mismatch
# independently so the caller sees the full picture before moving on.
function Compare-Test([string]$name, [string[]]$actual, [int]$exitCode,
                      [string]$expectedFile, $expectedExit = 0) {
    $a      = Normalize $actual
    $e      = Normalize (Get-Content $expectedFile)
    $exitOk = ($null -eq $expectedExit) -or ($exitCode -eq $expectedExit)
    $outOk  = ($a.Trim() -eq $e.Trim())
    if ($exitOk -and $outOk) { Write-Host "$name OK"; return 0 }
    if (-not $exitOk) {
        Write-Host "FAIL ${name}: exit $exitCode (expected $expectedExit)"
    }
    if (-not $outOk) {
        Write-Host "FAIL ${name}: output mismatch"
        Write-Host '--- actual ---';   $a -split "`n" | ForEach-Object { Write-Host "  $_" }
        Write-Host '--- expected ---'; $e -split "`n" | ForEach-Object { Write-Host "  $_" }
    }
    return 1
}

# ── openjml.bat --version ────────────────────────────────────────
try {
    $version = 'openjml ' + (Get-Content "$tests\..\..\version.txt" -Raw).Trim()
    Set-Content "$tests\testJmlVersion\expected" $version
    $out  = & "$ojbin\openjml.bat" --version 2>&1; $exit = $LASTEXITCODE
    $res += Compare-Test 'testJmlVersion' $out $exit "$tests\testJmlVersion\expected"
} catch { Write-Host "FAIL testJmlVersion: $_"; $res++ }

# ── openjml.bat -check on a valid file (testOK1) ─────────────────
try {
    $out  = & "$ojbin\openjml.bat" --specs-path "$tests\src" "$tests\src\B.java" 2>&1
    $exit = $LASTEXITCODE
    if ($exit -eq 0) { Write-Host 'testOK1 OK' }
    else { Write-Host "FAIL testOK1: exit $exit"; $out | ForEach-Object { Write-Host "  $_" }; $res++ }
} catch { Write-Host "FAIL testOK1: $_"; $res++ }

# ── openjml.bat cases from runtests: help, bad arguments, runtime, paths ──
# Each is (test folder, arguments, expected exit code or $null), run from $tests so that
# relative paths in messages (./src/testPath/...) match the expected files.
$cases = @(
    ,@('testJmlHelpSimp',    @(), $null)
    ,@('testJmlHelp',        @('-?'), $null)
    ,@('testJmlHelp',        @('--help'), $null)
    ,@('testJmlHelp',        @('-help'), $null)
    ,@('testJmlBadNoSource', @('--verboseness='), 2)
    ,@('testJmlBadNoValue',  @('--verboseness'), 2)
    ,@('testJmlBadJava',     @('--check', '-java'), 2)
    ,@('testRuntime4',       @('src/C.java'), $null)
    ,@('testRuntime5',       @('src/D.java'), $null)
    ,@('testPath1',  @('-jmltesting', './src/testPath/data/TestPath.java'), 1)
    ,@('testPath2',  @('-jmltesting', './src/testPath/data/TestPath.java', '-classpath', './src/testPath/data'), 1)
    ,@('testPath3',  @('-jmltesting', './src/testPath/data/TestPath.java', '--specs-path', './src/testPath/data-specs'), 1)
    ,@('testPath4',  @('-jmltesting', './src/testPath/data/TestPath.java', '-sourcepath', './src/testPath/data-specs'), 1)
    ,@('testPath5',  @('-jmltesting', './src/testPath/data/TestPath.java', '-sourcepath', './src/testPath/data-specs;./src/testPath/data'), 1)
    ,@('testPath6',  @('-jmltesting', './src/testPath/data/TestPath.java', '-sourcepath', './src/testPath/data;./src/testPath/data-specs'), 1)
    ,@('testPath7',  @('-jmltesting', './src/testPath/data/TestPath.java', '-sourcepath', './src/testPath/data', '--specs-path', './src/testPath/data-specs'), 1)
    ,@('testPath8',  @('-jmltesting', './src/testPath/data/TestPath.java', '-classpath', './src/testPath/data-specs;./src/testPath/data'), 1)
    ,@('testPath9',  @('-jmltesting', './src/testPath/data/TestPath.java', '-classpath', './src/testPath/data;./src/testPath/data-specs'), 1)
    ,@('testPath10', @('-jmltesting', './src/testPath/data/TestPath.java', '-classpath', './src/testPath/data', '--specs-path', './src/testPath/data-specs'), 1)
)
Push-Location $tests
try {
    foreach ($c in $cases) {
        $name, $cargs, $expExit = $c
        try {
            $out  = & "$ojbin\openjml.bat" @cargs 2>&1; $exit = $LASTEXITCODE
            $res += Compare-Test "$name $($cargs -join ' ')" $out $exit "$name\expected" $expExit
        } catch { Write-Host "FAIL ${name}: $_"; $res++ }
    }
    # A bad verboseness value, from the environment and from openjml.properties
    try {
        $env:OPENJML_verboseness = 'x'
        $out  = & "$ojbin\openjml.bat" --check 2>&1; $exit = $LASTEXITCODE
        $res += Compare-Test 'testJmlBadProperty (environment)' $out $exit 'testJmlBadProperty\expected' 2
    } catch { Write-Host "FAIL testJmlBadProperty (environment): $_"; $res++ }
    finally { Remove-Item Env:OPENJML_verboseness }
    try {
        Set-Content 'openjml.properties' 'org.openjml.option.verboseness=x'
        $out  = & "$ojbin\openjml.bat" --check 2>&1; $exit = $LASTEXITCODE
        $res += Compare-Test 'testJmlBadProperty (openjml.properties)' $out $exit 'testJmlBadProperty\expected' 2
    } catch { Write-Host "FAIL testJmlBadProperty (openjml.properties): $_"; $res++ }
    finally { Remove-Item 'openjml.properties' -ErrorAction SilentlyContinue }
} finally { Pop-Location }

# ── openjml.bat --esc (testEsc1, testEsc2) ───────────────────────
# Push to $tests so source paths in ESC messages are relative
# (./src/testEsc/A.java:4:) matching the expected files.
Push-Location $tests
try {
    $out  = & "$ojbin\openjml.bat" --esc .\src\testEsc\A.java `
                -classpath .\src\testEsc 2>&1; $exit = $LASTEXITCODE
    $res += Compare-Test 'testEsc1' $out $exit testEsc1\expected 6
} catch { Write-Host "FAIL testEsc1: $_"; $res++ }

try {
    $out  = & "$ojbin\openjml.bat" --esc .\src\testEsc\B.java `
                -classpath .\src\testEsc 2>&1; $exit = $LASTEXITCODE
    $res += Compare-Test 'testEsc2' $out $exit testEsc2\expected 0
} catch { Write-Host "FAIL testEsc2: $_"; $res++ }
finally { Pop-Location }

# ── RAC: compile with openjml.bat -rac, run with openjml-java.bat ──
# Push to $tests so source paths in RAC messages are relative
# (./src/testRac/A.java:4:) and match expected-ok / expected-simple.
Push-Location $tests
try {
    $racDir = (New-Item -ItemType Directory -Path 'rac-bat' -Force).FullName
    $rt     = "$ojbin\jmlruntime.jar"

    $compOut  = & "$ojbin\openjml.bat" -rac --rac-show-source=line `
        -d "$racDir" -classpath ".\src\testRac" --specs-path ".\src\testRac" `
        ".\src\testRac\A.java" 2>&1
    $compExit = $LASTEXITCODE
    if ($compExit -ne 0) {
        Write-Host "FAIL testRac-bat (compilation): exit $compExit"
        $compOut | ForEach-Object { Write-Host "  $_" }
        $res++
    } else {
        # No-arg run: assertion passes (0 != 2) → exit 0, output START/END
        $out  = & "$ojbin\openjml-java.bat" -classpath "$racDir;$rt" A 2>&1
        $exit = $LASTEXITCODE
        $res += Compare-Test 'testRac-ok (.bat)' $out $exit ".\testRac\expected-ok"

        # Two-arg run: assertion fails, program continues → exit 0, violation printed
        $out  = & "$ojbin\openjml-java.bat" -classpath "$racDir;$rt" A 1 2 2>&1
        $exit = $LASTEXITCODE
        $res += Compare-Test 'testRac-simple (.bat)' $out $exit ".\testRac\expected-simple"
    }
} catch { Write-Host "FAIL testRac-bat: $_"; $res++ }
finally { Pop-Location }

# ── testAPI using .bat scripts (full output comparison) ───────────
Push-Location "$tests\testAPI"
try {
    Remove-Item *.class -ErrorAction SilentlyContinue
    $out  = cmd /c "`"$tests\testAPI\run.bat`"" 2>&1; $exit = $LASTEXITCODE
    $res += Compare-Test 'testAPI (.bat)' $out $exit "$tests\testAPI\expected"
} catch { Write-Host "FAIL testAPI (.bat): $_"; $res++ }
finally { Pop-Location }

# ── LSP server through openjml-lsp.bat (#1033) ────────────────────
try {
    $env:OPENJML_LSP_LOG = "$ojbin\openjml-lsp-smoke.log"
    & node "$tests\..\scripttests\lsp-smoke.js" "$ojbin\openjml-lsp.bat" "$ojbin\lsp smoke"
    if ($LASTEXITCODE -ne 0) {
        Write-Host '--- server log ---'; Get-Content $env:OPENJML_LSP_LOG -ErrorAction SilentlyContinue | ForEach-Object { Write-Host "  $_" }
        $res++
    }
} catch { Write-Host "FAIL lsp-smoke: $_"; $res++ }
finally { Remove-Item Env:OPENJML_LSP_LOG -ErrorAction SilentlyContinue }

if ($res -gt 0) { Write-Error "$res .bat test(s) failed"; exit 1 }
Write-Host 'All .bat tests passed'
