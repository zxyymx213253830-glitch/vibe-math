param([switch]$CheckOnly)
$ErrorActionPreference = 'Stop'
$ollamaPath = 'D:\Ollama\ollama.exe'
try {
    $null = Invoke-RestMethod 'http://127.0.0.1:11434/api/version' -TimeoutSec 3
} catch {
    Start-Process -FilePath $ollamaPath -ArgumentList 'serve' -WindowStyle Hidden
    $ready = $false
    for ($attempt = 0; $attempt -lt 30; $attempt++) {
        Start-Sleep -Seconds 1
        try {
            $null = Invoke-RestMethod 'http://127.0.0.1:11434/api/version' -TimeoutSec 2
            $ready = $true
            break
        } catch { }
    }
    if (-not $ready) { throw 'Ollama did not start. Open Ollama and try again.' }
}
if ($CheckOnly) { exit 0 }
& $ollamaPath run 'deepseek-prover-v2:7b'
exit $LASTEXITCODE
