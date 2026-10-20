param(
    [ValidateSet('status','queue','check','accept')]
    [string]$Action = 'status',
    [string]$Evidence
)
$scriptPath = Join-Path $PSScriptRoot 'sheaf\wishart\tools\sheaf.py'
$sheafArgs = @('-X', 'utf8', $scriptPath, $Action)
if ($Evidence) { $sheafArgs += $Evidence }
& 'D:\miniconda3\python.exe' @sheafArgs
exit $LASTEXITCODE
