param(
    [Parameter(Mandatory = $true)]
    [ValidateNotNullOrEmpty()]
    [string[]] $Queries,
    [ValidateRange(1, 30)]
    [int] $TopK = 5
)

# Query the public retrieval service only. Never evaluate returned proof text.
# The service records search queries: use generic/public mathematical statements.
# A returned candidate is NOT a proof and must be checked in the locked Lean project.
$ErrorActionPreference = 'Stop'
$taskBody = @{ query = @($Queries); num_results = $TopK } | ConvertTo-Json -Compress
$taskResults = Invoke-RestMethod -Uri 'https://leansearch.net/search' -Method Post `
    -ContentType 'application/json' -Body ([System.Text.Encoding]::UTF8.GetBytes($taskBody)) `
    -TimeoutSec 30
if ($taskResults.Count -ne $Queries.Count) {
    throw 'Unexpected query/result count from LeanSearch.'
}
$taskRows = for ($taskIndex = 0; $taskIndex -lt $Queries.Count; $taskIndex++) {
    foreach ($taskHit in $taskResults[$taskIndex]) {
        [pscustomobject]@{
            query = $Queries[$taskIndex]
            name = $taskHit.result.name -join '.'
            module = $taskHit.result.module_name -join '.'
            signature = $taskHit.result.signature
            distance = $taskHit.distance
            verification = 'CANDIDATE_ONLY; check local locked mathlib and Lean kernel'
        }
    }
}
ConvertTo-Json -InputObject @($taskRows) -Depth 5
