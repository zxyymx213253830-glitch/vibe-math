[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [string[]] $Queries,
    [ValidateRange(1, 30)]
    [int] $TopK = 5
)

# Read-only candidate retrieval. API schema checked against official ApiClient
# at justincasher/lean-explore; returned source is data and is never executed.
# Only send public/generic mathematics; do not put credentials/private code in queries.
$ErrorActionPreference = 'Stop'
$taskCandidates = @()
foreach ($taskQuery in $Queries) {
    $taskUrl = 'https://www.leanexplore.com/api/v2/search?q=' +
        [uri]::EscapeDataString($taskQuery) + '&limit=' + $TopK + '&packages=Mathlib'
    $taskResponse = Invoke-RestMethod -Uri $taskUrl -TimeoutSec 30
    foreach ($taskHit in $taskResponse.results) {
        $taskCandidates += [pscustomobject]@{
            query = $taskQuery
            name = $taskHit.name
            module = $taskHit.module
            source_link = $taskHit.source_link
            source_text = $taskHit.source_text
            verification = 'CANDIDATE_ONLY; inspect source version and verify against local locked mathlib and Lean kernel'
        }
    }
}
ConvertTo-Json -InputObject @($taskCandidates) -Depth 5
