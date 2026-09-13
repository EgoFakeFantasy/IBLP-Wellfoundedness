param([string]$Lake = 'lake')
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Force verification | Out-Null
    # Every project module must enter the audited environment through IBLP.
    $moduleFiles = @(Get-ChildItem -LiteralPath IBLP -Filter '*.lean' -Recurse -File)
    $modulePaths = @{ IBLP = (Join-Path $PSScriptRoot 'IBLP.lean') }
    foreach ($file in $moduleFiles) {
        $relative = $file.FullName.Substring($PSScriptRoot.Length + 1)
        $moduleName = ($relative -replace '\.lean$', '') -replace '[\\/]', '.'
        $modulePaths[$moduleName] = $file.FullName
    }
    $pending = [System.Collections.Generic.Queue[string]]::new()
    $reachable = [System.Collections.Generic.HashSet[string]]::new()
    $pending.Enqueue('IBLP')
    while ($pending.Count -gt 0) {
        $moduleName = $pending.Dequeue()
        if (-not $reachable.Add($moduleName)) { continue }
        if (-not $modulePaths.ContainsKey($moduleName)) { throw "Missing local module: $moduleName" }
        foreach ($line in Get-Content -LiteralPath $modulePaths[$moduleName]) {
            if ($line -match '^\s*import\s+(IBLP(?:\.[A-Za-z0-9_]+)*)') {
                $pending.Enqueue($Matches[1])
            }
        }
    }
    $unreachable = @($modulePaths.Keys | Where-Object { -not $reachable.Contains($_) })
    if ($unreachable.Count -gt 0) { throw "Modules outside root audit: $($unreachable -join ', ')" }
    & $Lake --rehash build 2>&1 | Tee-Object -FilePath verification\build.log
    if ($LASTEXITCODE -ne 0) { throw 'Full build failed.' }
    & $Lake env lean CheckMilestones.lean 2>&1 | Tee-Object -FilePath verification\milestones.log
    if ($LASTEXITCODE -ne 0) { throw 'Milestone type check failed.' }
    & $Lake env lean Audit.lean 2>&1 | Tee-Object -FilePath verification\audit.log
    if ($LASTEXITCODE -ne 0) { throw 'Kernel axiom audit failed.' }
    $auditText = Get-Content -LiteralPath verification\audit.log -Raw
    $auditMatch = [regex]::Match($auditText, 'Kernel audit passed: (\d+) IBLP constants \(including (\d+) private constants\); (\d+) theorem constants;')
    if (-not $auditMatch.Success) { throw 'Missing kernel audit summary.' }
    $sources = @(Get-ChildItem -LiteralPath IBLP -Filter '*.lean' -Recurse -File)
    $sources += Get-Item -LiteralPath IBLP.lean, CheckMilestones.lean, Audit.lean
    $bad = $sources | Select-String -Pattern '\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\s'
    if ($bad) { $bad | Out-String | Write-Output; throw 'Forbidden proof token.' }
    $checks = [ordered]@{
        checkedAtUtc = [DateTime]::UtcNow.ToString('o')
        scope = 'Complete formal proof of the original I3 -> Acc Child root and absence of infinite original expansion branches. Original six-row root, empty zero, full-tail copy, first-copy fallback only, original q staircase, native middle-row exception, canonical filtered frozen queue and original Child are unchanged. Full internal extender, complete finite copying and frozen/native scan closure, saturation, totality and strict image-top comparison are proved. For each fixed finite pattern an actual finite membership formula expresses existence of a full saturated BoundedRealization below an ordinal. It decodes every point, full elementary row graph, critical point, edge, paired-source and trace computation, exact historical composite graph, computed natural top and full weak mark certificate. Six actual syntax books are proved fixed under every elementary map. External minimal bad top and reflection of the fixed chosen child formula give accessibility of every complete realization; the original I3 root supplies the main theorem with no extra mathematical premise. This proves expansion-tree well-foundedness; no separate lexicographic order is claimed. All local public and private declarations are audited transitively.'
        leanToolchain = (Get-Content lean-toolchain -Raw).Trim()
        fullMarkedBLPCommit = (& git -C .lake/packages/fullMarkedBLP rev-parse HEAD).Trim()
        fullBuild = 'passed'
        milestoneTypes = 'passed'
        axiomAudit = 'passed'
        auditedConstants = [int]$auditMatch.Groups[1].Value
        auditedPrivateConstants = [int]$auditMatch.Groups[2].Value
        auditedTheorems = [int]$auditMatch.Groups[3].Value
        auditIncludesPrivateDeclarations = $true
        rootImportCoverage = 'passed'
        projectModuleCount = $moduleFiles.Count
        mainWellFoundednessTheorem = 'IBLP.i3_wellFoundedAtRoot : IBLP.I3 -> Acc IBLP.Child IBLP.root'
        sourceGuard = 'passed'
        sourceFiles = @($sources | Sort-Object FullName | ForEach-Object {
            [ordered]@{ path = $_.FullName.Substring($PSScriptRoot.Length + 1); sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash }
        })
    }
    $checks | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath verification\result.json -Encoding utf8
} finally {
    Pop-Location
}






