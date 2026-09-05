param(
    [Parameter(Mandatory = $true)][string]$Module,
    [string]$Output,
    [int]$MemoryMB = 4096,
    [int]$ReserveMB = 8192
)

$ErrorActionPreference = 'Stop'
if (Get-Process lean,lake -ErrorAction SilentlyContinue) {
    throw 'Another Lean/Lake process is running; refusing a concurrent compilation.'
}
$freeMB = (Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory / 1024
if ($freeMB -lt ($MemoryMB + $ReserveMB)) {
    throw "Insufficient free memory: $([int]$freeMB) MB."
}
$env:LEAN_NUM_THREADS = '1'
$logBase = Join-Path ([IO.Path]::GetTempPath()) ('janus-lean-' + [guid]::NewGuid())
$leanArguments = @('env', 'lean', "--memory=$MemoryMB", '--threads=1')
if ($Output) { $leanArguments += @('-o', $Output) }
$leanArguments += $Module
# Start-Process joins arguments; reject quotes and quote paths containing spaces.
$quotedArguments = foreach ($argument in $leanArguments) {
    if ($argument.Contains('"')) { throw 'Quotes in arguments are unsupported.' }
    '"' + $argument + '"'
}
$rootProcess = Start-Process (Get-Command lake).Source -ArgumentList $quotedArguments `
    -PassThru -WindowStyle Hidden -RedirectStandardOutput "$logBase.out" `
    -RedirectStandardError "$logBase.err"
$tracked = @{$rootProcess.Id = $rootProcess}
$stoppedForMemory = $false
$peakMB = 0
$minimumFreeMB = $freeMB
try {
    while (-not $rootProcess.HasExited) {
        $processTree = Get-CimInstance Win32_Process
        do {
            $added = $false
            foreach ($entry in $processTree) {
                if ($tracked.ContainsKey([int]$entry.ParentProcessId) -and
                    -not $tracked.ContainsKey([int]$entry.ProcessId)) {
                    $child = Get-Process -Id $entry.ProcessId -ErrorAction SilentlyContinue
                    if ($child) { $tracked[$child.Id] = $child; $added = $true }
                }
            }
        } while ($added)
        $workingMB = 0
        foreach ($ownedProcess in $tracked.Values) {
            $ownedProcess.Refresh()
            if (-not $ownedProcess.HasExited) {
                try { $ownedProcess.PriorityClass = 'High' }
                catch { if (-not $ownedProcess.HasExited) { throw } }
                $workingMB += $ownedProcess.WorkingSet64 / 1MB
            }
        }
        $freeMB = (Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory / 1024
        $peakMB = [Math]::Max($peakMB, $workingMB)
        $minimumFreeMB = [Math]::Min($minimumFreeMB, $freeMB)
        if ($freeMB -lt $ReserveMB -or $workingMB -gt ($MemoryMB + 1024)) {
            $stoppedForMemory = $true
            break
        }
        Start-Sleep -Seconds 1
        $rootProcess.Refresh()
    }
} finally {
    foreach ($ownedProcess in $tracked.Values) {
        if (-not $ownedProcess.HasExited) { $ownedProcess.Kill() }
    }
    $rootProcess.WaitForExit()
    Get-Content "$logBase.out"
    Get-Content "$logBase.err"
    Write-Host "Lean logs: $logBase.out / $logBase.err"
    Write-Host "Sampled process-tree peak: $([int]$peakMB) MB; minimum free: $([int]$minimumFreeMB) MB."
}
if ($stoppedForMemory) { throw 'Lean stopped to preserve available system memory.' }
exit $rootProcess.ExitCode
