param(
    [switch]$Write
)

$ErrorActionPreference = "Stop"
$root = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path

function Test-ExcludedPath([string]$Path) {
    $parts = $Path.Substring($root.Length + 1) -split "[\\/]"
    $parts -contains ".git" -or $parts -contains ".lake"
}

function Get-ProjectFiles {
    @(
        & git -C $root ls-files --cached --others --exclude-standard |
            ForEach-Object { $_.Replace("\", "/") }
    )
}

function Write-Utf8NoBom([string]$Path, [string[]]$Lines) {
    [System.IO.File]::WriteAllText(
        $Path,
        (($Lines -join [Environment]::NewLine) + [Environment]::NewLine),
        [System.Text.UTF8Encoding]::new($false)
    )
}

$tracked = [string[]]@(Get-ProjectFiles)
[Array]::Sort($tracked, [System.StringComparer]::Ordinal)
$lean = [string[]]@($tracked | Where-Object { $_.EndsWith(".lean") })
[Array]::Sort($lean, [System.StringComparer]::Ordinal)

if ($Write) {
    Write-Utf8NoBom (Join-Path $root "MANIFEST.txt") @(
        $tracked | Where-Object { $_ -ne "MANIFEST.txt" }
    )
    Write-Utf8NoBom (Join-Path $root "LEAN_SOURCE_INVENTORY.txt") $lean
    $tracked = [string[]]@(Get-ProjectFiles)
    [Array]::Sort($tracked, [System.StringComparer]::Ordinal)
}

$errors = [System.Collections.Generic.List[string]]::new()

$manifest = @(
    Get-Content (Join-Path $root "MANIFEST.txt") |
        Where-Object { $_.Trim() -and -not $_.StartsWith("#") } |
        ForEach-Object { $_.Trim() }
)
$expectedManifest = @($tracked | Where-Object { $_ -ne "MANIFEST.txt" })
foreach ($entry in $manifest) {
    if (-not (Test-Path (Join-Path $root $entry) -PathType Leaf)) {
        $errors.Add("MANIFEST.txt lists missing file: $entry")
    }
}
if (($manifest -join "`n") -cne ($expectedManifest -join "`n")) {
    $errors.Add("MANIFEST.txt is not the sorted project-file manifest")
}

$inventory = @(
    Get-Content (Join-Path $root "LEAN_SOURCE_INVENTORY.txt") |
        Where-Object { $_.Trim() -and -not $_.StartsWith("#") } |
        ForEach-Object { $_.Trim() }
)
if (($inventory -join "`n") -cne ($lean -join "`n")) {
    $errors.Add("LEAN_SOURCE_INVENTORY.txt is out of date")
}

$aggregate = Get-Content (Join-Path $root "ClassicalThermodynamics\Applications.lean") -Raw
Get-ChildItem (Join-Path $root "ClassicalThermodynamics\Applications") -Directory |
    ForEach-Object {
        $traceability = Join-Path $_.FullName "Traceability.lean"
        if (Test-Path $traceability -PathType Leaf) {
            $module = "ClassicalThermodynamics.Applications.$($_.Name).Traceability"
            if ($aggregate -notmatch [regex]::Escape("import $module")) {
                $errors.Add("Applications.lean does not import $module")
            }
        }
    }

$obsoleteNames = @(
    "PhaseSeparation",
    "IMPLEMENTATION_REPORT",
    "INTEGRATION_REPORT",
    "INTERNAL_IMPORT_AUDIT",
    "Applications/ResponseFunctions/Traceability",
    "FHFunction.lean"
)
$textExtensions = @(".lean", ".md", ".txt", ".toml", ".yml", ".yaml", ".ps1")
$checkerRelativePath = "scripts/check_documentation.ps1"
Get-ChildItem $root -Recurse -File |
    Where-Object {
        -not (Test-ExcludedPath $_.FullName) -and
        $textExtensions -contains $_.Extension.ToLowerInvariant() -and
        $_.FullName.Substring($root.Length + 1).Replace("\", "/") -ne
          $checkerRelativePath
    } |
    ForEach-Object {
        $text = Get-Content $_.FullName -Raw
        foreach ($obsolete in $obsoleteNames) {
            if ($text.Contains($obsolete)) {
                $relative = $_.FullName.Substring($root.Length + 1)
                $errors.Add("$relative contains obsolete name $obsolete")
            }
        }
    }

$markdownPattern = "\]\(([^)#]+)(?:#[^)]+)?\)"
Get-ChildItem $root -Recurse -File -Filter "*.md" |
    Where-Object { -not (Test-ExcludedPath $_.FullName) } |
    ForEach-Object {
        $content = Get-Content $_.FullName -Raw
        foreach ($match in [regex]::Matches($content, $markdownPattern)) {
            $target = $match.Groups[1].Value
            if ($target -match "^(https?://|mailto:)") {
                continue
            }
            $targetPath = Join-Path $_.DirectoryName $target
            if (-not (Test-Path $targetPath -PathType Leaf)) {
                $relative = $_.FullName.Substring($root.Length + 1)
                $errors.Add("$relative links to missing file $target")
            }
        }
    }

if ($errors.Count -gt 0) {
    $errors | Write-Error
    exit 1
}

Write-Output "Documentation consistency checks passed."
