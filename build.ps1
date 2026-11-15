# Compila islita.exe con MinGW (MSYS2 UCRT64) y la instala en %LOCALAPPDATA%\Programs\islita
$ErrorActionPreference = "Continue"
$env:PATH = "C:\msys64\ucrt64\bin;$env:PATH"
Set-Location $PSScriptRoot
windres islita.rc -O coff -o islita_res.o
if ($LASTEXITCODE -ne 0) { throw "Error al compilar el icono" }
g++ -std=c++20 -Os -s -static -municode -mwindows -fno-exceptions -fno-rtti islita.cpp islita_res.o -o islita.exe `
    -ld2d1 -ldwrite -lwindowscodecs -lole32 -luuid -lshell32 -lshlwapi -lpdh -lcomctl32 `
    -lruntimeobject -lshcore -lwinhttp -ldwmapi -lwinmm -lwbemuuid -loleaut32 -luser32 -lgdi32 -ladvapi32 -lwlanapi -liphlpapi -lws2_32
if ($LASTEXITCODE -ne 0) { throw "Error al compilar" }
$dst = "$env:LOCALAPPDATA\Programs\islita"
New-Item -ItemType Directory -Force $dst | Out-Null
Get-Process islita, Isla -ErrorAction SilentlyContinue | Stop-Process -Force
Start-Sleep -Milliseconds 300
Copy-Item islita.exe "$dst\islita.exe" -Force
Write-Host "Instalada en $dst\islita.exe ($([math]::Round((Get-Item islita.exe).Length/1KB)) KB)"
