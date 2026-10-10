@echo off
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0start.ps1" -CheckOnly
if errorlevel 1 goto failed
"D:\miniconda3\python.exe" "%~dp0prove.py"
pause
exit /b
:failed
pause
exit /b 1
