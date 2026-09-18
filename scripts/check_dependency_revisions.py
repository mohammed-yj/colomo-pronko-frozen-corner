"""Check every fetched package against the committed lockfile."""
from pathlib import Path
import json,subprocess
root=Path(__file__).resolve().parents[1]/'lean'
lock=json.loads((root/'lake-manifest.json').read_text())
for pkg in lock['packages']:
    path=root/lock['packagesDir']/pkg['name']
    got=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    assert got==pkg['rev'],(pkg['name'],got,pkg['rev'])
    print(pkg['name'],got)
