"""Audit the explicit public file manifest, preserved inputs, and Lean source tokens."""
from pathlib import Path
import hashlib,json,os,re,subprocess
ROOT=Path(__file__).resolve().parents[1]


def lean_code(text):
    out=[];i=0;depth=0;string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:
                if text[i]=='\n':out.append('\n')
                i+=1
        elif string:
            if text[i]=='\\':i+=2
            elif text[i]=='"':string=False;i+=1
            else:i+=1
        elif text.startswith('/-',i):depth=1;out.append(' ');i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(text[i]);i+=1
    assert not depth and not string,'Unclosed comment or string'
    return ''.join(out)


def main():
    (ROOT/'.audit').mkdir(exist_ok=True)
    manifest=ROOT/'SHA256SUMS'
    assert manifest.exists(),'Missing explicit public manifest'
    names=set()
    for line in manifest.read_text().splitlines():
        sha,name=line.split('  ',1)
        assert name not in names and not Path(name).is_absolute() and '..' not in Path(name).parts
        names.add(name);p=ROOT/name
        assert p.is_file() and not p.is_symlink(),name
        assert hashlib.sha256(p.read_bytes()).hexdigest()==sha,name
    names.add('SHA256SUMS')
    ignore={'.git','.lake','.audit','.venv','__pycache__'}
    actual=set()
    for path,ds,fs in os.walk(ROOT):
        ds[:]=[d for d in ds if d not in ignore]
        for f in fs: actual.add(str((Path(path)/f).relative_to(ROOT)))
    assert actual==names,{'extra':sorted(actual-names),'missing':sorted(names-actual)}
    if (ROOT/'.git').exists():
        tracked=set(subprocess.check_output(['git','ls-files'],cwd=ROOT,text=True).splitlines())
        if tracked:assert tracked==names,{'tracked_difference':sorted(tracked^names)}
    provenance=json.loads((ROOT/'provenance.json').read_text())
    for name,record in provenance['preserved_files'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==record['sha256'],name
    forbidden=re.compile(r'\b(?:sorry|admit|axiom|sorryAx|native_decide|implemented_by)\b|debug\.skipKernelTC')
    proof_files=[ROOT/'lean/CP.lean',*sorted((ROOT/'lean/CP').rglob('*.lean'))]
    for p in [*proof_files,ROOT/'lean/lakefile.lean',*sorted((ROOT/'lean/tools').glob('*.lean'))]:
        code=lean_code(p.read_text())
        assert not forbidden.search(code),str(p.relative_to(ROOT))
        if p in proof_files:assert not re.search(r'\b(?:unsafe|decide)\b',code),p.name
    listed=set(re.findall(r'"(CP(?:\.[A-Za-z0-9_]+)*)"',(ROOT/'lean/lakefile.lean').read_text()))
    modules={str(p.relative_to(ROOT/'lean').with_suffix('')).replace('/','.') for p in proof_files}
    assert modules<=listed,modules-listed
    toolchain=(ROOT/'lean/lean-toolchain').read_text().strip()
    assert toolchain=='leanprover/lean4:v4.19.0'
    deps=json.loads((ROOT/'lean/lake-manifest.json').read_text())
    for p in deps['packages']:assert re.fullmatch('[a-f0-9]{40}',p['rev']),p['name']
    assert next(p['rev'] for p in deps['packages'] if p['name']=='mathlib')=='c44e0c8ee63ca166450922a373c7409c5d26b00b'
    for name in names:
        p=ROOT/name
        assert not any(part in {'.DS_Store','.lake','__pycache__'} for part in p.parts),name
        assert p.suffix not in {'.zip','.gz','.log','.pyc'},name
        if p.suffix=='.pdf':continue  # PDF content/metadata were separately audited before publication.
        txt=p.read_text()
        assert not re.search(r'/(?:Users|home)/[^\s/]+|[A-Z]:\\(?:Users|Documents)\\',txt),name
        assert not re.search(r'gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}',txt),name
    print(json.dumps({'passed':True,'public_files':len(names),'preserved_files':len(provenance['preserved_files']),
                      'lean_modules':len(modules),'forbidden_tokens':[]},indent=2))


if __name__=='__main__':main()
