"""Fail closed on unexpected axioms, absent roots, or normalization leakage."""
from pathlib import Path
import json,re,sys
allowed={'propext','Classical.choice','Quot.sound'}
root=Path(__file__).resolve().parents[1]
axiom_text=Path(sys.argv[1]).read_text()
dep_text=Path(sys.argv[2]).read_text()
assert 'error:' not in axiom_text+dep_text
observed={}
for name,values in re.findall(r'^AXIOM_AUDIT (\S+) \[([^\]]*)\]$',axiom_text,re.M):
    assert name not in observed,name
    observed[name]=sorted(v.strip() for v in values.split(',') if v.strip())
    assert set(observed[name])<=allowed,(name,observed[name])
total=re.findall(r'^AXIOM_AUDIT_TOTAL (\d+)$',axiom_text,re.M)
assert len(total)==1 and int(total[0])==len(observed)>0
# The source manifest fixes the project; compare the complete environment theorem inventory.
expected_path=root/'certificates/lean-axioms.json'
if expected_path.exists():
    assert observed==json.loads(expected_path.read_text())['theorems'],'Theorem/axiom inventory differs'
sections={};current=None
for line in dep_text.splitlines():
    if line.startswith('CP_DEPENDENCIES '):
        current=line.split(' ',1)[1];assert current not in sections;sections[current]=[]
    elif current and line.startswith('CP.'): sections[current].append(line)
expected=re.findall(r'^#cp_project_dependencies (\S+)',(root/'lean/tools/Dependencies.lean').read_text(),re.M)
assert set(expected)==set(sections),(set(expected)-set(sections))
core=['CP.Kernel.omega_mul_J_sub_C','CP.Kernel.omega_inverse_eq_J_sub_C',
      'CP.Kernel.odd_deleted_inverse','CP.Kernel.omega_odd_rank',
      'CP.Connection.even_connection_native','CP.Connection.odd_connection_native',
      'CP.StageOne.even_finite_bridge','CP.StageOne.odd_finite_bridge']
for name in core:
    assert name in observed and name in sections,name
    assert not any('NormalizationInput' in n for n in sections[name]),name
for parity in ['even','odd']:
    name=f'CP.StageOne.{parity}_normalized'
    assert name in observed and name in sections,name
    assert any(f'{parity.capitalize()}NormalizationInput' in n for n in sections[name]),name
print(json.dumps({'passed':True,'theorem_declarations':len(observed),
    'axioms':sorted(set().union(*map(set,observed.values()))),'dependency_roots':len(sections),
    'unconditional_core_roots':core,'normalization_interfaces_separated':True},indent=2))
