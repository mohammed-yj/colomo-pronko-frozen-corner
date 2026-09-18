"""Rebuild Appendix A ratios and compare every term with supplement S.1."""
from pathlib import Path
import json,re
import sympy as S

a,m=S.symbols('a m')
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'certificates/recurrence.json').read_text())
D=S.sympify(data['denominator'],locals={'a':a,'m':m})
terms=[S.sympify(t,locals={'a':a,'m':m}) for t in data['summands']]
u1=a*(2*m-a-1)/((m+a-1)*(m-a))
u2=a*(a-1)*(2*m-a)*(2*m-a-1)/((m+a-2)*(m+a-1)*(m-a)*(m-a+1))
v0=(m-a-1)*(2*m-2)*(2*m-3)/((m+a-1)*(2*m-a-2)*(2*m-a-3))
v1=a*(2*m-2)*(2*m-3)/((m+a-1)*(m+a-2)*(2*m-a-2))
v2=a*(a-1)*(2*m-2)*(2*m-3)/((m+a-1)*(m+a-2)*(m+a-3)*(m-a))
v3=v2*(a-2)*(2*m-a-1)/((m+a-4)*(m-a+1))
w2=a*(a-1)*(2*m-2)*(2*m-3)*(2*m-4)*(2*m-5)/((m+a-4)*(m+a-3)*(m+a-2)*(m+a-1)*(2*m-a-3)*(2*m-a-2))
beta=3*(3*m-7)*(3*m-5)/(4*(2*m-5)*(2*m-3))
rebuilt=[D,-2*D*u1,D*u2,-D*v0,S.Rational(3,2)*D*v1,S.Rational(3,2)*D*v2,-D*v3,-D*beta*w2]
assert len(terms)==8
for i,(lhs,rhs) in enumerate(zip(terms,rebuilt)):
    assert S.cancel(lhs-rhs)==0, ('summand',i)
    S.Poly(lhs,a,m,domain=S.ZZ)
assert S.Poly(sum(terms),a,m,domain=S.ZZ).is_zero
assert S.cancel(1-2*u1+u2-v0+S.Rational(3,2)*(v1+v2)-v3-beta*w2)==0
# Verify a second representation extracted from the preserved Lean statement.
lean=(root/'lean/CP/Polynomial.lean').read_text()
expr=lean.split('theorem recurrence_certificate (a m : ℚ) :',1)[1].split('= 0 := by',1)[0]
lean_terms=re.split(r'\n    (?=[+-] )',expr.strip())
assert len(lean_terms)==8
for lhs,rhs in zip(lean_terms,terms):
    assert S.expand(S.sympify(lhs,locals={'a':a,'m':m})-rhs)==0
print('PASS: eight integer-polynomial terms, Appendix A ratios, zero sum, and preserved Lean certificate agree exactly.')
print('General denominator nonvanishing uses the paper proof for m>=5, 0<=a<=floor((m+1)/2).')
