"""Exact regression checks reconstructed from the final paper, not historical logs.
Finite ranges provide consistency evidence, not proofs for arbitrary parameters.
"""
from functools import lru_cache
from itertools import combinations
from math import comb, factorial
import json
import sympy as S

x, y, z = S.symbols('x y z')


def check(value, label):
    if isinstance(value, S.MatrixBase):
        assert value == S.zeros(*value.shape), label
    else:
        assert S.cancel(value) == 0, (label, value)


@lru_cache(None)
def h(m):
    return S.Poly(sum(S.Rational(comb(m+a-1,m-1)*comb(2*m-a-2,m-1),
                                comb(3*m-2,m-1))*z**a for a in range(m)), z)


def A(n):
    return S.prod(S.Rational(factorial(3*j+1),factorial(n+j)) for j in range(n))


def choose(n,k):
    return comb(n,k) if 0 <= k <= n else 0


def K(q):
    return S.Matrix(q,q,lambda i,j:choose(i+j,i)+(-1)**i*choose(j,i)-(-1)**j*choose(i,j))


def G(q):
    return S.Matrix(q,q,lambda i,j:(-1)**(i+j)*choose(i+j,i))


def R(q):
    return S.eye(q)[:,::-1]


def E(q,s):
    return S.diag(*([0]*(q-s)+[1]*s))


def U(q):
    return S.Matrix(q,q,lambda i,j:(-1)**(j-i)*choose(q-1-i,j-i) if j>=i else 0)


def coefficient_matrix(p,q):
    p=S.Poly(p,x,y)
    return S.Matrix(q,q,lambda i,j:p.coeff_monomial(x**i*y**j))


def pfaffian(matrix):
    @lru_cache(None)
    def rec(indices):
        if not indices: return S.Integer(1)
        return sum((-1)**(j+1)*matrix[indices[0],indices[j]]*
                   rec(indices[1:j]+indices[j+1:]) for j in range(1,len(indices)))
    assert matrix.rows==matrix.cols and matrix.rows%2==0
    return rec(tuple(range(matrix.rows)))


def cp_matrix(n,s):
    r=n-s
    plus=[]; minus=[]
    for i in range(s):
        hi=h(r+i+1).as_expr()
        plus.append(S.Poly((1+(-1)**(i+1)*z)*(1-z)**i*hi,z))
        minus.append(S.Poly((1-(-1)**(i+1)*z)*(1-z)**i*hi,z))
    return S.Matrix(s,s,lambda i,j:sum(plus[i].nth(a)*minus[j].nth(b)*
        comb(i-a+j-b,i-a) for a in range(i+1) for b in range(j+1))/h(r+j+1).nth(0))


def asm_count(n,s):
    # A monotone-triangle row records columns with partial ASM column sum one.
    # A zero top-left s-square is equivalent to all entries of row s exceeding s.
    @lru_cache(None)
    def count(row):
        k=len(row)
        if k==s and any(v<=s for v in row): return 0
        if k==1: return 1
        return sum(count(up) for up in combinations(range(row[0],row[-1]+1),k-1)
                   if all(row[i]<=up[i]<=row[i+1] for i in range(k-1)))
    return count(tuple(range(1,n+1)))


def main():
    counts={}
    for m in range(1,21):
        hm=h(m).as_expr(); b=h(m).nth(0)
        check(hm.subs(z,1)-1,('h(1)',m))
        check(b-A(m-1)/A(m),('b',m))
        check(z**(m-1)*hm.subs(z,1/z)-hm,('reciprocity',m))
        check((1-z)**(m-1)*hm.subs(z,z/(z-1))-(1-z)**(2*m-1)*hm-
              (-1)**(m-1)*z**(2*m-1)*hm.subs(z,1-z),('fractional',m))
        if m>=3:
            check(h(m-1).nth(0)/b*(z-1)**2*hm-z**2*h(m-2).as_expr()-
                  (z-2)*(z+1)*(2*z-1)*h(m-1).as_expr()/2,('recurrence',m))
        if m>=2:
            rho=(z-1)/z
            check(hm.subs(z,rho)*h(m-1).as_expr()+(z-1)**2/z*hm*
                  h(m-1).as_expr().subs(z,rho)-b*z**(m-2)*(z*z-z+1),('adjacent',m))
    counts['refined_polynomials']='orders 1..20; normalization, reciprocity, fractional substitution, recurrence, adjacent identity'
    print('PASS refined polynomial identities',flush=True)
    for n in range(1,13):
        check(K(n).det()-A(n),('det K',n))
        T=S.Matrix(n,n,lambda i,j:(-1)**j*choose(i,j))
        B=R(n)*U(n)
        check(T*T-S.eye(n),('T involution',n))
        check(B*T-R(n)*B,('B T',n))
        check(B*B.T-G(n),('Gram',n))
        check(B*(K(n)-S.eye(n))*B.T-(R(n)+S.eye(n))*G(n)*(R(n)-S.eye(n)),('congruence',n))
        for s in range(n+1):
            kd=(K(n)-E(n,s)).det()
            if 2*s>n:check(kd,('forbidden',n,s))
            if n<=8:
                check(kd-asm_count(n,s),('independent ASM count',n,s))
                M=cp_matrix(n,s)
                # Each side is polynomial in lambda of degree at most s.
                # s+1 exact evaluations verify that polynomial for this n,s.
                for lam in range(s+1):
                    check(A(n)*(S.eye(s)-lam*M).det()-(K(n)-lam*E(n,s)).det(),('candidate',n,s,lam))
        print('PASS candidate/count n=',n,flush=True)
    counts['candidate']='n=1..8, every 0<=s<=n, equality as a polynomial in lambda via s+1 exact points'
    counts['independent_enumeration']='monotone-triangle dynamic counting, n=1..8, every 0<=s<=n'
    counts['binomial_and_forbidden']='n=1..12, all s; exact binomial identities and det K normalization'
    for N in range(1,7):
        q=2*N; b=h(N+1).nth(0)
        u=S.expand(x*h(N+1).as_expr().subs(z,1+x)); v=S.expand((1+x)*h(N).as_expr().subs(z,1+x))
        us=S.cancel(x**(N+1)*u.subs(x,1/x)); vs=S.cancel(x**(N+1)*v.subs(x,1/x))
        w=u*v.subs(x,y)-u.subs(x,y)*v
        ws=us*vs.subs(x,y)-us.subs(x,y)*vs
        den=b*b*(y-x)*(1+x+x*y)*(1+y+x*y)
        num=S.expand(w*ws-b*b*x**q*(y-x)*(1+x+x*y)+b*b*y**q*(y-x)*(1+y+x*y))
        c,rem=S.div(S.Poly(num,x,y),S.Poly(den,x,y))
        check(rem.as_expr(),('kernel divisibility',N))
        assert c.degree(x)<q and c.degree(y)<q
        C=coefficient_matrix(c.as_expr(),q)
        omega=G(q)*R(q)-R(q)*G(q)
        J=R(q)*G(q).inv()-G(q).inv()*R(q)
        check(C+C.T,('skew',N));check(R(q)*C*R(q)+C,('reflection',N))
        check(omega*(J-C)-S.eye(q),('even inverse',N))
        D=S.Matrix(N,N,lambda i,j:-C[i,j]-C[i,q-1-j])
        le=K(q)-E(q,N)
        check(S.eye(N)+le.inv()[N:,N:]-U(N).T*R(N)*D*R(N)*U(N),('even connection',N))
        oq=q+1
        O=coefficient_matrix((1+x)*(1+y)*c.as_expr()+x**q-y**q,oq)
        vp=S.Poly(S.expand(h(N+1).as_expr().subs(z,1+x)*us/b**2),x)
        nu=S.Matrix([vp.nth(i) for i in range(oq)])
        alpha=nu[N]; assert alpha>0
        Go=G(oq); Ro=R(oq); om=Go*Ro-Ro*Go
        Q=S.Matrix(oq,q,lambda i,j:int(i==j)+int(i==j+1))
        gamma=Ro*Go.inv()-Go.inv()*Ro-O
        e=S.Matrix([(-1)**i for i in range(oq)])
        check(Q.T*Go*Q-G(q),('compression',N))
        check(gamma-Q*omega.inv()*Q.T,('odd lift',N))
        check(om*nu,('null vector',N)); assert om.rank()==q
        check((e.T*nu)[0]-(-1)**N,('alternating dot nu',N))
        check(om*gamma-S.eye(oq)+e*nu.T/(e.T*nu)[0],('rank one defect',N))
        center=S.eye(oq)[:,N]; P=S.eye(oq)-nu*center.T/alpha
        keep=[i for i in range(oq) if i!=N]
        check(om.extract(keep,keep)*(P*gamma*P.T).extract(keep,keep)-S.eye(q),('deleted inverse',N))
        EE=S.Matrix(N+1,N+1,lambda i,j: -O[i,j]-O[i,q-j] if i<N and j<N else
                    O[i,N] if i<N else -2*nu[j] if j<N else alpha)
        So=EE[:N,:N]-EE[:N,N:]*EE[N:,:N]/alpha
        lo=K(oq)-E(oq,N)
        check(S.eye(N)+lo.inv()[N+1:,N+1:]-U(N).T*R(N)*So*R(N)*U(N),('odd connection',N))
        for s in range(N+1):
            even=(K(q)-E(q,s)).det(); odd=(K(oq)-E(oq,s)).det()
            check(even-le.det()*D[s:,s:].det(),('even relative',N,s))
            check(odd-lo.det()/alpha*EE[s:,s:].det(),('odd relative',N,s))
            check(even-A(N)**2*D[s:,s:].det(),('even normalized',N,s))
            check(odd-A(N)**2*EE[s:,s:].det(),('odd normalized',N,s))
            central=list(range(s,q-s))
            check((-1)**(N-s)*pfaffian(C.extract(central,central))-D[s:,s:].det(),('even Pfaffian folding',N,s))
            central=list(range(s,oq-s)); sub=O.extract(central,central); nv=nu.extract(central,[0])
            bordered=sub.row_join(nv).col_join((-nv.T).row_join(S.zeros(1,1)))
            check(pfaffian(bordered)-EE[s:,s:].det(),('odd Pfaffian folding',N,s))
        print('PASS even/odd kernels and bridges N=',N,flush=True)
    counts['kernels_and_bridges']='N=1..6, all s=0..N, polynomial division, inverse, lift, nullspace, center projection, connections, relative and normalized bridges, even/odd Pfaffian folding'
    print(json.dumps({'passed':True,'checks':counts},indent=2))


if __name__=='__main__': main()
