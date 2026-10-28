"""Independent exact resolvent checks. No Magma code is executed here."""
from __future__ import annotations
from itertools import combinations, permutations
from pathlib import Path
from random import Random
from functools import lru_cache
import json
import sympy as sp
from reference_checks import blank, put, constants0, sign, quintic, quartic, disc, associative, alt, quintic_model
from action_reference import cubic, cubic_action, quintic_action, quartic_action
from resolution_reference import basis_transform

HERE=Path(__file__).resolve().parent
DATA=json.loads((HERE/'fixtures/resolvent_integral_minors.json').read_text())
EDGES=[tuple(x) for x in DATA['edges']]; MINORS=[tuple(x) for x in DATA['minors']]
EI={e:i for i,e in enumerate(EDGES)}; MI={m:i for i,m in enumerate(MINORS)}
SEEDS=DATA['forms']
@lru_cache(None)
def remap(p):
 out=[]
 for minor in MINORS:
  es=[];sgn=sign(p)
  for e in minor:
   a,b=EDGES[e];a,b=p[a],p[b]
   if a>b:a,b=b,a;sgn=-sgn
   es.append(EI[a,b])
  sgn*=sign(es);out.append((MI[tuple(sorted(es))],sgn))
 # NOTE det(permutation) applies once to the degree-three polynomial.
 # Including it in every transformed minor applies it three times = once.
 return out

def minors(A):
 return [sp.det(sp.Matrix([[A[r][EDGES[e][0]][EDGES[e][1]] for r in range(4)] for e in es])) for es in MINORS]

def sextic(A,mod=None):
 delta=minors(A)
 if mod:delta=[int(v)%mod for v in delta]
 cache={}
 def F(name,prefix):
  p=tuple(prefix)+tuple(i for i in range(5) if i not in prefix)
  if p not in cache:cache[p]=[sg*delta[e] for e,sg in remap(p)]
  ds=cache[p]
  val=sum(c*ds[a]*ds[b]*ds[d] for c,a,b,d in SEEDS[name] if ds[a] and ds[b] and ds[d])
  return val%mod if mod else sp.expand(val)
 T=blank(6);anchors=[1,0,3,2,3]
 for i in range(5):
  for j in range(i+1,5):
   for k in range(5):
    if k not in (i,j):put(T,i+1,j+1,k+1,F('distinct',[i,j,k]))
  for j in range(5):
   if j!=i:put(T,i+1,i+1,j+1,F('square_other',[i,j]))
  k=anchors[i]
  for j in range(5):
   if j not in (i,k):put(T,i+1,j+1,j+1,F('difference',[i,j,k]))
 for i in range(5):
  j,k=[r for r in range(5) if r!=i][:2]
  put(T,i+1,i+1,i+1,sp.expand(T[i+1][j+1][j+1]+T[i+1][k+1][k+1]+F('square_diagonal',[i,j,k])))
 T=constants0(T)
 if mod:T=[[[int(v)%mod for v in row] for row in plane] for plane in T]
 return T

def quadratic_parameters(coeff):
 a,b,c,d=coeff
 return b*c-9*a*d,a*c**3+b**3*d+27*a*a*d*d-9*a*b*c*d

def quadratic_resolvent(coeff):
 t,n=quadratic_parameters(coeff);T=blank(2);put(T,1,1,0,-n);put(T,1,1,1,t);return T

def sextic_transport(T,L):
 n=6;B=sp.diag(sp.ones(1),L);U=basis_transform(T,B);H=sp.eye(n)
 for i,a in enumerate([2,1,4,3,4],1):H[i,0]=-U[i][a][a]
 B=H*B
 return basis_transform(T,B),B

def split_model():
 A=[]
 for i in range(4):
  M=sp.zeros(5)
  for j in [(i-1)%5,(i+1)%5]:M[i,j]+=1;M[j,i]-=1
  A.append(M.tolist())
 return A

def run_smoke():
 AA=split_model();print('split quintic disc',disc(quintic(AA)),flush=True)
 S=sextic(AA);print('split sextic disc',disc(S),'assoc',associative(S),flush=True)
 for f in [[-1,-1,0,0,0,1],[0,0,0,0,0,1]]:
  A=quintic_model(f);Q=quintic(A);S=sextic(A)
  print('monogenic',f,'discQ',disc(Q),'discS',disc(S),flush=True)
  assert associative(S)[0]
  assert disc(S)==(16*disc(Q))**3


def cubic_of_quartic(AB):
    u,v=sp.symbols('u v');A,B=[sp.Matrix(M) for M in AB];M=u*A+v*B
    f=sp.expand(4*M[0,0]*M[1,1]*M[2,2]+M[0,1]*M[0,2]*M[1,2]
        -M[0,0]*M[1,2]**2-M[1,1]*M[0,2]**2-M[2,2]*M[0,1]**2)
    return [f.coeff(u,3-i).coeff(v,i) for i in range(4)]


def table_mod(T,p):
    return [[[int(v)%p for v in row] for row in plane] for plane in T]


def compare_split_lattice(T):
    """Independent integral ring identification, not just equal discriminants."""
    F=json.loads((HERE/'fixtures/split_sextic_lattice.json').read_text())
    B=sp.Matrix(F['basis_images_in_Z6'])
    assert B[0,:]==sp.ones(1,6) and abs(B.det())==64
    for row in B.tolist():
        assert all((v-row[0])%2==0 for v in row)
        assert (sum(row)-2*row[0])%4==0
    # Parity imposes index 2^5; the additional mod-4 condition doubles it.
    # Therefore this full-rank contained lattice of index 64 is equal to it.
    assert sum(all((v-row[0])%2==0 for v in row) and (sum(row)-2*row[0])%4==0
               for row in __import__('itertools').product(range(4),repeat=6))==4**6//64
    for i in range(6):
        for j in range(6):
            lhs=sp.Matrix(1,6,[B[i,k]*B[j,k] for k in range(6)])
            rhs=sum((T[i][j][k]*B[k,:] for k in range(6)),sp.zeros(1,6))
            assert lhs==rhs
    return {'explicit_integral_ring_isomorphism':True,'index_in_Z6':64,
            'multiplication_identities':36,'discriminant':int(disc(T))}


def verify_seed_derivation():
    """Re-expand (35), reapply integral Pluecker identities, compare source."""
    import importlib.util
    from collections import defaultdict
    p=HERE.parent/'tools/build_resolvent_formulas.py'
    spec=importlib.util.spec_from_file_location('resolvent_formula_derivation',p)
    gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    raw={'distinct':gen.N(0,1,2),'square_other':gen.N(0,0,1),
         'difference':gen.add((1,gen.N(0,1,1)),(-1,gen.N(0,2,2))),
         'square_diagonal':gen.add((1,gen.N(0,0,0)),(-1,gen.N(0,1,1)),(-1,gen.N(0,2,2)))}
    raw_fixture=json.loads((HERE/'fixtures/resolvent_raw_minors.json').read_text())['forms']
    result={}
    target_counts={'distinct':[4,4,6,5,5],'square_other':[3,6,5,5,5],
                   'difference':[4,5,5,5,5],'square_diagonal':[4,5,5,5,5]}
    for name,F in raw.items():
        assert [[v,*m] for m,v in sorted(F.items())]==raw_fixture[name]
        out=defaultdict(int)
        for m,c in F.items():
            for k,v in gen.straighten(m).items():out[k]+=c*v
        out=gen.clean(out)
        assert all(v%2304==0 for v in out.values())
        assert [[c//2304,*m] for m,c in sorted(out.items())]==SEEDS[name]
        # Universal multiweight identity, for arbitrary split bundle weights.
        for c,*ms in SEEDS[name]:
            counts=[0]*5
            for minor in ms:
                for e in MINORS[minor]:
                    for i in EDGES[e]:counts[i]+=1
            assert counts==target_counts[name]
        result[name]={'raw_monomials':len(F),'integral_monomials':len(out),
                      'coefficientwise_division_by_2304_verified':True,
                      'universal_bundle_multiweights_verified':True}
    import re
    for name, terms in SEEDS.items():
        text=(HERE.parent/f'src/data/seed_{name}.m').read_text()
        actual=[[int(x) for x in row.split(',')]
                for row in re.findall(r'<(-?\d+,\d+,\d+,\d+)>',text)]
        expected=[[c,a+1,b+1,d+1] for c,a,b,d in terms]
        assert actual == expected
    result['embedded_magma_constants_match_rederived_formulas']=True
    return result


def run():
    from reference_checks import matrices
    from resolution_reference import transport
    rng=Random(4022026);out={}
    print('Universal cubic discriminant algebra and integral seed derivation',flush=True)
    a,b,c,d,z=sp.symbols('a b c d z');coeff=[a,b,c,d]
    t,n=quadratic_parameters(coeff)
    assert sp.expand(t*t-4*n-sp.discriminant(a*z**3+b*z*z+c*z+d,z))==0
    assert sp.expand(disc(cubic(coeff))-(t*t-4*n))==0
    out['cubic_universal_identity']=True
    # Two etale cubics over F2 have the same discriminant, different resolvents.
    split=quadratic_resolvent([1,0,1,1]);nonsplit=quadratic_resolvent([1,1,1,0])
    assert (split[1][1][1]%2,-split[1][1][0]%2)==(1,0)
    assert (nonsplit[1][1][1]%2,-nonsplit[1][1][0]%2)==(1,1)
    assert disc(split)%2==disc(nonsplit)%2==1
    out['characteristic_2_discriminant_algebra_not_determined_by_discriminant']=True
    for _ in range(10):
        co=[rng.randrange(-3,4) for _ in range(4)]
        C=cubic(co);D=quadratic_resolvent(co)
        assert disc(C)==disc(D) and associative(D)[0]
        B=sp.eye(3);B[1,0]=rng.randrange(-4,5);B[2,0]=rng.randrange(-4,5)
        U=basis_transform(C,B)
        extracted=[-U[1][1][2],U[1][1][1]-2*U[1][2][2],
                   -U[2][2][2]+2*U[1][2][1],U[2][2][1]]
        assert extracted==co
        for g in [sp.Matrix([[2,1],[0,1]]),sp.Matrix([[0,1],[1,0]])]:
            for tw in [True,False]:
                new=quadratic_resolvent(cubic_action(co,g,tw))
                assert disc(new)==g.det()**(2 if tw else 6)*disc(D)
    out['cubic_samples_with_normalization_and_twisted_untwisted_characters']=10
    print('Quartic -> cubic -> quadratic, including zero tensors',flush=True)
    ABs=[[[[0]*3 for _ in range(3)] for _ in range(2)]]
    for _ in range(8):
        AB=[]
        for j in range(2):
            A=sp.zeros(3)
            for i,k in combinations(range(3),2):A[i,k]=A[k,i]=rng.randrange(-3,4)
            for i in range(3):A[i,i]=rng.randrange(-3,4)
            AB.append(A.tolist())
        ABs.append(AB)
    for AB in ABs:
        co=cubic_of_quartic(AB);C=quartic(*AB);E=cubic(co);D=quadratic_resolvent(co)
        assert disc(C)==disc(E)==disc(D)
        for p in [2,3,5,7]:
            BB=[[[a%p for a in row] for row in A] for A in AB]
            assert all((a-b)%p==0 for a,b in zip(cubic_of_quartic(BB),co))
            assert disc(cubic(cubic_of_quartic(BB)))%p==disc(C)%p
        g=sp.Matrix([[2,1,0],[0,1,1],[0,0,1]])
        h=sp.Matrix([[2,1],[0,1]])
        for tw in [True,False]:
            factor=1/h.det() if tw else 1
            BB=[(factor*sp.Matrix(M)).tolist() for M in quartic_action(AB,g,h)]
            EE=cubic(cubic_of_quartic(BB))
            L=factor**3*g.det()**2*h.det()*h
            assert transport(E,L)==EE
    out['quartic_chains_with_covariance_and_four_small_primes']=len(ABs)
    out['integral_seed_derivation']=verify_seed_derivation()
    print('Bhargava sextic orders, reductions, and split-order identification',flush=True)
    As=[split_model(),quintic_model([-1,-1,0,0,0,1]),quintic_model([0,0,0,0,0,1]),
        [alt([0]*10) for _ in range(4)]]
    As.extend([[alt([rng.randrange(-2,3) for _ in range(10)]) for _ in range(4)] for _ in range(4)])
    As.append([[[2*v for v in row] for row in A] for A in As[0]])
    sextics=[]
    for A in As:
        C=quintic(A);S=sextic(A);sextics.append(S)
        assert associative(S)[0] and disc(S)==(16*disc(C))**3
        for p in [2,3,5,7]:
            B=[[[int(a)%p for a in row] for row in M] for M in A]
            Sp=sextic(B,mod=p)
            assert Sp==table_mod(S,p)
            assert associative(Sp,p)[0] and disc(Sp)%p==(16*disc(C))**3%p
    out['quintic_to_sextic_integral_samples']=len(As)
    out['fresh_small_characteristic_evaluations']={'count':len(As)*4,'primes':[2,3,5,7],
          'uses_no_inverse_of_2_or_3':True}
    out['split_order']=compare_split_lattice(sextics[0])
    g=sp.eye(5);g[0,0]=4;g[0,1]=1;g[2,3]=-1
    h=sp.eye(4);h[1,1]=2;h[0,2]=1;h[1,3]=2
    gp=sp.eye(5);gp.row_swap(0,1);gp[2,3]=1
    hp=sp.eye(4);hp[1,2]=1
    counter=0
    for A,S in list(zip(As,sextics))[:3]+list(zip(As,sextics))[4:6]:
        for gg,hh in [(g,h),(gp,hp)]:
            for tw in [True,False]:
                if tw and gg.det()!=hh.det()**2: continue
                fac=1/hh.det() if tw else 1
                B=quintic_action(A,gg,hh,twist=tw)
                L=fac**12*gg.det()**5*hh.det()**3*gg.inv().T
                E,Basis=sextic_transport(S,L);D=sextic(B)
                assert E==D
                assert disc(D)==L.det()**2*disc(S)
                assert matrices(E)==matrices(D)
                counter+=1
    out['sextic_twisted_untwisted_and_orientation_transport_cases']=counter
    # An actual polynomial-family calculation over Z[u], not only specializations.
    u=sp.Symbol('u');A=quintic_model([-u,-1,0,0,0,1]);S=sextic(A);M=matrices(S)
    for i in range(6):
        for j in range(6):
            difference=M[i]*M[j]-sum((S[i][j][k]*M[k] for k in range(6)),sp.zeros(6))
            assert difference.applyfunc(sp.expand)==sp.zeros(6)
    source_disc=sp.factor(disc(quintic(A)));target_disc=sp.factor(disc(S))
    assert sp.expand(target_disc-(16*source_disc)**3)==0
    out['Z_u_family']={'polynomial':'z^5-z-u','source_discriminant':str(source_disc),
        'sextic_trace_discriminant':str(target_disc),'all_multiplication_identities':True}
    out['native_magma_executed']=False
    return out

if __name__ == "__main__":
    result=run()
    (HERE/"resolvent-results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
