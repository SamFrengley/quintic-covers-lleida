#!/usr/bin/env python3
"""Exact combinatorial expansion of Bhargava IV (35)--(37).
This is an offline derivation, not a dependency of the Magma package.
"""
from itertools import permutations, combinations, product
from collections import defaultdict
from functools import lru_cache
from math import gcd
import json, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
perms=list(permutations(range(5)))
def sign(p):return (-1)**sum(a>b for i,a in enumerate(p) for b in p[i+1:])
signs={p:sign(p) for p in perms}
first=[[p for p in perms if p[0]==i] for i in range(5)]
slots={(a,b):[p for p in perms if p[1]==a and p[3]==b] for a,b in product(range(5),repeat=2)}
edges=list(combinations(range(5),2)); ei={e:i for i,e in enumerate(edges)}
minors=list(combinations(range(10),4)); mi={m:i for i,m in enumerate(minors)}
@lru_cache(None)
def delta(pairs):
 s=1;e=[]
 for a,b in pairs:
  if a==b:return -1,0
  if a>b:a,b=b,a;s=-s
  e.append(ei[a,b])
 if len(set(e))<4:return -1,0
 return mi[tuple(sorted(e))],s*sign(e)
def clean(d):return {k:v for k,v in d.items() if v}
@lru_cache(None)
def P(i,a,b,c,d):
 out=defaultdict(int)
 for p in first[i]:
  e,s=delta(((a,p[1]),(b,p[2]),(p[3],p[4]),(c,d)))
  if s:out[e]+=signs[p]*s
 return clean(out)
@lru_cache(None)
def U(k,a,b,c):
 out=defaultdict(int)
 for p in first[a]:
  for q in slots[b,c]:
   e,s=delta(((k,p[1]),(q[0],p[2]),(p[3],p[4]),(q[2],q[4])))
   if s:out[e]+=signs[p]*signs[q]*s
 return clean(out)
@lru_cache(None)
def N(i,j,k):
 out=defaultdict(int)
 for p in perms:
  a,b,c,d,e=p;s=signs[p]
  for f in range(5):
   A=P(i,f,b,c,d)
   if not A:continue
   for g,h in product(range(5),repeat=2):
    B=P(j,a,g,h,e)
    V=U(k,f,g,h)
    if not B or not V:continue
    for x,cx in A.items():
     for y,cy in B.items():
      for z,cz in V.items():
       out[tuple(sorted((x,y,z)))]+=s*cx*cy*cz
 return clean(out)
def add(*terms):
 out=defaultdict(int)
 for s,d in terms:
  for k,v in d.items():out[k]+=s*v
 return clean(out)
if __name__=='__main__':
 start=time.time()
 forms={
  'distinct':N(0,1,2),
  'square_other':N(0,0,1),
  'difference':add((1,N(0,1,1)),(-1,N(0,2,2))),
  'square_diagonal':add((1,N(0,0,0)),(-1,N(0,1,1)),(-1,N(0,2,2)))
 }
 for name,F in forms.items():
  G=gcd(*F.values());print(name,len(F),'content',G,'divisible2304',all(v%2304==0 for v in F.values()),flush=True)
 output={'edges':edges,'minors':minors,'denominator':2304,'forms':{k:[[v,*m] for m,v in sorted(F.items())] for k,F in forms.items()}}
 (ROOT/'tests/fixtures/resolvent_raw_minors.json').write_text(json.dumps(output))
 print('seconds',time.time()-start,flush=True)

@lru_cache(None)
def straighten_pair(ia,ib):
 A=minors[ia]; B=minors[ib]
 if all(a<=b for a,b in zip(A,B)):return {(ia,ib):1}
 r=next(i for i in range(4) if A[i]>B[i]) # 0 based
 head=A[:r]; tail=B[r+1:]; U=A[r:]+B[:r+1]; length=4-r
 assert len(U)==5 and len(set(U))==5
 out=defaultdict(int)
 for sel in combinations(range(5),length):
  rest=tuple(i for i in range(5) if i not in sel)
  X=head+tuple(U[i] for i in sel)
  Y=tuple(U[i] for i in rest)+tail
  if len(set(X))<4 or len(set(Y))<4:continue
  coeff=sign(sel+rest)*sign(X)*sign(Y)
  key=tuple(sorted((mi[tuple(sorted(X))],mi[tuple(sorted(Y))])))
  out[key]+=coeff
 orig=out.pop((ia,ib))
 assert orig in (-1,1), (ia,ib,orig)
 assert all(key<(ia,ib) for key in out)
 return {key:-value*orig for key,value in out.items() if value}
@lru_cache(None)
def straighten(m):
 for i in range(len(m)-1):
  A=minors[m[i]];B=minors[m[i+1]]
  if any(a>b for a,b in zip(A,B)):
   out=defaultdict(int)
   for pair,c in straighten_pair(m[i],m[i+1]).items():
    mm=tuple(sorted(m[:i]+pair+m[i+2:]))
    for key,v in straighten(mm).items():out[key]+=c*v
   return clean(out)
 return {m:1}
if __name__=='__main__':
 result={}
 for name,F in forms.items():
  out=defaultdict(int)
  for m,c in F.items():
   for k,v in straighten(m).items():out[k]+=c*v
  out=clean(out)
  print('straight',name,len(out),'content',gcd(*out.values()),'seconds',time.time()-start,flush=True)
  assert all(c%2304==0 for c in out.values())
  result[name]=[[c//2304,*m] for m,c in sorted(out.items())]
 output={'edges':edges,'minors':minors,'forms':result,'denominator':1}
 (ROOT/'tests/fixtures/resolvent_integral_minors.json').write_text(json.dumps(output))
 print('done',time.time()-start,flush=True)


if __name__ == '__main__':
    from write_resolvent_data import write_data
    write_data(output, ROOT/'src/data')
    print('Regenerated integral fixtures and separate Magma data modules.', flush=True)
