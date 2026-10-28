"""Structural/textual checks. This is deliberately NOT described as a Magma compiler."""
from __future__ import annotations
import json
import re
from pathlib import Path
from itertools import combinations, permutations
from math import comb

ROOT = Path(__file__).resolve().parents[1]


def clean(text: str) -> str:
    text = re.sub(r'/\*.*?\*/|//[^\n]*', '', text, flags=re.S)
    text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
    return re.sub(r'(^intrinsic[^\{]*)\{.*?\}', r'\1', text, flags=re.M|re.S)


def blocks(text: str):
    pattern = r'^(function|procedure|intrinsic)\s+([^\(\s]+).*?^\s*end \1;'
    return list(re.finditer(pattern, text, flags=re.M|re.S))


def edge_rank(i: int, j: int) -> int:
    return (i-1)*5-(i-1)*i//2+j-i


def minor_rank(es: tuple[int, ...]) -> int:
    rank, previous = 1, 0
    for k, e in enumerate(es, 1):
        rank += sum(comb(10-j, 4-k) for j in range(previous+1, e))
        previous = e
    return rank


def audit() -> dict:
    files = sorted((ROOT/'src').rglob('*.m'))
    texts = {p.relative_to(ROOT): p.read_text() for p in files}
    all_text = '\n'.join(texts.values())
    declaration = re.search(r'declare attributes FinFlatCov:(.*?);', all_text, re.S)[1]
    attrs = set(re.findall(r'\b\w+\b', declaration))
    public = attrs-{'_Data'}
    assert public == {'Degree','Model','CoefficientRing','ProjectiveBase','Embedding',
                      'Twisted','StructureConstants','Discriminant',
                      'DefiningPolynomials','UnderlyingScheme'}
    records = dict(re.findall(r'FFC(\w+) := recformat<(.*?)>;', all_text, re.S))
    records = {group:set(re.findall(r'\w+', value)) for group,value in records.items()}
    forbidden = ['BaseKind', 'CorrectedSexticResolvent', 'CreateFiniteFlatCover',
                 'AssumeResolution', 'ActionConvention', 'ToLower', 'FFCProjectiveFlag']
    code = clean(all_text)
    assert not re.search(r"\bBase\s*:=", code)
    for word in forbidden:
        assert not re.search(r'\b'+word+r'\b', code), word
    for first, group, field in re.findall(r'`(\w+)(?:`(\w+))?(?:`(\w+))?', code):
        assert first in attrs, first
        if first == '_Data' and group:
            assert group in records['Data'], group
            if field: assert field in records[group], (group,field)
    sizes = {str(p):len(t.splitlines()) for p,t in texts.items()}
    assert max(sizes.values()) <= 500
    # No dependent multi-generator comprehension of the reported faulty form.
    assert not re.search(r':[^;\n]*\bi in \[[^\]]*\],\s*j in \[i', code)
    naming = (ROOT/'src/core/names.m').read_text()
    assert 'P<[X]> := PolynomialRing(R,n);' in naming
    primes_source = (ROOT/'src/base_change/primes.m').read_text()
    projective_source = (ROOT/'src/base_change/projective.m').read_text()
    assert 'FFCBaseCoordinateNames(R)' in primes_source
    assert 'FFCNamedFunctionField(F,n,names)' in primes_source
    assert 'FFCNamedPolynomialRing(F,n,names)' in primes_source
    assert 'FFCBaseCoordinateNames(R)' in projective_source
    assert 'names[free]' in projective_source

    # A homogeneous prime fibre uses the original degree-one generators,
    # not the affine ratio named s alongside a retained scaling variable t.
    branch = primes_source.split('if C`ProjectiveBase then',1)[1]
    branch = branch.split('/* The genuine Proj residue field',1)[0]
    assert 'FFCNamedFunctionField(k,1,[names[2]])' in branch
    assert 'Evaluate(f,[U.1,U!F.1])' in branch
    assert 'FFCMapWithImages(R,K,[a,K!F.1])' in branch
    assert 'rho' not in branch
    schemes_source = (ROOT/'src/geometry/schemes.m').read_text()
    affine_scheme = schemes_source.split('function FFCNativeAffineBaseScheme',1)[1]
    affine_scheme = affine_scheme.split('end function;',1)[0]
    assert 'ProjectiveSpace(Parent(Q[1]))' in affine_scheme
    assert 'return Scheme(P,Q),P;' in affine_scheme
    assert 'AssignNames(~T,[Sprint(Name(P,i))' in schemes_source

    pairs = (ROOT/'src/constructors/polynomials.m').read_text()
    assert '&cat[[<i,j> : j in [i..n-2]] : i in [0..n-2]]' in pairs
    assert '&cat[[<i,j> : j in [i..m]] : i in [0..m]]' in pairs

    # The public model constructors all agree on the default presentation.
    headers = re.findall(r'^intrinsic FiniteFlatCover\(.*?-> FinFlatCov', all_text, re.M|re.S)
    assert len(headers) == 4
    assert all('Embedding := "Model"' in h for h in headers)
    algebra_source = '\n'.join(t for p,t in texts.items() if str(p).startswith('src/algebra/'))
    assert not re.search(r'`Embedding\s*:=', clean(algebra_source))
    assert 'FFCCheckEquationShape(C,C`DefiningPolynomials,C`Embedding,C`ProjectiveBase)' in all_text
    assert 'intrinsic FiniteFlatCoverVersion()' in all_text

    # The matrix-descent comprehension must reference the matrix entry explicitly.
    descent_text = (ROOT / 'src/actions/descent.m').read_text()
    assert 'FFCDescendElement(M[i,j],R,' in descent_text
    assert 'FFCDescendElement(a,R,Sprintf("%o entry (%o,%o)"' not in descent_text

    # Module imports must resolve, name actual package-local exports, and be acyclic.
    exports, imports, dependencies = {}, {}, {}
    for path,text in texts.items():
        exports[path] = set(re.findall(r'^(?:function|procedure)\s+(\w+)', text, re.M))
        exports[path] |= set(re.findall(r'^(FFC\w+)\s*:=', text, re.M))
        imports[path] = {}
        for name,syms in re.findall(r'import "([^"]+)":\s*([^;]+);', text):
            target = (ROOT/path.parent/name).resolve().relative_to(ROOT)
            assert target in texts, (path,target)
            imports[path][target] = set(re.findall(r'\w+',syms))
        dependencies[path] = set(imports[path])
    for path,imp in imports.items():
        available = set(exports[path])
        for target,names in imp.items():
            assert names <= exports[target], (path,target,names-exports[target])
            available |= names
        local_code = clean(texts[path])
        used = set(re.findall(r'\bFFC\w+\b',local_code))
        # Record identifiers are local to the type definition module.
        if str(path).endswith('core/type.m'):
            available |= {'FFC'+g for g in records}
        assert used <= available, (path,used-available)
    seen,active = set(),set()
    def visit(path):
        assert path not in active, path
        if path in seen: return
        active.add(path)
        for other in dependencies[path]: visit(other)
        active.remove(path);seen.add(path)
    for path in texts: visit(path)
    ordered=[Path(x) for x in re.findall(r'src/[^\s{}]+\.m',(ROOT/'spec').read_text())]
    assert len(ordered)==len(set(ordered))==len(files)
    assert set(ordered)==set(texts)
    position={p:i for i,p in enumerate(ordered)}
    for p,ds in dependencies.items():
        assert all(position[d]<position[p] for d in ds),p

    # Expensive getter call sites: direct calls only, not a runtime interception.
    intrinsic_count = 0
    disc_callers = []
    for path,text in texts.items():
        parsed = blocks(text)
        assert len(parsed)==len(re.findall(r'^(?:function|procedure|intrinsic)\b',text,re.M)),path
        for match in parsed:
            kind,name = match[1],match[2]
            body = clean(match[0]).split('\n',1)[1]
            intrinsic_count += kind=='intrinsic'
            if re.search(r'(?<![A-Za-z`])(?:TraceDiscriminant|Discriminant)\(',body):
                assert name in {'Discriminant','VerifyResolvent'}, (path,name)
                disc_callers.append(name)
                if name=='VerifyResolvent':
                    assert 'CheckDiscriminant := false' in match[0]
                    assert body.index('if CheckDiscriminant then')<body.index('TraceDiscriminant(')
            if str(path).startswith('src/constructors/'):
                assert not re.search(r'\b(?:IsModelFiniteFlat|UnderlyingScheme|ModelScheme|'
                                     r'ResolutionMaps|VerifyResolution|Resolvent|'
                                     r'ConjecturalSexticResolvent|TracePairing)\(',body), (path,name)
                if 'IsAssociative(C)' in body:
                    assert 'if CheckAlgebra then' in body or 'if check then' in body
            if name in {'Model','CachedComputations','Degree','BaseRing','ProjectiveBase',
                        'BundleWeights','TschirnhausenInvariants','FirstSyzygyInvariants',
                        'FFCAlgebraBundleWeights','FFCBinaryModelWeights','FFCBinaryCoefficientWeights'}:
                assert not re.search(r'\b(?:StructureConstants|ResolutionMaps|ModelPolynomials|'
                                     r'DefiningPolynomials|UnderlyingScheme|Discriminant)\(',body), name
    # Independently exhaust all labels for the optimized integer ranking functions.
    edges=list(combinations(range(1,6),2))
    minors=list(combinations(range(1,11),4))
    assert [edge_rank(*e) for e in edges] == list(range(1,11))
    assert [minor_rank(m) for m in minors] == list(range(1,211))
    permuted = 0
    for p in permutations(range(1,6)):
        for minor in minors:
            es=[]
            for e in minor:
                i,j=sorted((p[edges[e-1][0]-1],p[edges[e-1][1]-1]))
                es.append(edge_rank(i,j))
            es=tuple(sorted(es))
            assert minor_rank(es)==minors.index(es)+1
            permuted+=1
    native = list((ROOT/'tests').rglob('*.m'))+list((ROOT/'examples').glob('*.m'))
    for path in native:
        s=path.read_text()
        for name in re.findall(r'load "([^"]+)";',s): assert (ROOT/name).is_file(),(path,name)
        assert not re.search(r'\b(?:BaseKind|CreateFiniteFlatCover|CorrectedSexticResolvent|AssumeResolution)\b',clean(s)),path
        assert len(s.splitlines())<=500,path
    return {'source_modules':len(files),'maximum_source_lines':max(sizes.values()),
            'maximum_algorithm_lines':max(v for p,v in sizes.items() if '/data/' not in p),
            'public_attributes':sorted(public),'implementation_record_attributes':['_Data'],
            'undefined_fields_or_imports':[], 'import_graph_acyclic':True,
            'intrinsic_blocks_checked':intrinsic_count,
            'discriminant_getter_callers':disc_callers,
            'constructor_direct_expensive_calls':False,
            'legacy_Base_option_removed':True, 'coordinate_ring_X_names':True,
            'base_change_names_preserved':True,
            'homogeneous_prime_images_not_ratios':True,
            'native_ambient_uses_named_polynomial_ring':True, 'split_invariants_do_not_call_expensive_getters':True,
            'permuted_minor_rank_cases':permuted,
            'native_files_checked_as_text':len(native),
            'uniform_model_constructor_defaults':True,
            'algebra_accessors_do_not_assign_embedding':True,
            'cached_equation_shapes_checked':True,
            'native_compilation_or_execution':False}

if __name__ == '__main__':
    print(json.dumps(audit(),indent=2))
