"""Check the integral direct-table action against polynomial substitution.
This proves an algebraic identity; it does not execute the Magma implementation.
"""
from __future__ import annotations
import sympy as sp


def transform(A: sp.Matrix, g: sp.Matrix) -> sp.Matrix:
    n = A.rows
    B = sp.zeros(n)
    for a in range(n):
        B[a,a] = sum(A[i,i]*g[a,i]**2 for i in range(n))
        B[a,a] += sum(A[i,j]*g[a,i]*g[a,j]
                      for i in range(n) for j in range(i+1,n))
        for b in range(a+1,n):
            value = sum(2*A[i,i]*g[a,i]*g[b,i] for i in range(n))
            value += sum(A[i,j]*(g[a,i]*g[b,j]+g[a,j]*g[b,i])
                         for i in range(n) for j in range(i+1,n))
            B[a,b] = B[b,a] = value
    return B


def quadratic(A: sp.Matrix, x: list) -> sp.Expr:
    return sum(A[i,j]*x[i]*x[j] for i in range(A.rows) for j in range(i,A.rows))


def run() -> dict:
    symbols = sp.symbols('a0:6')
    A = sp.Matrix([[symbols[0],symbols[1],symbols[2]],
                   [symbols[1],symbols[3],symbols[4]],
                   [symbols[2],symbols[4],symbols[5]]])
    g = sp.Matrix(3,3,sp.symbols('g0:9'))
    x = sp.Matrix(sp.symbols('x0:3'))
    B = transform(A,g)
    assert sp.expand(quadratic(A,g.T*x)-quadratic(B,x)) == 0
    # The formula is over Z: coefficientwise identity implies every reduction.
    assert all(sp.Poly(entry,*symbols,*list(g)).domain == sp.ZZ for entry in B)
    return {'universal_coefficient_table_substitution_identity':True,
            'integer_coefficients_no_division':True,
            'characteristic_two_supported_by_integral_identity':True,
            'native_magma_executed':False}

if __name__ == '__main__':
    import json
    print(json.dumps(run(),indent=2))
