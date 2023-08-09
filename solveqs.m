function Geteq(q, mat: searchPole:=false)
    a,b,c,d:=Explode(Eltseq(mat));
    K:=Parent(a);
    assert GroundField(K) eq Rationals();
    n:=Degree(K);
    if searchPole then
        P:=PolynomialRing(K,n);
    else
        P:=PolynomialRing(K, n+1);
        z:=P.(n+1);
    end if;
    xs:=[];
    for i in [1..n] do
        xs:=Append(xs, P.i);
    end for;
    B:=Basis(K);
    x:=P!0;
    for i in [1..n] do
        x+:= xs[i]*B[i];
    end for;

    q1ev:=P!0;
    q1:=Numerator(q);
    coeffs1:=Coefficients(q1);
    deg:=Degree(q);
    n:=#coeffs1;
    for i in [1..n] do
        q1ev+:=coeffs1[i]*x^(i-1);
    end for;
    q2ev:=P!0;
    q2:=Denominator(q);
    coeffs2:=Coefficients(q2);
    n:=#coeffs2;
    for i in [1..n] do
        q2ev+:=coeffs2[i]*x^(i-1);
    end for;

    eq1:= c*q1ev+d*q2ev;
    if searchPole then
        return eq1;
    else
        eq2:= a*q1ev+b*q2ev-z*eq1;
        return eq2;
    end if;
end function;

function EqToNumberFieldEqs (equation)
    L1,L2:=CoefficientsAndMonomials(equation);
    K:=Parent(L1[1]);
    assert GroundField(K) eq Rationals();
    B:=Basis(K);
    n:=Degree(K);    
    m:=Rank(Parent(L2[1]));
    P:=PolynomialRing(Rationals(), m);
    eqs:=[];
    for i in [1..n] do
        eqs[i]:=P!0;
    end for;

    for i in [1..#L1] do
        x:=L2[i];
        coeffs:=Eltseq(L1[i]);
        for i in [1..n] do
            eqs[i]+:= P!(coeffs[i]*x);
        end for;
    end for;
    return eqs;
end function;

function VecToK(vec, K)
    B:=Basis(K);
    n:=Degree(K);
    x:=K!0;
    for i in [1..n] do
        x+:=vec[i]*B[i];
    end for;
    return x;
end function;

function ProjSchemeFromEqs(eqs)
    P:=Parent(eqs[1]);
    n:=Rank(P);
    PP:=AffineSpace(Rationals(), n);
    scheme:=Scheme(PP, eqs);
    return scheme;
end function;

function CheckPoint(P, quot, A)
    K:=Parent(A[1][1]);
    P1:=ProjectiveSpace(K, 1);
    quotMorph:=FFEltToActualMorph(quot, P1);
    morphA:=GL2MatToAut(A, P1);
    n:=Degree(K);
    
    x:=VecToK(P, K);

    pt:=P1![x, 1];
    comp:=quotMorph*morphA;
    return comp(pt);
end function;

// Apparently with affinespace, this doesn't work well. But proj. space should work better. So we try with z=1. But that's ofc. not the best thing.. maybe we can somehow use that y=1??