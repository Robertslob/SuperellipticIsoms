// Given a finite automorphism group G of PGL_2(K), this function returns a quotient morphism P1 --> P1=P1/G corresponding to the quotient of P1 by G 
function ComputeQuotientMorphismP1(mats)
    // I don't know how to not do this function field creation in such a stupid manner
    Q:= Parent(Eltseq(mats[1])[1]);
    P<x>:=PolynomialRing(Q);
    R<y>:=PolynomialRing(P);
    P1:=FunctionField(y);
    x := P1!x;
    poles :=0*Zeroes(x)[1];

    // We calculate the orbit of infinity under the matrices, which will give our poles divisor
    for mat in mats do        
        a,b,c,d := Explode(Eltseq(mat));
        if c ne 0 then
            f:= x-a/c;
            poles +:= Zeroes(f)[1];
        else 
            poles +:= Poles(x)[1];
        end if;
    end for;

    // We next need to find a point that does not lie in the orbit of infinity in order to use as base point for our zeroes divisor
    n := # mats;    
    zeroesBasePoint:= 0;
    for i:=0 to n do
        BasePlace := Zeroes(x-i)[1];
        polesSupport, indices := Support(poles);
        if not BasePlace in polesSupport then
            zeroesBasePoint := i;
            break;
        end if;
    end for;

    // We calculate the orbit of out zeroes base point under the matrices, which will give our zeroes divisor
    zeroes := 0*Zeroes(x)[1];
    for mat in mats do        
        a,b,c,d := Explode(Eltseq(mat));
        f := x-(a*zeroesBasePoint+b)/(c*zeroesBasePoint+d);
        zeroes +:= Zeroes(f)[1];
    end for;

    // We return the quotient morphism that corresponds to a function on P1 with rational divisor the zeroes minus the poles.
    b,f:= IsPrincipal(zeroes-poles);
    P<x>:= FunctionField(Q);
    f:= P!f;
    // Since the quotient morphism property does not change by multiplying with a scalar, we return it as a quotient of monic polynomials. This may come in handy for the field of definition of the quotient morphism.
    g:=Numerator(f);
    h:=Denominator(f);
    mu:=LeadingCoefficient(h)/LeadingCoefficient(g);
    f:=f*mu;
    return f;
end function;

// Input: GL_2(K)-matrix, P1_L for L/K some field ext.
// Output: Isomorphism of P1_L corresponding to this matrix.
function GL2MatToAut(mat, P1)
    a,b,c,d:=Explode(Eltseq(mat));
    x:= P1.1; y:=P1.2;
    return map<P1->P1 | [a*x+b*y, c*x+d*y]>;
end function;

// Given three tuples of K-points in P1, determines the corresponding matrix A in PGL_2(K) determined by these three points, i.e. for all tup in the tuples, A(tup[1])=tup[2].
// K-points need not be infty, and input values must be distinct
function DeterminePGL2MatrixFromThreeNonInfinitePoints(vals)
    K:=Parent(vals[1][1][1]);
    P1:=Curve(vals[1][1]);
    alphas:= [];
    betas:= [];
    for i:= 1 to 3 do
        alphas:= Append(alphas, vals[i][1][1]);
        betas:= Append(betas, vals[i][2][1]);
    end for;
    // B maps betas[1] to zero and betas[2] to infty, makes determining A easier
    B:= Matrix(K, 2, 2, [1, -betas[1], 1, -betas[2]]);
    mapB:= GL2MatToAut(B, P1);
    gam := mapB(P1![betas[3],1])[1];
    c:= (alphas[3]-alphas[1])/((alphas[3]-alphas[2])*gam);
    A:= Matrix(K, 2, 2, [1, -alphas[1], c, -alphas[2]*c]);
    return (B^-1)*A;
end function;

function HomogenizePoly(f, x, y, d)
    return &+[Coefficient(f,i)*x^i*y^(d-i) : i in [0..d]];
end function;

function FFEltToActualMorph(elt, P1)
    K:=BaseField(P1);
    elt:=FunctionField(K)!elt;
    f:=Numerator(elt);
    g:=Denominator(elt);
    d:=Degree(elt);
    x:=P1.1;
    y:=P1.2;
    f:=HomogenizePoly(f,x,y,d);
    g:=HomogenizePoly(g,x,y,d);
    return map<P1->P1 | [f,g]>;
end function;

function CheckWhetherPointInFirstTups (vals, P)
    n:=#vals;
    for i in [1..n] do
        if P eq vals[i][1] then
            return true;
        end if;
    end for;
    return false;
end function;

// Given maps f, g, A of P1 such that A lies in PGL_2(K) and there exists B such that B \circ f = g \circ A, return B.
// Does this by noting that f((i:1)) needs to get mapped to g(A(i:1)) for i some random value in K, and then finds the corresponding matrix determined by three such points.
// We ask in addition that both f and g \circ A do not have a pole at (i:1), so if this is the case, we go to the next i.
// So method works great, only in special cases may run into problem if K is finite.
function FillInP1Diagram(f, g, A)
    K := Parent(Eltseq(A)[1]);
    FF<x> := FunctionField(K);
    f:= FF!f;
    g:= FF!g;
    P1<x,y>:=ProjectiveSpace(K,1);
    infty:=P1![1,0];
    mapf:=FFEltToActualMorph(f, P1);
    mapg:=FFEltToActualMorph(g, P1);
    matMap:= GL2MatToAut(A, P1);
    i:=K!0;
    threeDistinctValues := false;
    triedIndices := [];
    vals := [];
    while (not threeDistinctValues) do
        if (IsFinite(K)) then
            while (i in triedIndices) do
                i:= Random(K);
            end while;
            triedIndices := Append(triedIndices, i);
        end if;
        
        P:= P1![i,1];
        Q:= mapg(matMap(P));
        P:= mapf(P);
        if P ne infty and Q ne infty and not CheckWhetherPointInFirstTups(vals, P) then
            vals:=Append(vals, <P,Q>);
        end if;        
        if #vals ge 3 then
            threeDistinctValues := true;
        end if;
        i +:= 1;
    end while;
    return DeterminePGL2MatrixFromThreeNonInfinitePoints(vals);
end function;