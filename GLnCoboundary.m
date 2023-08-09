//Given a matrix mat over a field K and an automorphism aut of this field K, returns aut(mat) by acting on the entries of the matrix. 
function AutomorphismActionOnMatrix(aut, mat)
    for i:= 1 to NumberOfRows(mat) do
        for j:= 1 to NumberOfColumns(mat) do
            val := mat[i,j];
            mat[i,j]:= aut(val);
        end for;
    end for;
    return mat;
end function;  

// Input: List of the form [a1, a2] or [a1].
// Output: a2 in the first case, and 0 in the latter case.
function FirstCoefficientFromMultivariate(multcoeffs)
    if #multcoeffs ge 2 then
        a:=multcoeffs[2];
    else
        a:=0;
    end if;
    return a;
end function;

function P1MapToMatrix(map)
    K:=BaseField(Domain(map));
    pols:=DefiningPolynomials(map);
    a:= FirstCoefficientFromMultivariate(Coefficients(pols[1],1));
    b:= FirstCoefficientFromMultivariate(Coefficients(pols[1],2));
    c:= FirstCoefficientFromMultivariate(Coefficients(pols[2],1));
    d:= FirstCoefficientFromMultivariate(Coefficients(pols[2],2));
    return Matrix(K, 2,2,[a,b,c,d]);
end function;


// Given a list of tuples of automorphisms aut and corresponding cocycles (matrices) mat, and a vector vec, returns the vector corresponding to sum (mat*aut(vec)).
function EvaluateCoboundaryFunction(automorphismsAndCocycles, vec)
    K:= Parent(Eltseq(automorphismsAndCocycles[1][2])[1]);
    b:= ChangeRing(Parent(vec)!0, K);
    for tup in automorphismsAndCocycles do
        aut := tup[1];
        cocycle := tup[2];
        val:= cocycle*ChangeRing(AutomorphismActionOnMatrix(aut, vec), K);
        b+:= val;
    end for;
    return b;
end function;

// Generates a random matrix
// Works only for finite fields or number fields
function RandomMatrix(K, bound, m, n)
    mat := ZeroMatrix(K, m,n);
    for i:= 1 to NumberOfRows(mat) do
        for j:= 1 to NumberOfColumns(mat) do
            if IsFinite(K) then
                mat[i,j] := Random(K);
            else
                mat[i,j]:= Random(K,bound);
            end if;
        end for;
    end for;
    return mat;
end function;

// Input: A list of tuples of automorphisms of some field L/K and corresponding matrices in GL_n(L) that satisfy the cocycle relation.
// Output: The coboundary B of this 1-cocycle, i.e. A_sigma = B * sigma(B)^(-1).
// Method: We know that every 1-cocycle in H^1(L/K,GL_n(L)) is a coboundary. There exists a constructive proof of this fact (Neukirch et al. Cohomology of Number fields, Theorem 6.2.3) with one computational problem, 
// for which we use a stochastic approach to solve this.
function DetermineGLnCoboundary(automorphismsAndCocycles)
    L:= Domain(automorphismsAndCocycles[1][1]);
    n := NumberOfColumns(automorphismsAndCocycles[1][2]);
    isInvertible:=false;
    bound:= 2;
    iterationsSameBound := 0;
    while not isInvertible do    
        if iterationsSameBound ge 5 then
            bound *:= 2;
            iterationsSameBound := 0;
        end if; 
        mat := ZeroMatrix(L, n,n);
        vecs := [];
        for i:=1 to n do
            vec := RandomMatrix(L, bound, n, 1);
            vec := EvaluateCoboundaryFunction(automorphismsAndCocycles, vec);
            for j := 1 to n do
                mat[j, i]:= vec[j][1];
            end for;
        end for;
        if IsInvertible(mat) then
	        isInvertible:=true;
        end if;
        iterationsSameBound +:= 1;
    end while;
    return mat;
end function;

// Given a map phi:X--> Y of curves, gives the matrix corresponding to the base change by the induced map on global differentials
function MatrixCanonCurve(phi)
    X:= Domain(phi);
    Y:= Codomain(phi);
    basisHoloDiffY:=BasisOfHolomorphicDifferentials(Y);
    RR2, h2:=SpaceOfHolomorphicDifferentials(X);
    g2:=h2^-1;
    matrixEntries:=[];
    for elt in basisHoloDiffY do
        val:=g2(Pullback(phi, elt));
        vec:= Eltseq(val);
        for entry in vec do
            matrixEntries:= Append(matrixEntries, entry);
        end for;
    end for;

    n:= #basisHoloDiffY;
    K:=BaseField(X);
    return Matrix(K, n, n, matrixEntries);
end function;

// Given a map phi:X--> Y of curves, gives the matrix corresponding to the base change by the induced map on the global dual differentials (for genus zero curves)
function MatrixAntiCanonCurve(phi)
    X:= Domain(phi);
    Y:= Codomain(phi);
    K1:=CanonicalDivisor(X);
    K2:=CanonicalDivisor(Y);
    AntiBasisK2:=Basis(-K2);
    RR2, h2:=RiemannRochSpace(-K1);
    g2:=h2^-1;
    matrixEntries:=[];
	mat:=P1MapToMatrix(phi);
    a,b,c,d:=Explode(Eltseq(mat));
    for elt in AntiBasisK2 do
        pullback:=Pullback(phi, elt);
        FF1:=Parent(pullback);
        FF2:=Parent(elt);
        denom:= c*FF1.1+d;
        val:=g2(pullback*denom^2/Determinant(mat));
        vec:= Eltseq(val);
        for entry in vec do
            matrixEntries:= Append(matrixEntries, entry);
        end for;
    end for;

    n:= #AntiBasisK2;
    K:=BaseField(X);
    return Matrix(K, n, n, matrixEntries);
end function;

function CheckWhetherCoboundaryMapIsCorrectTest(tupsSigmaMats, coboundaryMap)
    b:= true;
    for tup in tupsSigmaMats do
        sigma:=tup[1];
        mat:=tup[2];
        A:= mat^-1*coboundaryMap*AutomorphismActionOnMatrix(sigma, coboundaryMap)^-1;
        if not IsScalar(A) then
            b:= false;
        end if;
    end for;
    return b;       
end function;

// Input: List of tuples <sigma,phi_sigma>: where phi_sigma is an isomorphisms between sigma(X) and X and the phi_sigma satisfy the cocycle relation, and a boolean indicating whether we should look at the dual of the global differentials.
// Output: Coboundary corresponding to induced base changes of induced maps on (dual of) global differentials.
// Given isomorphisms between a curve and its Galois conjugates that satisfy the cocycle relation, we obtain induced maps on (the dual of) the global differentials. These give matrices via the methods MatrixCanonCurve() and MatrixAntiCanonCurve()
// that satisfy the cocycle condition, hence we obtain a coboundary via DetermineGLnCoboundary(), which we return.
function CurveCoboundaryFromCocyclesEmbedding(cocycles: antiCanonical:= false)
    matrixCocycles:=[];
    for cocycle in cocycles do
        sigma:=cocycle[1];
        isom:=cocycle[2];
        if antiCanonical then
            mat:=MatrixAntiCanonCurve(isom);
        else 
            mat:= MatrixCanonCurve(isom);
        end if;

        matrixCocycles:=Append(matrixCocycles, <sigma, mat>);
    end for;
    cob:= DetermineGLnCoboundary(matrixCocycles);
    b:=CheckWhetherCoboundaryMapIsCorrectTest(matrixCocycles, cob);
    return b, cob;
end function;

// Input: Matrix mat acting on projective space P
// Output: Corresponding morphism of P induced by mat.
function ProjectiveSpaceMorphismFromLinearTransformation(mat, P)
    n := NumberOfColumns(mat);
    list := [];
    for i := 1 to n do
        f := 0;
        for j := 1 to n do
            f +:= mat[i, j]*P.j;
        end for;
        list := Append(list, f);
    end for;
    return map< P-> P | list>;
end function;

// Input: Curve C over a field K of genus g, Projective space P^(g-1)_K, g x g matrix mat over K, and a boolean indicating whether we should use the anticanonical divisor
// Output: comp(C), comp, where comp denotes the composition of the canonical map of C and the induced action of mat on P^(g-1).
function AmbientRationalModelAndMapFromCoboundary(mat, C, P : antiCanonical:=false)
    K := BaseRing(C);
    n := NumberOfColumns(mat);
    if antiCanonical then
        can:= CanonicalDivisor(C);
        f:= DivisorMap(-can, P);
    else 
        f := CanonicalMap(C, P);
    end if;
    g := ProjectiveSpaceMorphismFromLinearTransformation(mat^-1, P);
    comp := f * g;
    return comp(C), comp;
end function;

// Input: Curve C over a field K of genus g, g x g matrix mat over K, and a boolean indicating whether we should use the anticanonical divisor
// Output: comp(C), comp, where comp denotes the composition of the canonical map of C and the induced action of mat on projective space of dimension g-1 over K.
// Note: Same as AmbientRationalModelAndMapFromCoboundary(), but without specified ambient space.
function RationalModelAndMapFromCoboundary(mat, C : antiCanonical:=false)
    K := BaseRing(C);
    n := NumberOfColumns(mat);
    P := ProjectiveSpace(K, n-1);
    return AmbientRationalModelAndMapFromCoboundary(mat, C, P : antiCanonical:=antiCanonical);
end function;

// Input: Curve C over a field K of genus g, Projective space P^(g-1)_K, g x g matrix mat over K, and a boolean indicating whether we should use the anticanonical divisor
// Output: comp(C), where comp denotes the composition of the canonical map of C and the induced action of mat on P^(g-1).
// Note: Faster than AmbientRationalModelAndMapFromCoboundary().
function AmbientRationalModelFromCoboundary(mat, C , P: antiCanonical:= false)
    K := BaseRing(C);
    n := NumberOfColumns(mat);
    if antiCanonical then
        can:= CanonicalDivisor(C);
        f:= DivisorMap(-can, P);
    else 
        f := CanonicalMap(C, P);
    end if;
    D, b := CanonicalImage(C, f);
    g := ProjectiveSpaceMorphismFromLinearTransformation(mat^-1, P);
    return g(D);
end function;

// Input: Curve C over a field K of genus g, g x g matrix mat over K, and a boolean indicating whether we should use the anticanonical divisor
// Output: comp(C), where comp denotes the composition of the canonical map of C and the induced action of projective space of dimension g-1 over K.
// Note: Same as AmbientRationalModelAndMapFromCoboundary(), but without specified ambient space. Faster than RationalModelAndMapFromCoboundary().
function RationalModelFromCoboundary(mat, C : antiCanonical:=false)
    K := BaseRing(C);
    n := NumberOfColumns(mat);
    P := ProjectiveSpace(K, n-1);
    return AmbientRationalModelFromCoboundary(mat, C, P : antiCanonical:=antiCanonical);
end function;

function VerifyCocycleCriterium(tups)
    res:= true;
    messages:= [];
    fieldOfDef:=Parent(tups[1][2][1][1]);
    for tup in tups do
        sigma:=tup[1];
        mat:=tup[2];
        if Parent(tups[1][2][1][1]) ne fieldOfDef then
            messages:=Append(messages, <sigma, "clash with FOD">);
            res:=false;
        end if;
        for tup2 in tups do
            tau:=tup2[1];
            mat2:=tup2[2];
            comp:= tau*sigma;
            matCandidates:=[];
            for tup3 in tups do
                aut:=tup3[1];
                mat3:=tup3[2];
                if aut eq comp then
                    matCandidates:=Append(matCandidates, mat3);
                end if;
            end for;
            for mat3 in matCandidates do
                A:= mat3^-1* AutomorphismActionOnMatrix(sigma, mat2)*mat;
                if not IsScalar(A) then
                    res:=false;
                    messages:=Append(messages, <sigma,tau,"corresponding matrix wrong">);
                end if;
            end for;
            if #matCandidates eq 0 then
                messages:=Append(messages, <sigma,tau,"no candidates">);
            else if #matCandidates ge 2 then
                messages:=Append(messages, <sigma,tau,"more than one candidate">);
            end if;
            end if;
        end for;
    end for;
    return res, messages;
end function;

/*

Code for doing everything on function fields, doesnt work always because incompatible with canonicalmap function

// Input: A list of tuples with automorphisms sigma of a field L over a field K and isomorphisms from sigma(FF) to FF that satisfy cocycle relation, and a boolean indicating whether we should use the anticanonical embedding. 
// Output: A matrix B such that B^-1 sigma(B) = A_sigma for all sigma in Gal(L/K), where 
function CoboundaryFromCocyclesEmbedding(cocycles : antiCanonical:=false, schemeFF := false)
    matrixCocycles:=[];
    for cocycle in cocycles do
        sigma:=cocycle[1];
        isom:=cocycle[2];
        dom:= Domain(isom);
        codom:=Codomain(isom);
        if antiCanonical eq true then    
            det:=cocycle[3];
            mat:= MatrixOnAntiCanonDivisorFromFFIsomorphism(dom, codom, isom,det);
        else 
            mat:= MatrixOnCanonDivisorFromFFIsomorphism(dom, codom, isom : schemeFF := schemeFF);
        end if;
        matrixCocycles:=Append(matrixCocycles, <sigma, mat>);
    end for;
    return matrixCocycles, DetermineGLnCoboundary(matrixCocycles)^-1;
end function;

// Input: function field of P1 and a PGL_2-matrix over the constant field.
// Output: Isomorphism of the function field corresponding to this matrix.
function FFIsomFromPGL2Matrix (FP1, mat)
    x:= FP1.1;
    a,b,c,d := Explode(Eltseq(mat));
    return hom<FP1 -> FP1 | (a*x+b)/(c*x+d)>;
end function;

// Input: Function fields FF1 and FF2 and an isomorphism phi: FF1 -> FF2.
// Output: Matrix A such that vec(phi(e_i))=A*vec(e_i'), where e_i (resp. e_i') are basis elements of the Riemann-Roch space of the anticanonical divisor of FF1 (resp. FF2).
// PROBLEM: Idea is that we call this method with sigma(FF) and FF, and then need our basisses to be sigma(e_i) and e_i. So currently works if FF is over k, 
// but would only work in this case if magma somehow enforces that sigma(e_i) is the new basis, which I don't think it does. Should be able to reprogram this so that it does.
// Other PROBLEM: Currently hardcoded so that it thinks in projective coordinates. This is fine for P1, but how does this work for general curves?
function MatrixOnAntiCanonDivisorFromFFIsomorphism(FF1, FF2, phi,det)
    k:=ConstantField(FF1);
    K1:=CanonicalDivisor(FF1);
    K2:=CanonicalDivisor(FF2);
    BasisK1:=Basis(-K1);
    RR2, h2:=RiemannRochSpace(-K2);
    g2:=h2^-1;
    n:= #BasisK1;
    matrixEntries:=[];
    for elt in BasisK1 do
        val:=g2(phi(elt)*Denominator(phi(FF2.1))^2/det);
        vec:= Eltseq(val);
        for entry in vec do
            matrixEntries:= Append(matrixEntries, entry);
        end for;
    end for;
    return Transpose(Matrix(k, n, n, matrixEntries));
end function;


// Input: Function fields FF1 and FF2 and an isomorphism phi: FF1 -> FF2.
// Output: Matrix A such that vec(phi(e_i))=A*vec(e_i'), where e_i (resp. e_i') are basis elements of the Riemann-Roch space of the canonical divisor of FF1 (resp. FF2).
// PROBLEM: Idea is that we call this method with sigma(FF) and FF, and then need our basisses to be sigma(e_i) and e_i. So currently works if FF is over k, 
// but would only work in this case if magma somehow enforces that sigma(e_i) is the new basis, which I don't think it does. Should probably (?) be able to reprogram this so that it does.
function MatrixOnCanonDivisorFromFFIsomorphism(FF1, FF2, phi : schemeFF:= false)
    if schemeFF then
        k:=BaseField(Scheme(FF1));
    else
        k:=ConstantField(FF1);
    end if;
    K1:=CanonicalDivisor(FF1);
    K2:=CanonicalDivisor(FF2);
    BasisK1:=Basis(K1);
    RR2, h2:=RiemannRochSpace(K2);
    g2:=h2^-1;
    n:= #BasisK1;
    matrixEntries:=[];
    x:= BaseField(FF1).1;
    for elt in BasisK1 do
        val:=g2(phi(elt));
        vec:= Eltseq(val);
        for entry in vec do
            matrixEntries:= Append(matrixEntries, entry);
        end for;
    end for;
    return Transpose(Matrix(k, n, n, matrixEntries));
end function;

*/