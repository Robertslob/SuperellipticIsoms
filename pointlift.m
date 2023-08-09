function kConicFromGenusZeroCurve(k, C: PP2:=ProjectiveSpace(k,2))
    b,con:=IsConic(C);
    f:=DefiningPolynomial(C);
    P<x,y,z>:= PolynomialRing(k,3);
    return Conic(PP2, P!f);
end function;

// Input: A field FOM, a conic called model that can be defined over FOM, and a map P1 --> model over some field K that contains FOM.
// Output: If the conic has a point over FOM, then we return the map P1 --> model --> P1, where the last map comes from the parametrization corresponding to a point over FOM.
// Method: We find a parametrization of model over FOM, and then see where three points of P1 --> model --> P1 are mapped to, and determine the corresponding matrix.
function MapToConicAsP1(mapToModel, k)
    model:=Codomain(mapToModel);
    kConic:= kConicFromGenusZeroCurve(k, model);
    assert HasRationalPoint(kConic);
    phi:= Parametrization(kConic);
    phiInv:=phi^-1;
    P1<x,y>:=Domain(mapToModel);

    psi:= map<model->P1 | DefiningPolynomials(phiInv)>;

    comp:= mapToModel*psi;
    pointTups:=[];
    K:= BaseField(model);
    i:=K!0;
    
    while #pointTups lt 3 do
        P:=P1![i,1];
        Q:=comp(P);
        if Q[2] ne 0 then
            pointTups:=Append(pointTups, <P,Q>);
        end if;
        i+:=1;
    end while;
    mat:=DeterminePGL2MatrixFromThreeNonInfinitePoints(pointTups);
    a,b,c,d:=Explode(Eltseq(mat));
    map:= map<P1 -> P1 | [a*x+b*y, c*x+d*y]>;
    b, map:= IsIsomorphism(map);
    return map;
end function;

function CheckOutsideBranchLocus(quotMorph, P)
    sch:=Pullback(quotMorph,P);
    return IsNonsingular(sch);
end function;

function RatPointOutsideBranchLocus(quotMorph, mapToP1)
    P1:=Codomain(mapToP1);
    K:=BaseField(P1);
    i:= K!0;
    b:=true;
    while b do
        Q:=P1![i,1];
        inv:=mapToP1^-1;
        P:=inv(Q);
        if CheckOutsideBranchLocus(FFEltToActualMorph(quotMorph, P1), P) then
            return P;
            b:=false;
        end if;
        i+:=1;
    end while;
end function;

// Given a univariate polynomial, return the irreducible factor with smallest degree
function FindSmallestFactor(f)
    fac:=Factorization(f);
    deg:=Degree(f)+1;
    smallestFactor:=0;
    for tup in fac do
        g:=tup[1];
        if Degree(g) lt deg then
            smallestFactor:=g;
            deg:=Degree(g);
        end if;
    end for;
    return smallestFactor;
end function;

// Input: A map between two schemes some field k, and an extension K of k
// Output: The corresponding map over K
function BaseChangeMap (map, K)
    dom:=Domain(map);
    domK:=BaseChange(dom, K);
    codom:=Codomain(map);
    codomK:=BaseChange(codom, K);
    return map<domK -> codomK | DefiningPolynomials(map)>;
end function;

function LiftPointOnP1(quotMorph, P)
    sch:=Pullback(quotMorph, P);
    P1:=Curve(P);
    K:=BaseField(P1);
    f:=DefiningPolynomial(sch);
    uf:= Evaluate(f, 2, 1);
    uf:=UnivariatePolynomial(uf);
    if Degree(uf) le 0 then
        return P1![1,0];
    end if;
    b, root:= HasRoot(uf);
    if b then
        return P1![root,1];
    else
        factor:= FindSmallestFactor(uf);
        L<a>:=NumberField(factor);
        minpolyQ:= MinimalPolynomial(a, Rationals());
        //factor:=uf;
        splitPoly:=DefiningPolynomial(K)*minpolyQ;
        //return splitPoly;
        // Maybe do Pari stuff here
        L:=SplittingField(splitPoly);
        assert IsSubfield(K,L);
        P1L:=BaseChange(P1, L);
        factor:=ChangeRing(factor, L);
        b, a:=HasRoot(factor);
        return P1L![a, 1];
    end if;
end function;   

function ReducedIsomsConjugates(f,n,k)
    FOM, completeRedAuts:=SuperEllipticFieldOfModuli(f,n,k :extended:=true);
    completeSigmaMatList:=[**];
    for tup in completeRedAuts do
        sigma:=tup[1];
        isoms:=tup[2];
        mats:=[];
        for isom in isoms do
            matTups:=isom[3];
            for matTup in matTups do
                mats:=Append(mats, matTup[2]);
            end for;
        end for;
        completeSigmaMatList:=Append(completeSigmaMatList, <sigma, mats>);
    end for;
    return completeSigmaMatList;
end function;

function AutToPoint(aut, P)
    C:=Curve(P);
    return C![aut(P[1]), aut(P[2])];
end function;

function FindCorrespondingMat(auts, P,Q, F)    
    P1:=Curve(P);
    P1F:=Curve(ProjectiveSpace(F, 1));
    PF:=P1F![F!P[1], F!P[2]];
    QF:=P1F![F!Q[1], F!Q[2]];
    numberOfPossibleAuts:=0;
    for mat in auts do
        aut:=GL2MatToAut(mat, P1F);
        if aut(PF) eq QF then
            possibleAut:= aut;
            numberOfPossibleAuts +:= 1;
        end if;
    end for;
    if numberOfPossibleAuts eq 0 then
        return 0, auts;
    else 
        return numberOfPossibleAuts, possibleAut;
    end if;
end function;

function ListOfCorrectMatricesAndConjugates(tupsSigmaMats, Q, F)
    correspondingAuts:=[**];
    for tup in tupsSigmaMats do
        sigma:=tup[1];
        auts:=tup[2];
        val, correctAut := FindCorrespondingMat(auts, Q, AutToPoint(sigma, Q), F);
        if not val eq 1 then
            return val, <sigma, auts>;
            print("error listcorrectmatricesandconj");
        end if;
        correspondingAuts :=Append(correspondingAuts, <sigma, correctAut>);
    end for;
    return true, correspondingAuts;
end function;

function ListOfCorrectMatricesAndConjugatesReversed(tupsSigmaMats, Q)
    correspondingAuts:=[];
    for tup in tupsSigmaMats do
        sigma:=tup[1];
        auts:=tup[2];
        b, correctAut := FindCorrespondingMat(auts, AutToPoint(sigma, Q), Q);
        if not b then
            return false, <sigma, auts>;
        end if;
        correspondingAuts :=Append(correspondingAuts, <sigma, correctAut>);
    end for;
    return true, correspondingAuts;
end function;

function CheckWhetherCoboundaryMapIsCorrect(tupsSigmaMats, coboundaryMap)
    b:= true;
    for tup in tupsSigmaMats do
        sigma:=tup[1];
        mat:=tup[2];
        A:= mat^-1*coboundaryMap^-1*AutomorphismActionOnMatrix(sigma, coboundaryMap);
        if not IsScalar(A) then
            b:= false;
        end if;
    end for;
    return b;       
end function;

function DetermineSmallestFieldOfDefinition(P, K: normal:=true)
    L:=Parent(P[1]);
    if IsSubfield(L, K) then
        F:=K;
    else 
        if P[1] ne 0 then
            F:=sub<L | P[1]>;
        else 
            F:=K;
        end if;
    end if;

    if not IsSubfield(F,K) then
        F:=Compositum(F,K);
    end if;

    if normal and F ne K then
        F:=SplittingField(F);
    end if;    
    
    return Curve(ProjectiveSpace(F,1))![F!P[1], F!P[2]];
end function;

function FindSmallestFactorOverK(f, K)
    fac:=Factorization(f);
    deg:=Infinity();
    for tup in fac do
        g:=tup[1];
        L:=NumberField(g);
        P<x>:=PolynomialRing(L);
        b, a:= HasRoot(P!g);
        minPolyK:=MinimalPolynomial(a, K);
        degPoly:=Degree(minPolyK);

        if degPoly lt deg then
            deg:=degPoly;
            result:=minPolyK;
            minPolyQ:=MinimalPolynomial(a,Rationals());
        end if;
    end for;
    return result, minPolyQ;
end function;

function PotentialLiftOnP1(quotMorph, P, K)
    time sch:=Pullback(quotMorph, P);
    P1:=Curve(P);
    f:=DefiningPolynomial(sch);
    uf:= Evaluate(f, 2, 1);
    uf:=UnivariatePolynomial(uf);
    P1K:=Curve(ProjectiveSpace(K,1));
    if Degree(uf) le 0 then
        return 1, P1K![1,0], "empty";
    end if;

    factor, factorQ:=FindSmallestFactorOverK(uf, K);
    b, a:=HasRoot(factor);
    if b then
        return 1, P1K![a,1], "empty";
    else        
        return Degree(factor), factor, factorQ;
    end if;
end function;

function DetermineRandomLift(mapToP1, quot, k, K: numberFieldBound:= 4, attemptBound:=5)    
    P1:=Codomain(mapToP1);
    quotMorph:=FFEltToActualMorph(quot, P1);
    attempts := 0;
    bestDegree:=Infinity();
    foundRationalLift := false;
    while attempts le attemptBound and not foundRationalLift do
        foundP0:=false;
        while not foundP0 do
            a:=Random(k, numberFieldBound);
            P0:=P1![a,1];
            inv:=mapToP1^-1;
            P:= inv(P0);
            "FoundP0";
            time foundP0:=CheckOutsideBranchLocus(quotMorph, P);
        end while;
        "PotentialLift";
        time deg, Q, rationalFactor:=PotentialLiftOnP1(quotMorph, P, K);
        if deg eq 1 then
            lift:= Q;
            foundRationalLift:=true;
        else            
            if deg lt bestDegree then
                bestDegree:=deg;
                bestFactor:=Q;
                bestRationalFactor:= rationalFactor;
            end if;
        end if;
        attempts+:=1;
    end while;

    if foundRationalLift eq true then
        return Q;
        // Q lives on P1_K
    end if;

    splitPoly:=DefiningPolynomial(K)*bestRationalFactor;
    splitPoly;
    // Might do Pari stuff here
    if Degree(splitPoly) ge 5 then
        L:=SplittingFieldPari(splitPoly : opt:=false);
    else
        L:=SplittingField(splitPoly);
    end if;

    //return bestFactor, L;

    assert IsSubfield(K,L);
    
    //return bestFactor, bestRationalFactor, splitPoly;
    
    P1L:=Curve(ProjectiveSpace(L,1));
    factor:=ChangeRing(bestFactor, L);
    b, a:=HasRoot(factor);
    return P1L![a, 1];
end function;

function vecsToCompatiblePoint(vecs, quotMorph)
    P1:=Domain(quotMorph);
    K:=BaseField(P1);
    for P in vecs do
        x:=VecToK(P, K);
        pt:=P1![x, 1];
        Q:=quotMorph(pt);
        outsideRamLocus:= CheckOutsideBranchLocus(quotMorph, Q);
        if outsideRamLocus then
            return true, pt;
        end if;
    end for;
    return false, "";
end function;

function FindSmartLifts(mapToB0AsP1, quot: searchPole:=false, initialBound:=5, maxBound:=50, stepSize:=10)
    A:=P1MapToMatrix(mapToB0AsP1);
    eqs:=EqToNumberFieldEqs(Geteq(quot,A:searchPole:=searchPole));
    sch:=ProjSchemeFromEqs(eqs);
    d:=Dimension(sch);
    P1:=Domain(mapToB0AsP1);
    quotMorph:=FFEltToActualMorph(quot, P1);

    L:=[];
    if d eq 0 then
        L:=RationalPoints(sch);
        if #L gt 0 then
            b, pt:= vecsToCompatiblePoint(L, quotMorph);
            if b then
                return true, pt;
            end if;
        end if;
    else 
        bound:=initialBound;
        while bound lt maxBound do
            L:=PointSearch(sch, bound);
            printf "Dimension=%o, bound=%o, searchPole=%o\n",d,bound,searchPole;   
            if #L gt 0 then
                b, pt:= vecsToCompatiblePoint(L, quotMorph);
                if b then
                    return true, pt;
                end if;
            end if;
            bound+:=stepSize;
        end while;
    end if;
    if #L eq 0 and searchPole then
        return FindSmartLifts(mapToB0AsP1, quot: initialBound:=initialBound, maxBound:=maxBound, stepSize:=stepSize);
    else    
        return false, "Did not find anything compatible, maybe try with larger bounds.";
    end if;
end function;

function checkRational(P, k)
    return IsCoercible(k, P[1]);
end function;

function CheckRationalityPointAtInfinity (mapToB0AsP1, quot, k)    
    P1:=Domain(mapToB0AsP1);
    quotMorph:=FFEltToActualMorph(quot, P1);
    comp:=quotMorph*mapToB0AsP1;
    infty:=P1![1,0];
    imageInfty:=comp(infty);

    if checkRational(imageInfty, k) and CheckOutsideBranchLocus(quotMorph, quotMorph(infty)) then
        return true, infty;
    end if;
    return false, "";
end function;

function TotalMethod2(f,n,k)
    K:=Parent(LeadingCoefficient(f));
    FOM, mapToModel, quot :=kModelOfXdivAutX(f,n,k);
    if FOM eq K then
        return "Model already over field of moduli";
    end if;
    k:=FOM;
    kModel:=kConicFromGenusZeroCurve(k, Codomain(mapToModel));
    if not HasRationalPoint(kModel) then
        return "B0 has no rational point, terminate.";
    end if;

    mapToB0AsP1:=MapToConicAsP1(mapToModel, k);
    P1:=Domain(mapToB0AsP1);
    b:= false;
    if not Degree(quot) eq 1 then 
        b, Q:=CheckRationalityPointAtInfinity(mapToB0AsP1, quot, k);
        if not b and k eq Rationals() then
            b, Q:=FindSmartLifts(mapToB0AsP1, quot);
        end if;
    end if;    
    if not b then 
        print "Could not find any smart points, so might need to calculate a splitting field. This might be time consuming..";
        Q:=DetermineRandomLift(mapToB0AsP1, quot, k, K);
        P1:=Curve(Q);
        K:=BaseField(P1);
        
        PolRingK<x>:=PolynomialRing(K);
        f:=PolRingK!f; 
    end if;          
    
    tupsSigmaMats:=ReducedIsomsConjugates(f,n,k);
    F:=Parent(tupsSigmaMats[1][2][1][1][1]);    
    assert IsSubfield(K,F);
    
    b, listCorrectAuts:=ListOfCorrectMatricesAndConjugates(tupsSigmaMats, Q, F);
    b, coboundaryMatrix:=CurveCoboundaryFromCocyclesEmbedding(listCorrectAuts:antiCanonical:=true);
    print "no errors";
    model, mapToModel:= RationalModelAndMapFromCoboundary(Transpose(coboundaryMatrix)^-1, P1: antiCanonical:=true);
    model:=Curve(model);
    mapToModel:=Restriction(mapToModel, Domain(mapToModel), model);
    map:= MapToConicAsP1(mapToModel, k);
    
    return model, map;
end function;

function ResultingPol(f,n,k)
    idc, map:=TotalMethod2(f,n,k);
    mat:=P1MapToMatrix(map);
    L:=BaseRing(mat);
    P<x>:=PolynomialRing(L);
    //return f,L,map;
    f:=P!f;
    degf:= Degree(f);
	a:= -degf mod n;
	homogDegf:= degf + Integers()!a;
    res:= TransformPolynomial(f,homogDegf, mat^-1);
    res:=res/LeadingCoefficient(res);
    return res;
end function;

/*


Ideeen: -In TransformPolynomial werken we automatisch met (cx+d)^deg vermenigvuldiging. Dit klopt niet volledig voor de isomorfismes vervolgens. 
-Maar volgens mij zou dit geen invloed moeten hebben voor de cocycle voorwaarde, dus dat is gek.


function TotalMethod(f,n,k)

    FOM, mapToModel, quotMorph :=kModelOfXdivAutX(f,n,k);
    k:=FOM;
    K:=Parent(LeadingCoefficient(f));
    kModel:=kConicFromGenusZeroCurve(k, Codomain(mapToModel));
    if not HasRationalPoint(kModel) then
        return "B0 has no rational point, terminate.";
    end if;

    mapToB0AsP1:=MapToConicAsP1(mapToModel, k);
    P:=RatPointOutsideBranchLocus(quotMorph, mapToB0AsP1);
    P:=DetermineSmallestFieldOfDefinition(P, K:normal:=false);
    Q:= LiftPointOnP1(FFEltToActualMorph(quotMorph, Curve(P)), P);
    Q:=DetermineSmallestFieldOfDefinition(Q, K);
    P1:=Curve(Q);
    L:=Parent(Q[1]);
    if not L eq K then
        PolRingL<x>:=PolynomialRing(L);
        f:=PolRingL!f;        
    end if;
    
    tupsSigmaMats:=ReducedIsomsConjugates(f,n,k);
    K:=Parent(tupsSigmaMats[1][2][1][1][1]);
    
    assert IsSubfield(L,K);
    P1:=Curve(ProjectiveSpace(K, 1));
    Q:=P1![K!Q[1], K!Q[2]];
    b2, listCorrectAuts:=ListOfCorrectMatricesAndConjugates(tupsSigmaMats, Q, K);

    matList:=[**];
    for tup in listCorrectAuts do
        sigma:=tup[1];
        aut:=tup[2];
        mat:=P1MapToMatrix(aut);
        matList:=Append(matList, <sigma, mat>);
    end for;
    b1:= VerifyCocycleCriterium(matList);

    invList:=[**];
    for tup in matList do
        invList:=Append(invList, <tup[1], tup[2]^-1>);
    end for;

    b, coboundaryMatrix:=CurveCoboundaryFromCocyclesEmbedding(listCorrectAuts:antiCanonical:=true);
    model, mapToModel:= RationalModelAndMapFromCoboundary(coboundaryMatrix, P1: antiCanonical:=true);
    return b2, model;
    model:=Curve(model);
    
    map:= MapToConicAsP1(mapToModel, FOM);
    
    coboundaryMapAsMat:= P1MapToMatrix(map);
    
    if CheckWhetherCoboundaryMapIsCorrect(invList, coboundaryMapAsMat) then
        return model, map;
    else
        return P, quotMorph, matList, coboundaryMapAsMat, b;
    end if;
end function;

function TransFormPolRatFnc(f, mat)
    a,b,c,d:=Explode(Eltseq(mat));
    R<x>:=Parent(f);
    K:=BaseRing(R);
    n:=Degree(f);
    coeffs:= Coefficients(f);
    LL<x>:=FunctionField(K);
    x1 := a*x+ b; z1 := c*x + d;
    g:=LL!0;
    for i in [1..(n+1)] do
        g+:= coeffs[i]*(x1/z1)^i;
    end for;
    return g;
end function;

    TODO next: We start with K/k Galois, now find a point P on P1 for which we're going to search for the morphism A_{sig} s.t. A_sig(sig(P))=P, with A_sig in red. aut. grp. 
    Only problem is that P need not be defined over K. So P defined over L, with L/k Galois and containing K. We calculate Aut(K/k), take some tau in here and search for A_sig(tau(P))=P, where tau\vert_K = sig.
*/