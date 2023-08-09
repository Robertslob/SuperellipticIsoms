Q:=RationalField();
/*
// Test for the GLnCoboundary method
P<x>:= PolynomialRing(Q);
f:= x^4+20*x+16;
L:=SplittingField(f);
grp, s, data := AutomorphismGroup(L, Q);
isInvertible:=false;
while not isInvertible do
    B:= RandomMatrix(L, 2, 2, 2);
    if IsInvertible(B) then
	    isInvertible:=true;
    end if;
end while;

tups := [];
for g in grp do
    phi:= data(g);
    tups:= Append(tups, <phi, B*(AutomorphismActionOnMatrix(phi,B))^-1>); 
end for;
C:= DetermineGLnCoboundary(tups);
for g in grp do
    phi:= data(g);
    C*(AutomorphismActionOnMatrix(phi,C))^-1 eq B*(AutomorphismActionOnMatrix(phi,B))^-1; 
end for;
*/
P<x>:=PolynomialRing(Q);
K<i>:=SplittingField(x^3-2);
P<x>:=PolynomialRing(K);
b,a:=HasRoot(x^3-2);
b,zeta:=HasRoot(x^2+x+1);
grp, s, data := AutomorphismGroup(K, Q);

// P1 example

// Supererelliptic example
galGrp:=[];
for g in grp do
    galGrp:=Append(galGrp, data(g));
end for;

/*
P<x>:=FunctionField(K);
R<y>:=PolynomialRing(P);
FF<a>:=FunctionField(y^5-i*x^5-x^4-i*x^3-1);
FFConj<b>:=FunctionField(y^5+i*x^5-x^4+i*x^3-1);
constmap:= hom<P->FF | -x>;
isom:= hom<FFConj -> FF | constmap,a>;
tups:=[<galGrp[1],IdentityHomomorphism(FF)>, <galGrp[2], isom>];
test, B:=CoboundaryFromCocyclesEmbedding(tups);   
//tups:= Appends(tups, <data(1), )*/

// Somehow, this example fails, but works if we change around x and y.
P<x,y,z,h,j,l>:=ProjectiveSpace(K, 5);
f:= (y^5-a*x^5+z^2*x^3-z^5);
X:=Curve(Scheme(P,[f,h,j,l]));

// So we try to do everything with schemes/curves instead. This Works!!
fConj1:= y^5-a*zeta*x^5+z^2*x^3-z^5;
fConj2:= y^5-a*zeta^2*x^5+z^2*x^3-z^5;
XConj1:=Curve(Scheme(P,[fConj1, h,j,l]));
XConj2:=Curve(Scheme(P,[fConj2, h,j,l]));
GaloisConj1Morph:=map<XConj1 -> X | [zeta^2*x,y,z,h,j,l]>; 
GaloisConj2Morph:=map<XConj2 -> X | [zeta*x,y,z,h,j,l]>; 
tups:=[**];
for sig in galGrp do
    if sig(a) eq a then
        tups:=Append(tups, <sig, IdentityAutomorphism(X)>);
    else if sig(a) eq zeta*a then
        tups:=Append(tups, <sig, GaloisConj1Morph>);
    else
        tups:=Append(tups, <sig, GaloisConj2Morph>);
    end if;
    end if;
end for;

//tups:=[<galGrp[1], IdentityAutomorphism(X)>, <galGrp[2],GaloisConj1Morph>];

b, boundary:=CurveCoboundaryFromCocyclesEmbedding(tups);
Z:=CanonicalImage(X,CanonicalMap(X,P));
g:=ProjectiveSpaceMorphismFromLinearTransformation(boundary^-1, P);
model:=g(Z);

function CheckDefinedOverGroundField(C, k)
    P<a,b,c,d,e,f>:=PolynomialRing(k,6);
    pols:=DefiningPolynomials(C);
    for pol in pols do
        P!pol;
    end for;
    return true;
end function;

b;
model;
CheckDefinedOverGroundField(model, Q);

// This one works
/*
P<x>:=FunctionField(K);
R<y>:=PolynomialRing(P);
FF<a>:=FunctionField(y^3-i*x^5+x^2-2);
FFConj<b>:=FunctionField(y^3+i*x^5+x^2-2);
constmap:= hom<P->FF | -x>;
isom:= hom<FFConj -> FF | constmap,a>;
tups:=[<Galgrp[1],IdentityHomomorphism(FF)>, <Galgrp[2], isom>];
test, B:=CoboundaryFromCocyclesEmbedding(tups);   
P<x,y,z,w>:=ProjectiveSpace(K,3);
f:=z^2*y^3-i*x^5+z^3*x^2-2*z^5;
X:=Curve(Scheme(P,[f,w]));

    */