clear;
AttachSpec("CHIMP/CHIMP.spec");
load "quotientmorphismP1.m";
load "GLnCoboundary.m";
load "superelliptic.m";
load "solveqs.m";
load "pointlift.m";

Q:=RationalField();
P<x>:=PolynomialRing(Q);
f:= x^4+1;
g:= x^4+1;
//ReducedSuperEllipticIsom(f,g^2,4,8,3);	

f:=x^3+5;
L:=SplittingField(f);
R<y>:=PolynomialRing(L);
a:=Roots(f,L)[1][1];
g:=y^6+y^3+a*y+3;                             
//SuperEllipticFieldOfModuli(g, 3, Rationals());
//Shoudl return Q

// THIS ONE GOES WRONG:
g:=x^4-2;
K<i>:=SplittingField(g);
R<x>:=PolynomialRing(K);
b,a:=HasRoot(R!g);

P<x>:=PolynomialRing(K);
//f:=x^6+i*x^5+x^4+1;
f:=x^20+a*x+3+2*a*x^5;
P2<u,v,w>:=ProjectiveSpace(K,2);
C:=Curve(ProjectiveSpace(K,1));
K1:=CanonicalDivisor(C);
canonEmbed:= DivisorMap(-K1, P2);
A:=Matrix(K,2,2,[i,1,3,1]);
//quot:=QuotientByReducedAutGroup(f,3);
//eqs:=EqToNumberFieldEqs(Geteq(quot,A));
//sch:=ProjSchemeFromEqs(eqs);
//FOM, mapToModel, quotMorph:=kModelOfXdivAutX(f,4,Q);
//pt, F:=TotalMethod2(f,4,Q);
//ResultingPol(f,4,Q);

//model:=kConicFromGenusZeroCurve(FOM, model);
//HasRationalPoint(model);
//resultingPol(f,3,Q);