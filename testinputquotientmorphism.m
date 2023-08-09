Q:=FiniteField(17);
//P<x>:=PolynomialRing(RationalField());
//Q<i>:= NumberField(x^2+1);
M1:= Matrix(Q,2,2,[1,0,0,1]);
M2:= Matrix(Q,2,2,[-1,0,0,1]);
/*M3:=Matrix(Q, 2,2, [0,1,1,0]);
M4:=Matrix(Q, 2,2, [0,-1,1,0]);
M5:= Matrix(Q, 2,2, [i,i,1,-1]);
M6:= Matrix(Q, 2,2, [-i,-i,1,-1]);
M7:= Matrix(Q, 2,2, [i,-i,1,1]);
M8:= Matrix(Q, 2,2, [-i,i,1,1]);
M9:= Matrix(Q, 2,2, [1,-i,1,i]);
M10:= Matrix(Q, 2,2, [1,i,1,-i]);
M11:= Matrix(Q, 2,2, [-1,-i,1,-i]);
M12:= Matrix(Q, 2,2, [-1,i,1,i]);
mats:= [M1,M2,M3,M4,M5,M6,M7,M8,M9,M10,M11,M12];

f:=ComputeQuotientMorphismP1(mats);*/

// Test for fill in diagram
f1:=ComputeQuotientMorphismP1([M1,M2]);
FillInP1Diagram(f1, (-f1+3)/f1, M1);

/*
P<x>:=PolynomialRing(Q);
R<y>:=PolynomialRing(P);
P1:=FunctionField(y);
x:= P1!x;
g:= (x^12 + 4879/900*x^10 - 33*x^8 - 4879/450*x^6 - 33*x^4 + 4879/900*x^2 + 1)/(x^10 - 2*x^6 + x^2);*/