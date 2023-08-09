// Copied from https://github.com/JRSijsling/hyperelliptic/blob/main/magma/toolbox/isgl2equiv.m-0987652
// Input: Polynomial f over a field K and homogeneous degree n, and a GL_2(K)-matrix mat.
// Output: Action of A on Homog(f), and then dehomogenizing again.
// Note: mat and f need to be defined over the same field.
function TransformPolynomial(f,n,mat)
    a,b,c,d := Explode(Eltseq(mat));
    x1 := a*Parent(f).1 + b; z1 := c*Parent(f).1 + d;
    return &+[Coefficient(f,i)*x1^i*z1^(n-i) : i in [0..n]];
end function;

// Input: Polynomials f and F over a field K and their homogeneous degree, and a GL_2(K) matrix mat.
// Output: Boolean whether f o mat = mu * F for some scalar mu and returns a boolean indicating this and mu. 
// Note: Requires the mat to be defined over K.
function GL2Equivalence(f, F, degf, degF, mat)
	FF := Parent(Eltseq(mat)[1]);

    fp := PolynomialRing(FF)!f;
    Fp := PolynomialRing(FF)!F;
	
	_f := TransformPolynomial(fp, degf, mat);
	_F := TransformPolynomial(Fp, degF, ScalarMatrix(2,1));
	mu := LeadingCoefficient(_f) / LeadingCoefficient(_F);
	return _f eq mu*_F, mu;
end function;

// Returns a boolean indicating whether two homogeneous polynomials are PGL_2-congruent, and if so, also a list of corresponding isomorphisms and corresponding scalar.
// Method: Using GL2Equivalence(), we determine whether the square-free parts of f and F are PGL_2-congruent, and if so check whether this also gives an equivalence for f and F. 
function GeneralIsGL2EquivalentWithSquarefree(f, F, sqfreef, sqfreeF, degf, degF: geometric:= true, commonField:=false)	
	ActualIsoms := [* *];

	// Check whether degrees match
	if degf ne degF then
		return false, ActualIsoms;
	end if;

	// Determine the homogeneous degree of the square free homogeneous polynomial
	if Degree(f) eq degf then
		homogeneousDegSqfreef:= Degree(sqfreef);
	else homogeneousDegSqfreef:= Degree(sqfreef)+1;
	end if;

	if Degree(F) eq degF then
		homogeneousDegSqfreeF:= Degree(sqfreeF);
	else homogeneousDegSqfreeF:= Degree(sqfreeF)+1;
	end if;

	// We first determine whether the square-free parts are PGL_2-congruent. If so, we check whether this isomorphism also induces an isomorphism of the original polynomials.
	if homogeneousDegSqfreef eq homogeneousDegSqfreeF then
		b, isoms := IsGL2EquivalentExtended(sqfreef, sqfreeF, homogeneousDegSqfreef : geometric:=geometric, commonfield := commonField);
		if b then			
			for isom in isoms do
				b, mu := GL2Equivalence(f, F, degf, degF, isom);
				if b then
					ActualIsoms := Append(ActualIsoms, <mu, isom>);
				end if;
			end for;
		end if;
	end if;

	return #ActualIsoms gt 0, ActualIsoms;
end function;

// Returns a boolean indicating whether two homogeneous polynomials are PGL_2-congruent, and if so, also a list of corresponding isomorphisms and corresponding scalar.
// Method: via GeneralIsGL2EquivalentWithSquarefree()/
function GeneralIsGL2Equivalent(f, F, degf, degF: geometric:= true, commonField:=false)
	squarefreef := SquarefreePart(f);	
	squarefreeF := SquarefreePart(F);
	return GeneralIsGL2EquivalentWithSquarefree(f, F, squarefreef, squarefreeF, degf, degF: geometric:= geometric, commonField:=commonField);
end function;

// Input: Two univariate polynomials f, F over the same field with no factors appearing to a multiplicity \geq n, and their degrees as homogeneous polynomials. Can also specify the booleans geometric and commonField,
// geometric determines whether we calculate the geometric automorphisms, and commonField whether the returned PGL_2-transformations are alle defined over the same field.
// Output: A list with <i,lambda, [*<mu, isom>*]>, such that f(isom(x))=mu*lambda^{-n}F^i holds. This corresponds to an isomorphism Y-->X, (x,y)\mapsto (isom(x),sqrt[n](mu)*lambda^{-1}*y^i).
// Method: We determine the squarefree part of f and F and factor F. For each 0<i<n that is coprime to n, we determine (in a smart way using that factors of F) whether the square free part of f and the square free part of F^i are PGL-2 equivalent.
// Then we check whether this matrix also gives an equivalence between f and F^i, and if so add this to the list of isomorphisms. We determine mu and lambda in a smart manner along the way.
// Note: f and F need to be defined over the same field
function ReducedSuperEllipticIsom(f, F, degf, degF, n : geometric := true, commonField := false)
	list:=[* *];
	if Parent(Coefficient(f,0)) ne Parent(Coefficient(F,0)) then
		return "Error: f and F are not defined over the same field";
	end if;
	K:=Parent(Coefficient(f,0));
	squarefreef := SquarefreePart(f);	
	squarefreeF := SquarefreePart(F);
	// Potentially, we can obtain the squarefreePart of F from its factorization. So depending on the functions, we do that calculation twice now. We could optimize this.
	factors:=SquarefreeFactorization(F);
	for i:=1 to n-1 do
		// We can only scale by n-multiples, so we check whether degrees match modulo n for some i coprime to n.
		if Gcd(i,n) eq 1 and degf mod n eq i*degF mod n then
			lambda := Parent(F)!1;
			ReducedF := LeadingCoefficient(F)^i;

			// F^i might have factors appearing to a power more than n, which we scale away with lambda. We call what's left after this scaling ReducedF, for which we calculate the PGL-2 congruence. 
			for j:=1 to # factors do
				factor := factors[j][1];
				e := factors[j][2];
				
				b:= i* e mod n;
				c:= Integers()!((i*e-b)/n); 	
				if c gt 0 then
					lambda *:= factor^c;
				end if;
				ReducedF *:= factor^b;
			end for;

			extraHomogeneousDegree := degF - Degree(F);
			homogeneousDegreeAfterPowering := i*extraHomogeneousDegree mod n;
			powerForLambda := Integers()!(degf/n);			
			degreeReducedF := Degree(ReducedF) + homogeneousDegreeAfterPowering;
			
			// Note that the squarefree part of F equals the squarefree part of ReducedF
			b, isoms := GeneralIsGL2EquivalentWithSquarefree(f, ReducedF, squarefreef, squarefreeF, degf, degreeReducedF: geometric:=geometric, commonField:=commonField);
			if b then
				L:=Parent(isoms[1][2][1][1]);
				if K ne L then
					assert IsSubfield(K,L);		
				end if;
				for tup in isoms do
					mu:=tup[1];
					A:=tup[2];
					a,b,c,d:=Explode(Eltseq(A));
					L1:=Parent(a);
					if K ne L1 then
						assert IsSubfield(K,L1);
					end if;
					P1<x>:=PolynomialRing(L1);
					lambdaA:=P1!lambda;
					if c ne 0 then
						lambdaA*:= (c*x+d)^powerForLambda;
					end if;
					list:=Append(list, <i, lambdaA, <mu,A>>);
				end for;
				if L ne K and commonField then		
					P<x>:=PolynomialRing(L);
					f:=P!f;
					F:=P!F;
					factors:=SquarefreeFactorization(F);
					K:=L;
				end if;
			end if;
		end if;
	end for;
	//return #list gt 0, list;
	// Earlier matrices may not be defined over the latest biggest field, so we fix that here.
	if commonField then
		finalList:=[];
		for tup in list do
			i:=tup[1];
			lambda:=Parent(F)!tup[2];
			mumattups:=tup[3];
			newtups:=[];
			for tup2 in mumattups do
				mu:=L!tup2[1];
				mat:=ChangeRing(tup2[2], K);
				newtups:=Append(newtups, <mu, mat>);
			end for;
			finalList:=Append(finalList, <i, lambda, newtups>);
		end for;
		return # finalList gt 0, finalList;	
	end if;

	return #list gt 0, list;

end function;				

// Calculates the reduced isomorphism group between two curves X: y^n=f and Y:y^n=F via ReducedSuperEllipticIsom() by choosing the homogeneous degree of f (F) to be equal to the degree of f (F) plus a (b), 
// where a (b) is the smallest non-negatitive integer such that the homogeneous degree is divisible by n.		
function NormalizedReducedSuperEllipticIsom(f, F, n : geometric:= true, commonField:= false)
	degf:= Degree(f);
	a:= -degf mod n;
	homogDegf:= degf + Integers()!a;
	degF:= Degree(F);
	b:= -degF mod n;
	homogDegF:= degF + Integers()!b;
	return ReducedSuperEllipticIsom(f, F, homogDegf, homogDegF, n: geometric:= geometric, commonField:=commonField);
end function;

// Input: Given a superelliptic curve X:y^n=f over some field K, calculate the reduced automorphism group of X via ReducedSuperEllipticIsom(). Can also specify the booleans geometric and commonField,
// geometric determines whether we calculate the geometric automorphisms, and commonField whether the returned PGL_2-transformations are alle defined over the same field.
// Output: A list with <i,lambda, [*<mu, isom>*]>, such that f(isom(x))=mu*lambda^{-n}f^i holds. This corresponds to an automorphism of X, (x,y)\mapsto (isom(x),sqrt[n](mu)*lambda^{-1}*y^i).
function ReducedSuperEllipticAutomorphismGroup(f, degf, n : geometric := true, commonField := false)
	return ReducedSuperEllipticIsom(f, f, degf, degf, n: geometric:=geometric, commonField:=commonField);
end function;

// Calculates the reduced automorphism group of the curve X: y^n=f by choosing the homogeneous degree of f to be equal to the degree of f plus a, 
// where a is the smallest non-negatitive integer such that the homogeneous degree is divisible by n.		
function NormalizedReducedSuperEllipticAutomorphismGroup(f, n : geometric:= true, commonField:= false)
	return NormalizedReducedSuperEllipticIsom(f, f, n : geometric:=geometric, commonField:= commonField);
end function;

// Given a polynomial over a field K and an automorphism sigma of K, return sigma(f) by acting on the coefficients.
function AutomorphismActionOnPolynomial(f, sig)
	coefficientsf:= Coefficients(f);
	x:= Parent(f).1;
	g:= Parent(f)!0;
	for i:= 1 to #coefficientsf do
		g +:= sig(coefficientsf[i])*x^(i-1);
	end for;
	return g;
end function;

// Given a rational function f over a field K and an automorphism sigma of K, return sigma(f) (using the action on the numerator and denominator via AutomorphismActionOnPolynomial()).
function AutomorphismActionOnRatFunction(f, sig)
	num:=Numerator(f);
	denom:=Denominator(f);
	K:=Parent(f);
	return K!AutomorphismActionOnPolynomial(num,sig)/K!AutomorphismActionOnPolynomial(denom, sig);
end function;

// Input: Superelliptic curve given by an eq X:y^n=f(x) over some field K and a subfield k of K s.t. K/k is Galois
// Output: Field of moduli of X and the isomorphisms between X and its Galois-conjugates given as a list
// of <i,lambda, [*<mu, isom>*]>, such that f(isom(x))=mu*lambda^{-n}(sigma(f))^i holds. This corresponds to an isomorphism sigma(X)-->X, (x,y)\mapsto (isom(x),sqrt[n](mu)*lambda^{-1}*y^i).
// Method: Calculate Aut(K/k), and determine whether isomorphisms between sigma(X) and X exist using NormalizedReducedSuperEllipticIsom().
// Note: Magma needs to recognize k as a subfield of K
function SuperEllipticFieldOfModuli(f, n, k: geometric:=true, extended:= false)
	K:= Parent(LeadingCoefficient(f));
	grp, s, data := AutomorphismGroup(K,k);
	L:= [**];
	successfullAuts:= [];
	for g in grp do
		map:= data(g);
		fConj:= AutomorphismActionOnPolynomial(f, map);
		b, isoms:=NormalizedReducedSuperEllipticIsom(fConj, f, n: geometric:=geometric, commonField:=true);
		if b then 
			successfullAuts:=Append(successfullAuts, map);
			F:=Parent(isoms[1][3][1][2][1][1]);
			if F ne Parent(LeadingCoefficient(f)) then		
				f:=PolynomialRing(F)!f; //THIS MUST STILL BE BUGGY; if we change the ring, then we should do the whole function again.
			end if;
			if extended then
				L:=Append(L, <map, isoms>);
			else 
				tup:= isoms[1];
				newTup:= <tup[1],tup[2], tup[3][1]>;
				L:=Append(L, <map, newTup>);
			end if;
		end if;
	end for;
	FieldOfModuli:= FixedField(K, successfullAuts);
	return FieldOfModuli, L; 
end function;

// Input: Superelliptic curve given by an eq X:y^n = f(x) over some field K
// Output: The quotient morphism X --> X/Aut(X)
// Method: We calculcate the Automorphism group of X using NormalizedReducedSuperEllipticAutomorphismGroup(), then we use ComputeQuotientMorphismP1() to calculate the quotient morphism.
// Potential problem: not sure whether our algo will always output the quotient morphism over K. 
function QuotientByReducedAutGroup(f,n)
	b, L:=NormalizedReducedSuperEllipticAutomorphismGroup(f,n: commonField:=true);
	mats := [**];
	
	K:=Parent(L[1][3][1][2][1][1]);
	for autTup in L do
		matTuple:= autTup[3];
		for tup in matTuple do
			mats:= Append(mats, tup[2]);
		end for;
	end for;
	quotMorph := ComputeQuotientMorphismP1(mats); 
	// The quotient morphism can sometimes be defined over the ground field. Will our algo always output this as well?
	// In any case, we try to convert it.
	F<x>:=FunctionField(Parent(LeadingCoefficient(f)));
	return F!quotMorph;
end function;

// Input: Superelliptic curve given by an eq X:y^n = f(x) over some field K and a subfield k of K.
// Ouput: The field of moduli of X w.r.t. k and the induced cocycles on X/Aut(X) w.r.t. the field of moduli as maps P1-->sigma(P1), x\mapsto A(X), and the quotient morphism X--> X/Aut(X).
// Method: We determine the field of moduli and isomorphisms between the Galois conjugates of X (using SuperEllipticFieldOfModuli()), then determine the quotient morphism X --> X/Aut(X) (using QuotientByReducedAutGroup()).
// Using FillInP1Diagram(), we obtain the induced cocycles X/Aut(X) --> sigma(X/Aut(X)).
function InducedGaloisIsomorphismsOnXdivAutX(f,n, k)
	FOM, descData:= SuperEllipticFieldOfModuli(f,n,k);
	quotMorph:=QuotientByReducedAutGroup(f,n);
	cocycles:=[];
	K:=Domain(descData[1][1]);
	P1:=ProjectiveSpace(K,1);
	for tup in descData do
		sigma:= tup[1];
        mat:=tup[2][3][2];

		cocycle := FillInP1Diagram(quotMorph, AutomorphismActionOnRatFunction(quotMorph, sigma),  mat);
		//correspondingAut:=GL2MatToAut(cocycle, P1);
		cocycles:=Append(cocycles, <sigma, cocycle>);
	end for;
	//return VerifyCocycleCriterium(cocycles);
	return FOM, cocycles, quotMorph;
end function;

// Input: Superelliptic curve given by an eq X:y^n = f(x) over some field K and a subfield k of K.
// Output: The field of moduli of X w.r.t. k, A model of X/Aut(X) over the field of moduli and corresponding isomorphism, and the quotient morphism X--> X/Aut(X).
// Method: We first determine the the induced cocycles X/Aut(X) --> sigma(X/Aut(X))  w.r.t. the field of moduli of X w.r.t. k, after which we determine the associated matrix on the global sections of the anticanonical sheaf, 
// and determine a coboundary for these matrices (using CurveCboundaryFromCocyclesEmbedding()). We use the anticanonical embedding and this matrix to obtain our model of X/Aut(X) over the field of moduli (using RationalModelAndMapFromCoboundary())
function kModelOfXdivAutX(f,n,k)
	FOM, inducedCocycles, quotMorph:= InducedGaloisIsomorphismsOnXdivAutX(f,n,k);
	L:= Parent(inducedCocycles[1][2][1][1]);
	cocyclesmaps:= [**];
	P1:=Curve(ProjectiveSpace(L, 1));
	for cocycle in inducedCocycles do
		sigma := cocycle[1];
		mat:=cocycle[2];
		// Transform mat to an aut on P1
		morph:= GL2MatToAut(mat, P1);
		cocyclesmaps:=Append(cocyclesmaps, <sigma, morph>);
	end for;
	b, coboundaryMatrix:=CurveCoboundaryFromCocyclesEmbedding(cocyclesmaps: antiCanonical:=true);
	
	model, mapToModel:= RationalModelAndMapFromCoboundary(Transpose(coboundaryMatrix^-1), P1: antiCanonical:=true);
	
	model:=Curve(model);
	mapToModel:=Restriction(mapToModel, Domain(mapToModel), model);
	return FOM, mapToModel, quotMorph;
end function;
