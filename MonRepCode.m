///////////////////////////////////////////////////////////////////
// 
// 	Functions for computing with the centraliser algebra of a monomial representation. 
// 
///////////////////////////////////////////////////////////////////


/////////////////////////////////
//
//	GetRankGroups returns the groups of rank r
//	given degree n. 
//
/////////////////////////////////

GetRankGroups := function(n,r);

	t := NumberOfPrimitiveGroups(n);
	Gs := [];
	for i in [1..t-2] do;
		G := PrimitiveGroup(n,i);

		H := Stabiliser(G,1);
		phi := CosetAction(G, H);
		OO := Orbits( phi(H) );
		rank := #OO;
		if rank eq r then;
			Append(~Gs, G);
			end if;
		end for;

	return Gs;

end function;



///////////////////////////////////////////////////////////////////
//
// Given finite group G and a subgroup H, the first function computes the 
// Schur cover of G. The second takes G, H and returns the following:
// S1 -- Schur cover of G
// S2 -- Preimage of H in Schur cover of G
// S3 -- Linear characters of S2
//
///////////////////////////////////////////////////////////////////


SchurCover := function(G);

	n := #G;
	ps := PrimeDivisors(n);
	Gamma := G;
	for p in ps do;
		PG := pMultiplicator(Gamma,p);
		if PG[1] gt 1 then;
			F,null := FPGroup(Gamma);
			FGamma := pCover(Gamma,F,p);
			Gamma := PermutationGroup(FGamma);
			end if;
		end for;
	
	return Gamma;

end function;

SchurData := function(G, H);

S := SchurCover(G);

n := NumberOfGenerators(G);
m := NumberOfGenerators(S);
list := [S.i -> G.i : i in [1..n]];
list2 := [S.i -> Id(G) : i in [n+1..m]];
phi := list cat list2;
phi := hom<S -> G | phi>;
phi2 := Inverse(phi);
H := Stabilizer(G,1);

S2 := phi2(H);
S3 := LinearCharacters(S2);

return [* S, S2, S3 *];
end function;




/////////////////////////////////////////////////////////
//
// 	Given a group G and a subgroup H, HigmanTransversal constructs a special 
//	transversal of H in which the elements corresponding to an orbital of H on the 
// 	cosets of G are all labelled by elements of the form t*h_i where H*t is a 
//	basepoint for the orbital. The second output, OrbitsReps, is the transversal
//	element corresponding to a fixed basepoint of each orbital. The third output,
//	ConjElts, is a list (corresponding to orbitals o) of lists (corresponding to each 
//	element x in the orbital), such that ConjElts[o][x] is the element h mapping the
//	basepoint of o to x.
//
/////////////////////////////////////////////////////////

HigmanTransversal := function(G, H);

	T, tau := Transversal(G, H);
	T := Setseq(T);

	phi := CosetAction(G, H);
	OO := Orbits( phi(H) );
	rank := #OO;

// For each orbital, we fix a basepoint, and find the
// corresponding transversal element, add that to OrbitsReps. 
// TransOrbs sorts transversal elements into orbitals.

	OrbitsReps := [];
	TransOrbs := [];
	for orb in OO do;
		temp := [];
		for j in T do;

			if 1^phi(j) in orb then;
				Append(~temp, j);

				if 1^phi(j) eq orb[1] then;
					Append(~OrbitsReps, j);

					end if;
				end if;	

			end for;
		Append(~TransOrbs, temp);
	end for;

// For each point x in each orbital we 
// find an element of H mapping the basepoint to x

	ConjElts := [ [One(G) ] ];
	for i in [2..rank] do;
		list := [];
		alpha := OrbitsReps[i];
		for xx in TransOrbs[i] do;
			valid :=( { alpha^-1 * h * xx : h in H } meet Set(H));
			if One(G) in valid then; 
				rep := One(G);
			else;
				rep := Random(valid);
				end if;

			Append(~list, rep);
			end for;
		Append(~ConjElts, list);
		end for;

// We assemble the transversal

	HigTrans := [];
	for i in [1..rank] do;
		for j in [1.. #OO[i]] do;
			Append(~HigTrans, OrbitsReps[i]*ConjElts[i,j]);
			end for;	
		end for;

	return [* HigTrans, OrbitsReps, ConjElts *];
end function;

///////////////////////////////////////////////
//
//	Given G, a subgroup H, and a Transversal T,
//	Split writes any element g of G as a product h*t. 
// 	Not optimised.
//
///////////////////////////////////////////////

Split := function(G, H, T, g);
	for ti in T do;
	if g*ti^-1 in H then;
	return [g*ti^-1, ti];
	end if;
	end for;
end function;


///////////////////////////////////////////////
//
// 	Given a Higman transversal and character of H, 
// 	we construct the monomial representation. The
//	first output is a list of generators, the second output is the algebra.
//
///////////////////////////////////////////////

MonomialAction := function(G, H, Higtrans, chi);

n := #Higtrans;
K := CharacterField(chi);
Alg := MatrixAlgebra(K, n);

// We construct a monomial matrix for each generator.

gens := [];

for gg in Generators(G) do;
temp := [];
	for t1 in Higtrans do;
	for t2 in Higtrans do;
	xx := t1 * gg * t2^-1;
		if Split(G, H, Higtrans, xx)[2] eq One(G) then;
		Append(~temp, K!chi( xx ));
		else;
		Append(~temp, K!0);
		end if;
	end for;
	end for;
Append(~gens, Alg!temp);

end for;

return gens, Alg;
end function;


///////////////////////////////////////////////////////////
//
// 	We construct the centraliser of a monomial representation 
// 	given Higman transversal data and a character of H. The outputs
//	of the previous functions are required, all of the same name, except here
//	the input Reps is the output OrbitsReps from HigmanTransversal.
//
///////////////////////////////////////////////////////////


ConstructCentraliser := function(G, H, HigTrans, Reps, ConjElts, chi, Alg);

rank := #Reps;
Cent := [];
K := CharacterField(chi);

for j in [1..rank] do;
tj := Reps[j];
orbital := [ tj*hj : hj in ConjElts[j]];

List := [];
// Rows and columns of the matrix are labelled by transversal elements.

	for tx in HigTrans do;
	for ty in HigTrans do;

//	An element is non-zero if and only if the transversal 
//	component belongs to the orbital.

	label := Split(G, H, HigTrans, ty*tx^-1)[2];
	if label in orbital then;
	index := Position(orbital, label);

//	hh is the element of H which maps the basepoint
//	of the orbital to the element ty*tx^-1. Hence sigma 
//	maps the pair (1, bp) to (x, y).

	hh := ConjElts[j,index];
	sigma := hh*tx;
	hy := Split(G, H, HigTrans, tj*sigma)[1];

	Append( ~List, K!( chi(hh^-1)*chi(hy) )  );
// chi (   Hpart( tx*sigma^-1, phi)
// chi (   Hpart( ty*sigma^-1*tj^-1, phi))^-1 );

	else;
	Append(~List, K!0);
	end if;
	end for;
	end for;

Append(~Cent, Alg!List);
end for;

return Cent;
end function;

/////////////////////////////////////////////////////////
//
//	The main function Quickcent runs through the above functions
//	for a given G, H and chi. 
// 	The algorithm constructs the centraliser algebra of the monomial representation 
// 	induced from the character of H. 
// 	Outputs are: 
// 		1) A basis for the centraliser algebra. 
// 		2) Generators for the monomial representation. 
// 		3) Matrices corresponding to non-orientable orbitals (which are almost never of 
// 		interest in applications, but I wanted to look at them).
//
/////////////////////////////////////////////////////////


QuickCent := function(G, H, chi);

HigTrans, OReps, CElts := HigmanTransversal(G, H);
gens, alg := MonomialAction(G, H, HigTrans, chi);
cent := ConstructCentraliser(G, H, HigTrans, OReps, CElts, chi, alg);

invalid := [];
for i in cent do;
for g in gens do;
if g*i*g^-1 ne i then;
Append(~invalid, i);
end if;
end for;
end for;

return cent, gens, invalid;
end function;

/////////////////////////////////////////////////////
//
// Demo: Construction of a Hadamard matrix of order 144 having M_11 as an 
// automorphism group.
//
/////////////////////////////////////////////////////

// G := PrimitiveGroup(11, 6);
// S := SylowSubgroup(G, 11);
// H := Normaliser(G, S);
// Char := CharacterTable(H);
// Chi := Char[1];
// Al := QuickCent(G, H, Chi);

// Unfortunately, MAGMA makes some arbitrary choice among orbitals of the same size. 
// There are three orbitals of length 11 and two of length 55. SOME choice of one of each 
// gives a Hadamard matrix - play with the negative signs here to find it!
// H := Al[1] + Al[2] - Al[3] + Al[4] + Al[5] - Al[6]; worked for me.
// Determinant(H) - 144^72;



////////////////////////////////////////////
//
//	Computing the different parts involved in Proposition 4.1.
//
/////////////////////////////////////////////

CharMat := function(G);

	n := #ConjugacyClasses(G);
	CharG := CharacterTable(G);
	return Matrix(n,n,[[CharG[i][j] : j in [1..n]] : i in [1..n]]);

end function;

MonRepCharTab := function(S,H,chi,L4);

	K := CharacterField(chi);
        T := L4[1];
        DC := L4[2];
        CosetReps := L4[3];

	CC := ConjugacyClasses(S);
	n := #CC;

	Cosets := [ ];

//	ind is the k_{1},...,k_{r}.

	ind := [];
	for i in DC do;
		Append(~Cosets, { h*i : h in H} );
		Append(~ind, #H/(#( { h : h in H} meet { i^-1*h*i : h in H})));
		end for;
        
	Rows := [];

// For each double coset & each element in a representative right coset

	for g in DC do;
		list := [K!0 : i in [1..n]];
		scalar := ind[Position(DC, g)];
		for h in H do;
		K := Parent(chi(h^(-1)));
// Sort into G-conjugacy classes. This is building the matrix L.
		P2 := Rationals();
			for i in [1..n] do;
				if IsConjugate(S, h*g, CC[i][3]) then;
					list[i] +:= scalar*chi(h^(-1));
					end if;
				end for;

			end for;
		P2 := Compositum(P2,Parent(list[1]));
		Append(~Rows, list);
		end for;

	M := CharMat(S);
	P1 := Parent(M[1][1]);

	P := Compositum(P1,P2);

	L := Matrix(P,Rows);

	K := KMatrixSpace(P,n,n);
	M := K!M;

	A := (1/#H)*M*Transpose(L);
	A := RemoveZeroRows(A);

	return Transpose(A);
	
end function;

/////////////////////////////////////////////////////
//
//	FixCharMat takes the output which can be in a field 
//	that's an extension of massive dimension and rewrites
//	it over the minimal field.
//
///////////////////////////////////////////////////////

FixCharMat := function(M,r);

	entries := [[M[i][j] : j in [1..r]] : i in [1..r]];
	entries := &cat entries;
	K := Rationals();
	for i in [1..r^2] do;
		K := Compositum(K,MinimalField(entries[i]));
		end for;
	pols := [MinimalPolynomial(entries[i]) : i in [1..#entries]];
	degs := [Degree(p ) : p in pols];
	if Max(degs) gt 1 then; 
		loc := Position(degs,Max(degs));
		p := MinimalPolynomial(entries[loc]);
		L<x> := ext<Rationals() | p>;
		null, phi := IsSubfield(L,K);
		psi := Inverse(phi);

		list := [psi(entries[i]) : i in [1..#entries]];

		MA := MatrixAlgebra(L,r);
		return MA!list;
	else;
		return M;
		end if;

end function;
	
	

///////////////////////////////////////////////////////////////////
//
// Returns a list of data required for working with the centraliser algebra 
// induced from chi, a character of H. Outputs in order: 
// L1 -- G 
// L2 -- H 
// L3 -- chi
// L4 -- Higman transversal of H in G (just a transversal in a format to reduce computations later). 
// L5 -- Monomial representations of the generators of G. 
// L6 -- Basis elements for the centraliser algebra
// L7 -- Character table of the centraliser algebra (note - may have a mismatch in ordering between L6, L7).
//
//////////////////////////////////////////////////////////////////

GroupData := function(G, H, chi);

L1 := G;
L2 := H;
L3 := chi;
L4 := HigmanTransversal(G, H);
L5, Alg := MonomialAction(G, H, L4[1], chi);
L6 := ConstructCentraliser(G, H, L4[1], L4[2], L4[3], chi, Alg);
M := MonRepCharTab(G, H, chi, L4);
L7 := FixCharMat(M, NumberOfRows(M));

return [* L1, L2, L3, L4, L5, L6, L7 *];
end function;



///////////////////////////
//
//	Tests whether the roots of the final 
//  polynomial have norm 1 (in the complex numbers).
//
///////////////////////////

ValidLastPoly := function(list);

	n := #list;
	
	B := BaseRing(Parent(list[1]));	
	K<z> := PolynomialRing(B);	
	P := Parent(list[n]);

	evals := [ K!0 : i in [1..n-1] ];
	Append(~evals, z);

	phi := hom<P->K | evals>;
	
	q6 := phi(list[n]);
	k6 := SplittingField(q6);
	r6 := Roots(q6, k6);

	c6 := Conjugates(r6[1,1]);
	
	ind := 0;
	for i in c6 do;
		m := Modulus(i);
		if AbsoluteValue(m -1) lt 10^-10 then;
		ind := 1;
		end if;
	end for;

	if ind eq 1 then;
	return true;
	else;
	return false;
	end if;

end function;


////////////////////////////////////////////////////
//
//	GetGroebner takes a character table, the degree 
//  of the centraliser algebra and a field B as arguments
//
////////////////////////////////////////////////////

GetGroebner := function(CT,n,B);

// Rewriting Character Table over a bigger field.

	F := Parent(CT[1][1]);
	F := Compositum(F,B);
	t := NumberOfRows(CT);
	Al := MatrixAlgebra(F,t);
	list := [[F!CT[i][j] : j in [1..t]] : i in [1..t]];
	CT := Al!list;	

// Build quadratic polynomials from Character Table

	R := PolynomialRing(F,2*t);
	pols := [R.1-1];
	for i in [1..t] do;
		Append(~pols,(R.(2*i-1))*(R.(2*i)) - 1);
		end for;
	for i in [1..t] do;
		r1 := 0;
		r2 := 0;
		for j in [1..t] do;	
			r1 +:= R.(2*j-1)*CT[j][i];
			r2 +:= R.(2*j)*ComplexConjugate(CT[j][i]);
			end for;
		Append(~pols,r1*r2 - n);
		end for;
	Id1 := ideal<R | pols>;

// Compute the Groebner basis of the ideal

	R := RadicalDecomposition(Id1);
	bases := [GroebnerBasis(R[i]) : i in [1..#R]];

	return bases;

end function;

// This function takes output from GroupData and computes a Groebner basis.

FindSolutions := function(GpData);

n := Index(GpData[1], GpData[2]);
U := GpData[2];
e := Exponent(U/CommutatorSubgroup(U));
B := CyclotomicField(e);

sols := GetGroebner(GpData[7], n, B);
sols2 := [];
for i in [1..#sols] do;
	if ValidLastPoly(sols[i]) then;
	Append(~sols2,sols[i]);					
	end if;
end for;

return sols2;
end function;


MyMinPoly:= function(list);

	n := #list;
        B := BaseRing(Parent(list[1]));	
	K<z> := PolynomialRing(B);	
	P := Parent(list[n]);

	evals := [ K!0 : i in [1..n-1] ];
	Append(~evals, z);

	phi := hom<P->K | evals>;
	
	q6 := phi(list[n]);
	k6 := SplittingField(q6);
	r6 := Roots(q6, k6);

        return AbsoluteMinimalPolynomial(r6[1,1]);


end function;
