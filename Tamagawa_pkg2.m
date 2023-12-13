freeze;

/******************************************************************************

   Regular models of arithmetic surfaces -- Tamagawa numbers

   Raymond van Bommel, March 2017

******************************************************************************/

// Some reference: http://arxiv.org/abs/math/9804069

// Begin: copied from source RegularModels
function multiplicity_of_point(idl, pt)
  Pol := Generic(idl);
  S := Scheme(AffineSpace(Pol), idl);
  F := Universe(pt`coords);
  d := Degree(F, BaseRing(Pol));
  m := Multiplicity(S, S(F)! pt`coords);

  return d*m;
end function;
// End: copied from source RegularModels

function SelfintersectionNumber(Hp, i)
	//print "Selfintersection,", i;
	M := IntersectionMatrix(Hp);
	j := Index(Hp`regular_fibres_indices, i);
	return M[j][j];
end function;

function IntersectionNumber(Hp, i, j)	// Copied more or less from source RegularModels.
	if (i eq j) then
		return SelfintersectionNumber(Hp, i);
	end if;
	intn_pts := [pt : pt in Hp`points | pt`is_regular and {i, j} subset pt`fibres];	// There are no non-regular fibres per assumption.
	m := 0;
	for pt in intn_pts do
		idx := pt`patch;
		intn := Hp`abstract_fibres[i]`explicit[idx]`ideal + Hp`abstract_fibres[j]`explicit[idx]`ideal;
		m +:= multiplicity_of_point(intn, pt`explicit[idx]);
	end for;
	return m;
end function;

function FindFrobeniusImage(Hp, i, e)	// Find the image of Frobenius of point i.
	
	assert(Type(Hp) eq CrvRegModel);
	assert(Type(i) eq RngIntElt);	// Some basic assertions.
	assert((1 le i) and (i le #Hp`points));
	assert(Type(e) eq RngIntElt);
	assert(1 le e);
	
	patch1 := Hp`points[i]`patch;
	coords1 := Hp`points[i]`explicit[patch1]`coords;
	p := #PrimeField(Hp`points[i]`field);
	frobcoords := [x^(p^e) : x in coords1];
	ans := -1;
	
	for j in [1..#Hp`points] do
		patch2 := Hp`points[j]`patch;
		coords2 := Hp`points[j]`explicit[patch2]`coords;
		if (patch1 eq patch2) and (coords2 eq frobcoords) then
			ans := j;
		end if;
	end for;
	
	assert(0 le ans);
	return ans;
	
end function;

function FindComponentFrobenius(Hp, L, i, e)	// Find image of component i under Frobenius
	patch := Hp`abstract_fibres[i]`patch1;
	ideal := Hp`abstract_fibres[i]`explicit[patch]`ideal;
	patchideal := Hp`patches[patch]`ideal_k;
	R<xx, yy, zz> := Parent(Generators(ideal)[1]);
	K := BaseRing(R);
	p := #PrimeField(K);
	if (IsPrimeField(K)) then
		frobK := hom< K -> K | >;
	else
		frobK := hom< K -> K | Generator(K)^(p^e) >;
	end if;
	frobR := hom< R -> R | frobK, xx, yy, zz >;
	frobideal := ideal< R | [frobR(x) : x in Generators(ideal)]>;
	frobpatchideal := ideal< R | [frobR(x) : x in Generators(patchideal)] >;
	assert(patchideal eq frobpatchideal);	// Just a sanity check, sometimes the ideal is not defined over the right field. Then we should stop.
	ret := -1;
	for j in [1..#L] do
		fib := Hp`abstract_fibres[L[j][1]];
		if (patch eq fib`patch1) then
			if (frobideal eq fib`explicit[patch]`ideal) then
				ret := j;
			end if;
		end if;
	end for;
	assert(ret ge 0);
	return ret;	
end function;

function FindBlownUpPoints(Hp, i)	// Find indices of points blown up in patch i.

	assert(Type(Hp) eq CrvRegModel);
	assert(Type(i) eq RngIntElt);	// Some basic assertions.
	assert(i in [x[1] : x in Keys(Hp`patches)]);
	
	L := [];
	for j in [1..#Hp`points] do
		P := Hp`points[j];
		if P`is_regular eq false then
			if P`patch[1] eq i then
				Append(~L, j); 
			end if;
		end if;
	end for;
	return L;
	
end function;

function RecurseThroughPatches(Hp, fibresperpatch, i, curfrob)

	//print "RecurseThroughPatches(Hp, fibresperpatch, ", i, ",", curfrob, ")";
	//print "----BEGIN----";

	// L = list of: [original fibre id, image frobenius]
	L := [];
	
	// Finv = inverse-frobenius : fibre index in matrix |-> original fibre index in matrix
	Finv := AssociativeArray();
	
	// M = intersection matrix
	M := [];
	
	// Find components in this patch and how Frobenius maps them.
	for fibid in fibresperpatch[i] do
		Append(~L, [fibid, -1]);
	end for;
	//print "L =", L;
	for j in [1..#L] do
		if (L[j][2] eq -1) then
			L[j][2] := FindComponentFrobenius(Hp, L, L[j][1], curfrob);
			Finv[L[j][2]] := j;
			//print "1: Finv[", L[j][2], "] =", j;
		end if;
	end for;
	M := [[IntersectionNumber(Hp, L[i][1], L[j][1]) : i in [1..#L]] : j in [1..#L]];
	
	// Recurse through points blownup.
	blownup := FindBlownUpPoints(Hp, i);
	copynr := 1;
	
	while (#blownup ge 1) do
		//print #blownup, "points left";
		P := blownup[1];
		Q := P;
		FrobImageP := [P];
		while (FindFrobeniusImage(Hp, Q, curfrob) ne P) do
			Q := FindFrobeniusImage(Hp, Q, curfrob);
			Append(~FrobImageP, Q);
		end while;
		nr := #FrobImageP;
		//print "Now considering", nr, "of them";
		newfrob := curfrob * nr;

		L2, M2 := RecurseThroughPatches(Hp, fibresperpatch, Hp`points[P]`blownup, newfrob);
		
		// Add nr copies of L2 and M2 to L and M
		for k in [1..nr-1] do
			curind := #L;	// Shift everything by this number.
			for m in [1..#L2] do
				Append(~L, [L2[m][1], curind + m + #L2]);	// Frobenius permutes these parts cyclically.
				Finv[curind + m + #L2] := #L;
				//print "2: Finv[", curind + m + #L2, "] =", #L;
			end for;
		end for;
		for k in [nr] do
			curind := #L;
			for m in [1..#L2] do
				Append(~L, [L2[m][1], curind + L2[m][2] - #L2*(nr-1)]);	// After nr cycles, it should act as recursively found frobenius.
				Finv[curind + L2[m][2] - #L2*(nr-1)] := #L; 
				//print "3: Finv[", curind + L2[m][2] - #L2*(nr-1), "] =", #L;
			end for;
		end for;
		prevM := #M;
		for k in [1..nr] do
			for m in [1..#L2] do
				Append(~M, []);
				for n in [1..prevM] do
					n2 := n;
					k2 := k-1;
					while k2 ge 1 do
						n2 := Finv[n2];
						k2 -:= 1;	// Take k-1 times the inverse Frobenius for n
					end while;
					Append(~M[n], IntersectionNumber(Hp, L[n2][1], L2[m][1]));	// Add row
					Append(~M[#M], IntersectionNumber(Hp, L[n2][1], L2[m][1]));	// Add column
				end for;				
			end for;
		end for;
		for k1,k2 in [1..nr] do
			for m1,m2 in [1..#L2] do
				if (k1 eq k2) then
					Append(~M[prevM+(k1-1)*#L2+m1], M2[m1][m2]); // Complete last block
				else
					Append(~M[prevM+(k1-1)*#L2+m1], 0);
				end if;
			end for;
		end for;
		//print "Just considered point", P, "eleminating", nr, "points";
		blownup := [x : x in blownup | not(x in FrobImageP)];
	end while;


	// Calculate intersection matrix, to be modified

	fibres := [Hp`abstract_fibres[fib[1]] : fib in L];
	mults  := [fib`multiplicity : fib in fibres];

	//print "End function on ", i;
	//print "Output:";
	//print L;
	//print M;
	
	//print "----END----";
	return L, M;
	
end function;

function FrobeniusOrder(frob, i)
	ret := 1;
	j := frob[i];
	while (j ne i) do
		j := frob[j];
		ret +:= 1;
	end while;
	return ret;
end function;


intrinsic TamagawaNumber(Hp::CrvRegModel) -> RngIntElt
{Computing the Tamagawa number of a regular model}

/*function TamagawaGetal(H, p)
	
	assert(Type(H) eq CrvHyp);	// Assert H is an hyperelliptic curve over Q.
	assert(Type(BaseField(H)) eq FldRat);
	assert(Type(p) eq RngIntElt);	// Assert p is a rational prime.
	assert(IsPrime(p));
	
	//H := MinimalWeierstrassModel(H);
	try
		Hp := RegularModel(H, p);
	catch e
		print "Regular model for p =", p, "cannot be computed for", H;
		return -1;
	end try;*/
	G := ComponentGroup(Hp);
	if assigned(Hp`model_with_split_components) then
		Hp := Hp`model_with_split_components;
	end if;
	
	fibresperpatch := [[] : i in [1..Max([x[1] : x in Keys(Hp`patches)])]];
	for i in [1..#Hp`abstract_fibres] do	// Assume there are no fibres being blown-up.
		fib := Hp`abstract_fibres[i];
		if not(fib`is_regular) then
			print "Warning: one of the components in the special fibre is not regular. This should only happen in the case when these components are geometrically irreducible. (Otherwise, the regular model is not computable.) The output is not guaranteed to be correct.";
			return #G;
		end if;
		Append(~fibresperpatch[fib`patch1[1]], i);
	end for;
	
	L,M := RecurseThroughPatches(Hp, fibresperpatch, 1, 1);
	M := Matrix(M);

	// Copied from source code RegularModels
	//mat := IntersectionMatrix(Hp);
	mults := [Hp`abstract_fibres[L[i][1]]`multiplicity : i in [1..#L]]; // Has to be reordered.
	assert Nrows(M) eq #mults;
 
	f := #mults;
	A := FreeAbelianGroup(#mults);
	Z := FreeAbelianGroup(1);
	B := Kernel(hom< A->Z | [m*Z.1 : m in mults] >);
	C,q := quo< B | [B| &+[M[i,j]*A.i : i in [1..f]] : j in [1..f]] >;
 
 	
 	// Construct Frobenius
 	frob := [i : i in [1..f]];
 	assert(#L eq f);
 	for i in [1..f] do
 		frob[i] := L[i][2];
 	end for;
	assert(M eq Matrix([[ M[i,j] : i in frob ] : j in frob ]));	// Check that the intersection matrix is Frobenius-invariant.
	assert(mults eq [mults[i] : i in frob]); // Check that the multiplicities are Frobenius-invariant.

 	map1 := hom< A->A | [A.frob[i] : i in [1..#Generators(A)]] >;
 	map2 := hom< B->C | [q(map1(B.i)) : i in [1..#Generators(B)]] >;
 	for b in [B| &+[M[i,j]*A.i : i in [1..f]] : j in [1..f]] do
 		assert map2(b) eq Zero(C);
 	end for;
 	map3 := hom< C->C | [map2((q^(-1))(C.i)) - C.i : i in [1..#Generators(C)]] >;
	D := Kernel(map3);

	assert IsFinite(C);
	
	/* D = Ker beta / Im alpha, in the sense of [Bosch-Liu, Thm. 1.11]
	// Now we calculate q, d and d'
	// This does not make sense, we are calculating the G-module as in [Bosch-Liu, Thm. 1.1]
	
	dprime := GCD(mults);
	d := GCD([FrobeniusOrder(frob,i)*mults[i] : i in [1..#mults]]);
	q := 2;
	if IsDivisibleBy(Genus(Hp`C)-1, dprime) then
		q := 1;
	end if;
	//return #D*dprime / (d*q);*/
	return #D; //, D, C, map3, frob, L, M;
end intrinsic;

/*
Load sample cases

H1 := HyperellipticCurve([1,0,6,-2]);
H2 := HyperellipticCurve([1,0,6,7]);
H3 := HyperellipticCurve([1,0,4,-4]);
H4 := HyperellipticCurve([1,0,4,-3]);
H5 := HyperellipticCurve([1,0,4,4]);

Hp1 := RegularModel(H1, 3);
G := ComponentGroup(Hp1);
Hp1 := Hp1`model_with_split_components;
Hp2 := RegularModel(H2, 3);
G := ComponentGroup(Hp2);
Hp2 := Hp2`model_with_split_components;
Hp3 := RegularModel(H3, 2);
G := ComponentGroup(Hp3);
//Hp3 := Hp3`model_with_split_components;
Hp4 := RegularModel(H4, 2);
G := ComponentGroup(Hp4);
Hp4 := Hp4`model_with_split_components;
Hp5 := RegularModel(H5, 2);
G := ComponentGroup(Hp5);
Hp5 := Hp5`model_with_split_components;
*/


// For EC([13,14]) at p=2 no RegularModel can be computed!

intrinsic TamagawaSelfTest() -> BoolElt
{Self-testing of the Tamagawa code for regular models}
	R<x> := PolynomialRing(Rationals());
	anyfail := false;
	for a,b in [-15..15] do
		print "a, b =", a, b;
		f := x^3 + a*x + b;
		if IsSeparable(f) then
			E := EllipticCurve(f);
			H := HyperellipticCurve(f);
			for p in BadPrimes(E) do	// Remark: BadPrimes(H) is not BadPrimes(E), the former always contains 2.
				print "p = ", p;
				tamgw1 := TamagawaNumber(E, p);
				try
					Hp := RegularModel(H,p);
					tamgw2 := TamagawaNumber(Hp);
				catch e
					print e;
					tamgw2 := 0;
				end try;
				if (tamgw1 ne tamgw2) then
					print "FAIL";
					anyfail := true;
					break;
				end if;
			end for;
		end if;
		if anyfail then
			break;
		end if;
	end for;

	return anyfail;
end intrinsic;
