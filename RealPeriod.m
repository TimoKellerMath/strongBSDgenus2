// Computation of the real period for arbitrary curves over Q.
// by: Raymond van Bommel

function PolyMor(pol, phi1, phi2)	// Given a "morphism" A -> B and a "morphism" Z[x1, .., xn] -> B construct the associated "morphism" A[x1, .., xn] -> B.
	if (Type(pol) eq SeqEnum) then
		return [PolyMor(p, phi1, phi2) : p in pol];
	end if;
	ret := 0;
	mon := Monomials(pol);
	coeff := Coefficients(pol);
	assert(#mon eq #coeff);
	for i in [1..#mon] do
		ret +:= phi1(coeff[i])*phi2(mon[i]);
	end for;
	return ret;
end function;



declare attributes CrvRegModel:
	MapFromParentK,	// Assoc -> Map
	//MapFromParentZ,	// Assoc -> Map
	patchK,			// Assoc -> FldFunFracSch
	patchZ,			// Assoc -> RngMPol
	PatchEquations,	// Assoc -> SeqEnum
	PatchIdeal,		// Assoc -> RngMPol
	pointsRP,			// SeqEnum
	FibreEquations,	// Assoc -> SeqEnum
	IdealModPrimePower,	// Assoc -> SeqEnum+
	IdealModPrimePower1,	// Assoc -> SeqEnum
	IdealModPrimePowerReduction,	// Assoc -> Assoc -> Map
	phi1,			// Assoc -> Map
	phi2,			// Assoc -> Map
	red,			// Assoc -> Map
	lift,			// Assoc -> Map
	MyMultiplicities,	// Assoc -> RngIntElt
	ComputedVanishingOrders;	// Assoc -> RngIntElt

procedure GeneratePatchData(Hp)
	if not(assigned(Hp`patchK)) then
		Hp`patchK := AssociativeArray();
		Hp`patchZ := AssociativeArray();		// Put empty arrays.
		Hp`MapFromParentK := AssociativeArray();
		//Hp`MapFromParentZ := AssociativeArray();
		Hp`phi1 := AssociativeArray();
		Hp`phi2 := AssociativeArray();
		Hp`red := AssociativeArray();
		Hp`lift := AssociativeArray();
		Hp`PatchEquations := AssociativeArray();
		Hp`PatchIdeal := AssociativeArray();
		Hp`ComputedVanishingOrders := [];
		Hp`patchK[<0,1>] := FunctionField(Hp`C);	// Function field of original curve.
		Hp`pointsRP := [* *];

		S := Sort(SetToSequence(Keys(Hp`patches)));
		for i in S do		// Keys have to be considered in chronological order.
			patchR<ix,iy,iz> := Parent(Hp`patches[i]`eqns[1]);
			OL := BaseRing(patchR);
			//RZ<tx,ty,tz,tw> := PolynomialRing(Integers(), 4, "grevlex");	// Five variables: tx, ty, tz usual coordinates, tw to define ring OL over Z, and tv to invert other fibres (not used in this part).
			if (Degree(OL) eq 1) then
				RZ<tx,ty,tz> := PolynomialRing(Integers(), 3, "grevlex");
				Hp`phi1[i] := hom < OL->RZ | >;
				eqn := 0;
			else	// Map from OL to RZ is defined differently in the number ring case.
				RZ<tx,ty,tz,tw> := PolynomialRing(Integers(), 4, "grevlex");
				assert (OL eq EquationOrder(OL));
				OL := EquationOrder(OL);
				eqn := DefiningPolynomial(OL);
				phi0 := hom < Parent(eqn) -> RZ | tw >;
				eqn := phi0(eqn);
				Hp`phi1[i] := hom < OL -> RZ | tw >;
			end if;
			Hp`phi2[i] := hom < patchR->RZ | [tx,ty,tz] >;
			Hp`PatchEquations[i] := PolyMor(Hp`patches[i]`eqns, Hp`phi1[i], Hp`phi2[i]) cat [eqn];	// Create a list of polynomials in RZ.
			Hp`PatchIdeal[i] := ideal < RZ | Hp`PatchEquations[i] >;
			//Groebner(Hp`PatchIdeal[i]);

			RQ := ChangeRing(RZ, Rationals());
			//I := ideal < RQ | Hp`PatchEquations[i]>; // cat [tv]>;
			//A5 := AffineSpace(RQ);
			//C := Curve(Scheme(A5,I));
			K<px,py,pz> := FieldOfFractions(RQ);
			Hp`patchK[i] := K;	// Generate function field.
			Hp`patchZ[i] := RZ;
			Hp`red[i] := hom < RZ -> K | [K.i : i in [1..Rank(RZ)]] >;
			Hp`lift[i] := hom < K -> RZ | [RZ.i : i in [1..Rank(RZ)]] >;


/*			if (i eq <1,1>) then
				if (Type(Hp`C) eq CrvHyp) then
					Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [1/py, px/py^(Genus(Hp`C)+1)] >;
				elif (Type(Hp`C) eq CrvPln) then
					Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [Hp`patches[i]`map[j] / Hp`patches[i]`map[3] : j in [1..2]] >;
				else
					assert(false);
				end if;
			elif (i eq <1,2>) then
				assert(Type(Hp`C) eq CrvPln);
				Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [Hp`patches[i]`map[j] / Hp`patches[i]`map[3] : j in [1..2]] >;
			elif (i eq <1,3>) then
				if (Type(Hp`C) eq CrvHyp) then
					Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [px, py] >;
				elif (Type(Hp`C) eq CrvPln) then
					Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [Hp`patches[i]`map[j] / Hp`patches[i]`map[3] : j in [1..2]] >;
OLD CODE; can probably be removed */

			if (i[1] eq 1) then // Construct map from parent: slightly different for initial patches.
				w := Gradings(AmbientSpace(Hp`C))[1];
				assert(w[3] eq 1);
				Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [PolyMor(Hp`patches[i]`map[j], Hp`phi1[i], Hp`phi2[i]) / PolyMor(Hp`patches[i]`map[3]^(w[j]), Hp`phi1[i], Hp`phi2[i]) : j in [1..2]] >;
				//vprint User2: "Map from original patch at i =", i, ":", [Hp`patches[i]`map[j] / Hp`patches[i]`map[3]^(w[j]) : j in [1..2]];
			else
				Hp`MapFromParentK[i] := hom < Hp`patchK[Hp`patches[i]`parent]->Hp`patchK[i] | [Hp`red[i](x) : x in PolyMor(Hp`patches[i]`map, Hp`phi1[i], Hp`phi2[i])] cat [K.i : i in [4..Rank(RZ)]] >; //, pv] >;
			end if;
		end for;
	end if;
end procedure;

function MyFunctionField(Hp, ind)
// {Find the function field of a patch together with a map from the parent function field.
//Moreover, it returns a polynomial ring over Z, list of equations used to construct function field, together with a reduction and lifting map.}
	if not(assigned(Hp`patchK)) then
		GeneratePatchData(Hp);
	end if;
	assert((ind in Keys(Hp`patches)) or (ind eq <0,1>)); //"Key is not in the list of patch keys";
	if (ind[1] eq 0) then
		return Hp`patchK[ind];
	else
		return Hp`patchK[ind], Hp`MapFromParentK[ind], Hp`patchZ[ind], Hp`PatchEquations[ind], Hp`red[ind], Hp`lift[ind];
	end if;
end function;

intrinsic PatchEquations(Hp::CrvRegModel, ind::Tup) -> SeqEnum
{Find the equations for a patch.}
	if not(assigned(Hp`patchK)) then
		GeneratePatchData(Hp);
	end if;
	require ind in Keys(Hp`patches): "Key is not in the list of patch keys";
	return Hp`PatchEquations[ind];
end intrinsic;

function FunctionFieldLiftMap(Hp, ind)
//{Returns the lifting map from the function field to the ring.}
	if not(assigned(Hp`patchK)) then
		GeneratePatchData(Hp);
	end if;
	assert(ind in Keys(Hp`patches));//"Key is not in the list of patch keys";
	return Hp`lift[ind];
end function;

intrinsic PatchIdeal(Hp::CrvRegModel, i::Tup) -> RngMPol
{Get ideal for the i-th patch of regular model Hp.}
	require(i in Keys(Hp`patches)): "Index is not the index of a patch of regular model.";
	if not(assigned(Hp`patchK)) then
		GeneratePatchData(Hp);
	end if;
	return Hp`PatchIdeal[i];
end intrinsic;

procedure GenerateFibreData(Hp)
	if not(assigned(Hp`FibreEquations)) then
		//mults := Multiplicities(Hp);
		Hp`FibreEquations := AssociativeArray();
		Hp`IdealModPrimePower := AssociativeArray();
		Hp`IdealModPrimePower1 := AssociativeArray();
		Hp`IdealModPrimePowerReduction := AssociativeArray();
		for i in [1..#Hp`abstract_fibres] do

			// (1) Construct a list of equations in RZ, the algebra over Z

			fibre := Hp`abstract_fibres[i];
			patch := fibre`patch1;
			patchK, MfP, RZ, patchEq := MyFunctionField(Hp, patch);
			gens_modp := Generators(fibre`explicit[patch]`ideal);
			baseField := BaseRing(Parent(gens_modp[1]));
			p := Characteristic(baseField);

			if (#baseField eq p) then
				phi2 := hom< Parent(gens_modp[1])->RZ | [RZ.1, RZ.2, RZ.3] >;
			else
				phi1 := hom < baseField->RZ | RZ.4 >;
				phi2 := hom< Parent(gens_modp[1])->RZ | phi1, [RZ.1, RZ.2, RZ.3] >;
			end if;

			fibEq := [phi2(g) : g in gens_modp] cat patchEq;

			/*// (2) Find equations to invert the other components. Not necessary anymore.
			Rp := ChangeRing(RZ, GF(p));
			I := ideal < Rp | patchEq >;
			P := ideal < Rp | fibEq >;
			otherFactors := ideal < Rp | 1>;
			for Q in RadicalDecomposition(I) do
				if (P ne Q) then
					otherFactors *:= Q;
				end if;
			end for;

			liftMap := hom < Rp->RZ | [RZ.i : i in [1..Rank(RZ)]] >;
			for a in Generators(otherFactors) do
				if not(a in P) then
					//Append(~fibEq, RZ.5*liftMap(a) - 1);
					//Append(~fibEq, RZ.5);
					break;
				end if;
			end for;*/

			// (3) Take ideal generated by it.
			P := ideal < RZ | fibEq >;
			Hp`FibreEquations[i] := Generators(P);
			Hp`IdealModPrimePower[i] := [];
			Hp`IdealModPrimePower1[i] := [];
			Hp`IdealModPrimePowerReduction[i] := AssociativeArray();
			Hp`ComputedVanishingOrders[i] := AssociativeArray();

		end for;
	end if;
end procedure;

intrinsic ComponentEquations(Hp::CrvRegModel, i::RngIntElt) -> SeqEnum
{Find the equations for the i-th fibre in its main patch.}
	if not(assigned(Hp`FibreEquations)) then
		GenerateFibreData(Hp);
	end if;
	require(i in [1..#Hp`abstract_fibres]): "Index is not the index of a component in the special fibre.";
	return Hp`FibreEquations[i];
end intrinsic;

procedure ComputeMultiplicity(Hp, i)
	K, phi, RZ, eqnP := MyFunctionField(Hp, Hp`abstract_fibres[i]`patch1);
	eqnC := ComponentEquations(Hp, i);
	p := #PrimeField(Hp`k);
	Rp := ChangeRing(RZ, Integers(p^2));
	k := 1;
	I := ideal < Rp | eqnP > + ideal < Rp | eqnC >;
	I1 := I;
	Ip := ideal < Rp | p >;
	while true do
		//I := ideal < Rp | eqnP > + ideal < Rp | eqnC>^k;
		//vprint User1: GroebnerBasis(I);
		//Groebner(I);		doesn't save time as ColonIdeal already does this
		if (ColonIdeal(I, Ip) subset I1) then
			Hp`MyMultiplicities[i] := k-1;
			return;
		end if;
		vprint User1: "Tried k =", k;
		k +:= 1;
		I := I* ideal <Rp | eqnC > + ideal < Rp | eqnP >;
	end while;
end procedure;

intrinsic MyMultiplicity(Hp::CrvRegModel, i::RngIntElt) -> RngIntElt
{Get multiplicity of i-th component of special fibre of Hp.}
	require (i in [1..#Hp`abstract_fibres]): "Index is not the index of a component in the special fibre";
	if not(assigned(Hp`MyMultiplicities)) then
		Hp`MyMultiplicities := AssociativeArray();
		for j in [1..#Hp`abstract_fibres] do
			ComputeMultiplicity(Hp, j);
		end for;
	end if;
	return Hp`MyMultiplicities[i];
end intrinsic;

procedure SimplifyPowerIdeal(~I, Iminusone, P)
// For each generator of Iminus one, check if it is in I localised at P. If so add generator to I.
	for g in Generators(Iminusone) do
		if not(ColonIdeal(I, Ideal(g)) subset P) then
			I := I + Ideal(g);
		end if;
	end for;
	Groebner(I);
end procedure;

intrinsic ComponentIdealModPrimePower(Hp, i, j) -> RngMPol
{Get ideal for the i-th fibre in Z/p^(j/multiplicity)Z.}
	assert(i in [1..#Hp`abstract_fibres]);//: "Index is not the index of a component in the special fibre.";
	K, phi, RZ, eqnP := MyFunctionField(Hp, Hp`abstract_fibres[i]`patch1);
	eqnC := ComponentEquations(Hp, i);
	for k in [#Hp`IdealModPrimePower[i]+1..j] do
		exp := Ceiling(k / MyMultiplicity(Hp, i));

		// In case the exponent didn't change, continue from the point where we were.
		if (k ge 2) and (Ceiling((k-1) / MyMultiplicity(Hp, i)) eq exp) then
			Hp`IdealModPrimePower1[i][k] := Hp`IdealModPrimePower1[i][k-1];
			Rp := Generic(Hp`IdealModPrimePower[i][k-1]);
			Hp`IdealModPrimePower[i][k] := Hp`IdealModPrimePower[i][k-1] * Hp`IdealModPrimePower1[i][k] + ideal < Rp | eqnP >;
			Groebner(Hp`IdealModPrimePower[i][k]);
			Hp`IdealModPrimePowerReduction[i][k] := Hp`IdealModPrimePowerReduction[i][k-1];
			SimplifyPowerIdeal(~Hp`IdealModPrimePower[i][k], Hp`IdealModPrimePower[i][k-1], Hp`IdealModPrimePower1[i][k]);
			continue;
		end if;

		// In other case, construct everything from the start.
		pk := #PrimeField(Hp`k)^exp;
		if (IsPrime(pk)) then
			Rp := ChangeRing(RZ, GF(pk));
		else
			Rp := ChangeRing(RZ, Integers(pk));
		end if;

		Hp`IdealModPrimePower1[i][k] := ideal < Rp | eqnP > + ideal < Rp | eqnC >;
		Groebner(Hp`IdealModPrimePower1[i][k]);
		Hp`IdealModPrimePower[i][k] := Hp`IdealModPrimePower1[i][k];
		for l in [2..j] do
				PrevIdeal := Hp`IdealModPrimePower[i][k];
				Hp`IdealModPrimePower[i][k] := ideal < Rp | eqnP > + Hp`IdealModPrimePower1[i][k] * Hp`IdealModPrimePower[i][k];
				SimplifyPowerIdeal(~Hp`IdealModPrimePower[i][k], PrevIdeal, Hp`IdealModPrimePower1[i][k]);
		end for;
		Hp`IdealModPrimePowerReduction[i][k] := hom < RZ->Rp | [Rp.i : i in [1..Rank(Rp)]] >;
	end for;
	return Hp`IdealModPrimePower[i][j], Hp`IdealModPrimePowerReduction[i][j], Hp`IdealModPrimePower1[i][j];
end intrinsic;

function LocalVanishingOrder(Hp, f, k : Max := 1000000)
	// Calculate order of vanishing of f in k-th fibre
	if (f in Keys(Hp`ComputedVanishingOrders[k])) then
		return Hp`ComputedVanishingOrders[k][f];
	end if;

	// Try to factor and compute orders of factors separately
	Fact := Factorisation(f);
	if #Fact ge 2 then
		ret := 0;
		for g in Fact do
			assert(g[2] ge 0);
			ret +:= LocalVanishingOrder(Hp, g[1], k : Max := Max) * g[2];
		end for;
		if (ret ge Max)	then
			return Max;
		end if;
		Hp`ComputedVanishingOrders[k][f] := ret;
		return Hp`ComputedVanishingOrders[k][f];
	end if;

	vprint User1: "LocalVanishingOrder(Hp,", f, ",", k, ")";
	assert k in [1..#Hp`abstract_fibres];
	//J := PatchIdeal(Hp, Hp`abstract_fibres[k]`patch1);
	//assert not(f in J); Removed, takes long to test


	for j in [1..Max] do
		if (j gt 1) then
			vprint User1: "Trying j =", j;
		end if;
		I, phi, Ip := ComponentIdealModPrimePower(Hp, k, j);
		//vprint User1: "Colon ideal(", I, ",", Ideal(phi(f)), ") =", ColonIdeal(I, Ideal(phi(f)));
		//vprint User1: "check if contained in", Ip;
		if ColonIdeal(I, Ideal(phi(f))) subset Ip then
			//if k eq 1 then
			//	print "LocalVanishingOrder(", f, ") =", j-1;
			//end if;
			Hp`ComputedVanishingOrders[k][f] := j-1;
			return j-1;
		end if;
	end for;

	assert Max lt 1000000;
	return Max;
end function;

procedure AttachPointsOnComponent(Hp, k : Max := "infty")
// Tries to find points to attach lying on the k-th component.
	I := ComponentIdealModPrimePower(Hp, k, 1);
	R<tx> := I^0;
	p := #BaseRing(I);
	if not(IsPrime(p)) then
		return;
	end if;
	if (Type(Max) eq MonStgElt) then
		Max := p+1;
	end if;
	found := 0;
	for x in [0..p-1] do
		J := I + ideal<R | tx - x>;	// Possible improvements: do this for other variables as well, also try higher degree polynomials in small characteristic
		vprint User1: "Trying x = ",x;
		vprint User1: "found", RadicalDecomposition(J);
		for K in RadicalDecomposition(J) do
			if (#(R/K) ne 1) and (#(R/K) ne Infinity()) then
				Q, red := R/K;
				while #Hp`pointsRP lt k do
					Append(~Hp`pointsRP, [* *]);
				end while;
				Append(~Hp`pointsRP[k], red);
				vprint User1: "added", red;
				found +:= 1;
				if (found ge Max) then
					return;
				end if;
			end if;
		end for;
	end for;
end procedure;

intrinsic AttachPointsOnSpecialFibre(Hp::CrvRegModel : Max := "infty")
{Put points on the special fibre in the data structure to make computations faster.}
	for k in [1..#Hp`abstract_fibres] do
		AttachPointsOnComponent(Hp, k : Max := Max);
		while #Hp`pointsRP lt k do
			Append(~Hp`pointsRP, [* *]);
		end while;
	end for;
	/*I := ComponentIdealModPrimePower(Hp, 1, 1); OLD CODE: only added rational points in first component
	R<tx> := I^0;
	p := #BaseRing(I);
	assert IsPrime(p);
	if (Type(Max) eq MonStgElt) then
		Max := p+1;
	end if;
	found := 0;
	for x in [0..p-1] do
		J := I + ideal<R | tx - x>;
		//print "Trying x = ",x;
		//print "found", #(R/J);
		for K in RadicalDecomposition(J) do
			if #(R/K) eq p then
				Q, red := R/K;
				Append(~Hp`points, red);
				found +:= 1;
				if (found ge Max) then
					return;
				end if;
			end if;
		end for;
	end for;*/
	return;
end intrinsic;



declare type DiffRegMod;

declare attributes DiffRegMod:
	Hp,		// CrvRegModel
	D,		// DivFunElt
	fdx,	// Assoc -> FunFldElt
	fReg,		// Assoc -> FunFldElt
	PointResidue,	// SeqEnum
	NoResidue;		// SetEnum

function RewriteDifferential(g, h, K, eqns)
// Rewrite differential g*dh in the form f*dx

	// Step 1: find kernel of matrix with derivatived to express other differentials in dx
	// 			we assume dx is a generator and this is possible.
	ker := Kernel(Matrix([[Derivative(e, i) : e in eqns] : i in [1..Rank(K)]]));
	assert Dimension(ker) eq 1;
	b := Basis(ker)[1];
	assert(b[1] ne 0);
	mult := [b[i]/b[1] : i in [1..Rank(K)]];

	// Step 2: compute derivatives of h with respect to the different variables and add results
	ret := K!0;
	for i in [1..Rank(K)] do
		ret +:= Derivative(h, i) * mult[i];
	end for;

	return g*ret;
end function;

intrinsic DifferentialOnRegularModel(D::DiffCrvElt, Hp::CrvRegModel : Check := true) -> DiffRegMod
{Create differential on a regular model from a differential on the original curve.}

	if Check then
		require IsIsomorphic(BaseChange(Curve(D), BaseRing(Hp`C)), Hp`C): "Differential is not defined on the curve underlying the regular model.";
	end if;
	S := Sort(SetToSequence(Keys(Hp`patches)));
	// Make new object.
	Dreg := New(DiffRegMod);
	Dreg`Hp := Hp;
	K<x, y> := MyFunctionField(Hp, <0,1>);
	M<xM> := FunctionField(Curve(D));
	phi := hom < FunctionField(Curve(D))->K | [x, y] >;
	Dreg`D := phi(D/Differential(xM)) * Differential(x);
	Dreg`fdx := AssociativeArray();
	Dreg`fdx[<0,1>] := phi(D/Differential(xM));
	Dreg`fReg := AssociativeArray();
	Dreg`fReg[<0,1>] := 0;
	Dreg`PointResidue := [* *];
	Dreg`NoResidue := {};

	for i in S do
		// Find differential by applying map from parent.
		K, phi, RZ<tx, ty, tz>, eqns, red := MyFunctionField(Hp, i);
		j := Hp`patches[i]`parent;
		Kparent<xp> := MyFunctionField(Hp, j);

		// Find the f such that the differential is f*dx and express everything in terms of the generator of the sheaf.
		fdx := RewriteDifferential(phi(Dreg`fdx[j]), phi(xp), K, [red(f) : f in eqns]);
		//vprint User1: "Differential on fibre", i, ":", fdx, "dx";
		eq1dy := Derivative(eqns[1],ty);
		eq2dy := Derivative(eqns[2],ty);
		eq1dz := Derivative(eqns[1],tz);
		eq2dz := Derivative(eqns[2],tz);
		Dreg`fdx[i] := fdx;
		Dreg`fReg[i] := red(eq1dy*eq2dz - eq1dz*eq2dy)*fdx;
	end for;

	return Dreg;
end intrinsic;

intrinsic '+'(D1::DiffRegMod, D2::DiffRegMod) -> DiffRegMod
{Return D1 + D2}
	require D1`Hp`C eq D2`Hp`C: "Differentials not defined on the same curve";
	D := New(DiffRegMod);
	D`Hp := D1`Hp;
	D`D := D1`D + D2`D;
	D`fdx := AssociativeArray();
	D`fReg := AssociativeArray();
	D`PointResidue := [* *];
	D`NoResidue := {};
	require(Keys(D1`fdx) eq Keys(D2`fdx)) : "Regular models do not have the same number of patches";
	for i in Keys(D1`fdx) do
		D`fdx[i] := D1`fdx[i] + D2`fdx[i];
		D`fReg[i] := D1`fReg[i] + D2`fReg[i];
	end for;
	return D;
end intrinsic;

intrinsic '*'(c::FldRatElt, D1::DiffRegMod) -> DiffRegMod
{Return c*D1}
	D := New(DiffRegMod);
	D`Hp := D1`Hp;
	D`D := c*D1`D;
	D`fdx := AssociativeArray();
	D`fReg := AssociativeArray();
	D`PointResidue := [* *];
	D`NoResidue := {};
	for i in Keys(D1`fdx) do
		D`fdx[i] := c*D1`fdx[i];
		D`fReg[i] := c*D1`fReg[i];
	end for;
	return D;
end intrinsic;

intrinsic '*'(c::RngIntElt, D::DiffRegMod) -> DiffRegMod
{Return c*D}
	return Rationals()!c * D;
end intrinsic;

/* intinsic '*'(f::FldFunFracSchElt, D1::DiffRegMod) -> DiffRegMod
{Return F*D1}
	TODO
end intrinsic*/

intrinsic Print(D::DiffRegMod){}
	printf "Differential on %o ", D`Hp;
	printf "given by %o", D`D;
end intrinsic;

intrinsic DifferentialVanishingOrder(D::DiffRegMod : Max := 10000, VanishingCheck := false) -> RngIntElt
{Computes the order of vanishing of the differential D on the special fibre of the regular model. Parameter 'VanishingCheck' can be used to save time if the differentials are known to be integral. All differentials are supposed to be regular on the generic fibre.}
	ret := 100*Max;	// This should be considered as being infinity.
	Hp := D`Hp;

	for k in [1..#Hp`abstract_fibres] do
		i := Hp`abstract_fibres[k]`patch1;
		phi := FunctionFieldLiftMap(Hp, i);
		fReg := D`fReg[i];
		num := Numerator(fReg);
		den := Denominator(fReg);
		factor := LCM([Denominator(t) : t in Coefficients(num) cat Coefficients(den)]);
		//factor /:= GCD([Numerator(t) : t in Coefficients(num) cat Coefficients(den)]);
		num *:= factor;
		den *:= factor;
		num := phi(num);
		den := phi(den);

		/*if not(assigned(Hp`abstract_fibres[k]`multiplicity)) then
			mults := Multiplicities(Hp);
		end if;*/

		//vprint User1: "Computing denOrd";
		denOrd := LocalVanishingOrder(Hp, den, k);
    vprintf User1: "ord(den) --> %o\n", denOrd;
		//vprint User1: "Computing numOrd";
		numOrd := LocalVanishingOrder(Hp, num, k : Max := Maximum(ret*MyMultiplicity(Hp, k) + denOrd, 0));
    vprintf User1: "ord(num) --> %o\n", numOrd;
		ret := Min(ret, Floor((numOrd - denOrd) / MyMultiplicity(Hp, k)));

		// Computing residues in points in order to speed up calculation later
		//if k eq 1 then
			if ((numOrd eq 0) and (denOrd eq 0)) then
				I, phi := ComponentIdealModPrimePower(Hp, k, 1);
				while (#D`PointResidue lt k) do
					Append(~D`PointResidue, [* *]);
				end while;
				for i in [#D`PointResidue[k]+1..#Hp`pointsRP[k]] do
					//vprint User1: "Trying point", i;
					rho := Hp`pointsRP[k][i];
					V, psi := VectorSpace(Codomain(rho));
					if rho(phi(den)) eq 0 then
						Append(~D`PointResidue[k], 0);
						Include(~D`NoResidue, [k,i]);
					else
						Append(~D`PointResidue[k], [psi( rho(phi(num)) / rho(phi(den)) )[i] : i in [1..Dimension(V)]]);
					end if;

					/*for x in GF(#(J^0/J)) do // OLD CODE: was inefficient
						if phi(num) - x*phi(den) in J then
							vprint User1: "Found", i;
							Append(~D`PointResidue, x);
							break;
						end if;
					end for;*/
				end for;
			else
				D`PointResidue[k] := [0 : i in Hp`pointsRP[k]];
				Include(~D`NoResidue, [k,-1]);
			end if;
			assert(#(D`PointResidue[k]) eq #Hp`pointsRP[k]);
		//end if;

		if (VanishingCheck) and (ret le 0) then
			return Floor(ret);
		end if;
	end for;

	return Floor(ret);
end intrinsic;













function RealGCD(a, b)	// Also used for regulator
	vprint User1: "RealGCD(", a, ",", b, ")";
	if (b le 1E-10) then
		return a;
	end if;
	if (a/b le 1E-3) then
		return b;
	end if;
	k := Floor(b/a);
	return RealGCD(b - k*a, a);
end function;

function Bool2Int(b)
	// Convert a boolean into an integer.
	if b then
		return 1;
	end if;
	return 0;
end function;

function CompensationFactorAtp(H, p, D)

	assert( (Type(H) eq CrvHyp) or (Type(H) eq CrvPln));	// Assert H is an hyperelliptic curve over the rationals or plane curve. Can maybe be lifted.
	assert(Type(BaseField(H)) eq FldRat);
	//assert(IsSimplifiedModel(H));
	assert(Type(p) eq RngIntElt);	// Assert p is a rational prime.
	assert(IsPrime(p));

	ret := 1;

	try
		Hp := RegularModel(H, p);
		vprint User1: "Regular model computed";
		/*mults := Multiplicities(Hp);
		vprint User1: "Multiplicities computed";*/
	catch e
		print "Regular model could not be constructed at p =", p, "for", H;
		print "Compensation factor (and hence the real period) could be off by a power of", p;
		return ret, p;
	end try;
	AttachPointsOnSpecialFibre(Hp : Max := Max(20, 2*Genus(H)));
	vprint User1: "Points added";

	K<x,y> := FunctionField(H);
	// Translate RiemannSurface basis of differentials to function field
	dx := Differential(FunctionField(Parent(D[1])).1);
	cf := hom < CoefficientField(Parent(D[1]/dx)) -> K | 1 >;
	fh := hom < Parent(D[1]/dx) -> K | cf, [x, y] >;
	basis := [DifferentialOnRegularModel(fh(D[i] / dx)*Differential(x), Hp : Check := false) : i in [1..Genus(H)]];
	vprint User1: "Basis computed";

	arewedone := false;

	while (arewedone eq false) do
		arewedone := true;

		// Check that basis elements are well-defined.
		for i in [1..#basis] do
			ord := DifferentialVanishingOrder(basis[i]);
			vprint User1: "Order of vanishing of", basis[i], "=", ord;
			if (ord ne 0) then
				basis[i] := p^(-ord) * basis[i];
				ret *:= p^(-ord);
				vprint User2: "Correction: replacing basis[", i, "] by", p^(-ord), "*basis[", i, "]";
			end if;
			assert(DifferentialVanishingOrder(basis[i]) eq 0);
		end for;

		NoResidue := &join[b`NoResidue : b in basis];
		//M := Matrix([[GF(p)!0] cat [GF(p)!b`PointResidue[i] : i in [1..#Hp`points[1]] | not(i in NoResidue) ] : b in basis]);
		M := Matrix([[GF(p)!0] cat &cat[&cat[b`PointResidue[k][i] : i in [1..#Hp`pointsRP[k]] | not([k,i] in NoResidue) ] : k in [1..#Hp`pointsRP] | not([k, -1] in NoResidue) ] : b in basis]);

		g := [x : x in Generators(Kernel(M))];
		vprint User1: "Kernel generated by", g;
		if (#g eq 0) then
			return ret, 1;
		end if;

		// Check that there is nothing vanishing everywhere.
		for i in CartesianPower(Set([0..(p-1)]), #g) do
			if (&+[j : j in i] eq 0) then
				continue;
			end if;

			v := &+[i[j]*g[j] : j in [1..#g]];
			D := &+[Integers()!v[j]*basis[j] : j in [1..#basis]];

			ord := DifferentialVanishingOrder(D : VanishingCheck := true);
			if (ord ge 1) then
				for j in [1..#basis] do
					if (v[j] ne 0) then
						basis[j] := 1/p^ord * D;
						vprint User2: "Changing basis: added", basis[j];
						ret /:= p^ord;
						arewedone := false;
						break;
					end if;
				end for;
				assert(arewedone eq false);
				break;
			end if;
		end for;

	end while;

	vprint User3: "at p = ", p;
	vprint User3: "basis = ", basis;

	return ret, 1;
end function;

function RealLatticeArea(M)
	// Given a (2g) x g matrix with entries over M, calculate the area of the lattice spanned by its columns.
	g := NumberOfColumns(M);
	assert(NumberOfRows(M) eq 2*g);

	// Calulcate the determinants of all g x g minors.
	dets := [];
	for S in Subsets(Set([1..2*g]), g) do
		N := Matrix([M[s] : s in S]);
		Append(~dets, Abs(Determinant(N)));
	end for;
	Sort(~dets);

	// Find the smallest determinant that is not approximately 0.
	ret := -1;
	for d in dets do
		assert( (d le 1E-19) or (d ge 1E-10) );	// Assume all determinants are either almost zero, or distinctively non-zero.
		if (d ge 1E-10) then
			if (ret eq -1) then
				ret := d;
			else	// Check that other determinants are integral multiples.
				ret := RealGCD(d, ret);
				assert(ret ge 1E-10);
				assert(Round(d/ret) - d/ret le 1E-10);
			end if;
		end if;
	end for;
	assert(ret ge 0);

	return ret;
end function;

function GetDifferentials(RS)
	HolDiff := HolomorphicDifferentials(RS);
	_<x,y> := FunctionField(RS);
	return [
		x^(i[1]-1)*y^(i[2]-1) / Evaluate(HolDiff[2], [x,y]) * Differential(x) // divide by x*y! MS 2023-07-26
		: i in HolDiff[1]
	];
end function;

intrinsic CompensationFactor(H::CrvHyp : UseMinimalModel := true) -> RngIntElt
{This function computes the real period. It also gives a list of all primes for which a regular model could not be computed. The real period could be off by powers of these primes.}
	// Calculates the real period

	require(Type(BaseField(H)) eq FldRat) : "H must be defined over the rationals";

	ReturnFudgeFactors := 0;
	if UseMinimalModel then // ReturnFudgeFactors eq 0 then
		Hw := MinimalWeierstrassModel(H);
	else
		Hw := H;
	end if;
	//Hs := SimplifiedModel(Hw);	// Take simplified models, not necessary with use of Neurohr's package
	g := Genus(H);
	c := 1;
	err := [];
	_<x,y> := PolynomialRing(Rationals(), 2);
	RS := RiemannSurface(Evaluate(DefiningPolynomial(Hw), [x,y,1]));
	if ReturnFudgeFactors gt 0 then
		assert(IsSimplifiedModel(H));
		_<xRS,yRS> := FunctionField(RS);
		Diff := [1/2*xRS^i*Differential(xRS)/yRS : i in [0..(g-1)]];
	else
		Diff := GetDifferentials(RS);
	end if;
	vprint User5: "Differential:", Diff;

	BP := BadPrimes(Hw);
	if not(2 in BP) then
		Append(~BP, 2);
	end if;

	if ReturnFudgeFactors gt 0 then
		BP := [ReturnFudgeFactors];
		assert(IsPrime(ReturnFudgeFactors));
	end if;

	for p in BP do
		vprint User1: "Calculating compensation factor for p =", p;
		cf := 1;
		cf, nerr := CompensationFactorAtp(Hw, p, Diff);
		c *:= cf;		// Calculate all compensation factors
		if (nerr ge 2) then
			Append(~err, nerr);
			assert(ReturnFudgeFactors eq 0);
		end if;
		vprint User5: "Compensation factor for p =", p, "is", cf;
	end for;

	return c;
	/*if ReturnFudgeFactors gt 0 then
		return c;
	end if;

	// Some calculations with big period matrix
	M := RS`BigPeriodMatrix;
	MR := [[ 2*Real(M[i][j]) : i in [1..g]] : j in [1..2*g]];
	rp := RealLatticeArea(Matrix(MR));

	return rp*c, err;*/

end intrinsic;

intrinsic RealPeriod(H::CrvHyp : ReturnFudgeFactors:=0, prec := 15)->FldReElt,RngIntElt
{This function computes the real period. It also gives a list of all primes for which a regular model could not be computed. The real period could be off by powers of these primes.}
	// Calculates the real period

	require(Type(BaseField(H)) eq FldRat) : "H must be defined over the rationals";

	if ReturnFudgeFactors eq 0 then
		Hw := MinimalWeierstrassModel(H);
	else
		Hw := H;
	end if;
	//Hs := SimplifiedModel(Hw);	// Take simplified models, not necessary with use of Neurohr's package
	g := Genus(H);
	c := 1;
	err := [];
	_<x,y> := PolynomialRing(Rationals(), 2);
	RS := RiemannSurface(Evaluate(DefiningPolynomial(Hw), [x,y,1]) : Precision := prec);
	if ReturnFudgeFactors gt 0 then
		assert(IsSimplifiedModel(H));
		_<xRS,yRS> := FunctionField(RS);
		Diff := [1/2*xRS^i*Differential(xRS)/yRS : i in [0..(g-1)]];
	else
		Diff := GetDifferentials(RS);
	end if;
	vprint User5: "Differential:", Diff;

	BP := BadPrimes(Hw);
	if not(2 in BP) then
		Append(~BP, 2);
	end if;

	if ReturnFudgeFactors gt 0 then
		BP := [ReturnFudgeFactors];
		assert(IsPrime(ReturnFudgeFactors));
	end if;

	for p in BP do
		vprint User1: "Calculating compensation factor for p =", p;
		cf := 1;
		cf, nerr := CompensationFactorAtp(Hw, p, Diff);
		c *:= cf;		// Calculate all compensation factors
		if (nerr ge 2) then
			Append(~err, nerr);
			assert(ReturnFudgeFactors eq 0);
		end if;
		vprint User5: "Compensation factor for p =", p, "is", cf;
	end for;

	if ReturnFudgeFactors gt 0 then
		return c;
	end if;

	// Some calculations with big period matrix
	M := RS`BigPeriodMatrix;
	MR := [[ 2*Real(M[i][j]) : i in [1..g]] : j in [1..2*g]];
	rp := RealLatticeArea(Matrix(MR));

	return rp*c, err, M, c;

end intrinsic;

// Computes a superset of the bad primes of C. Also used in joint code with David Holmes and Steffen Müller.
function MyBadPrimes(C)
	f := Equation(C);
	RZ<xZ,yZ,zZ> := PolynomialRing(Integers(),3);
	den := LCM([Denominator(c) : c in Coefficients(f)]);
	f := RZ!(den*f);
	fx := Derivative(f, xZ);
	fy := Derivative(f, yZ);
	fz := Derivative(f, zZ);

	NaiveDiscriminant := 1;
	for P in [ [xZ, yZ, 1], [xZ, 1, zZ], [1, yZ, zZ] ] do
		I := Ideal([ Evaluate(g, P) : g in [f, fx, fy, fz]]);
		G := GroebnerBasis(I);
		PotentialDiscriminant := G[#G];
		assert(PotentialDiscriminant in Integers());
		NaiveDiscriminant := LCM(NaiveDiscriminant, PotentialDiscriminant);
	end for;

	return PrimeFactors(Integers()!NaiveDiscriminant);
end function;

intrinsic RealPeriod(C::CrvPln)->FldReElt,RngIntElt
{This function computes the real period. It also gives a list of all primes for which a regular model could not be computed. The real period could be off by powers of these primes.}
	// Calculates the real period

	require(Type(BaseField(C)) eq FldRat) : "C must be defined over the rationals";

	g := Genus(C);
	c := 1;
	err := [];
	_<x,y> := PolynomialRing(Rationals(), 2);
	RS := RiemannSurface(Evaluate(DefiningPolynomial(C), [x,y,1]));
	Diff := GetDifferentials(RS);
	vprint User5: "Differential:", Diff;

	BP := MyBadPrimes(C);
	vprint User5: "Bad primes:", BP;
	if not(2 in BP) then
		Append(~BP, 2);
	end if;

	for p in BP do
		vprint User1: "Calculating compensation factor for p =", p;
		cf := 1;
		cf, nerr := CompensationFactorAtp(C, p, Diff);
		c *:= cf;		// Calculate all compensation factors
		if (nerr ge 2) then
			Append(~err, nerr);
		end if;
		vprint User5: "Compensation factor for p =", p, "is", cf;
	end for;


	// Some calculations with big period matrix
	M := RS`BigPeriodMatrix;
	MR := [[ 2*Real(M[i][j]) : i in [1..g]] : j in [1..2*g]];
	rp := RealLatticeArea(Matrix(MR));

	return rp*c, err;

end intrinsic;
