SetDebugOnError(true);
AttachSpec("p_adic_L_function.spec");
SetVerbose("pAdicLFunction", 2);
//SetVerbose("ModularSymbols", true);

import "p_adic_L_function.magma": pAdicLFunctionCoefficient, precompute_basic_integrals, loggam_binom;
import "modsym.magma": eval_modsym_pt, eval_modsym_unimodpath;


/*import "321.2.a.a.m": MakeNewformModFrm_321_2_a_a, MakeNewformModSym_321_2_a_a;
N := 3 * 107;
f := MakeNewformModFrm_321_2_a_a();
S := MakeNewformModSym_321_2_a_a();
R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(R![8, -5, -14, 2, 6, 0, -1], R![1, 1, 0, 1]);
p := 3;
degree := 2;
precision := 2;
prec := 10;*/

import "188.2.a.a.m": MakeNewformModFrm_188_2_a_a, MakeNewformModSym_188_2_a_a;
N := 188;
f := MakeNewformModFrm_188_2_a_a();
S := MakeNewformModSym_188_2_a_a(: sign := 0);
R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(R![1, -2, 1, 1, -1, 1]);
p := 3;
degree := 2;
precision := 6; // scaling exponent = 3 => exact up to precision M - 3 - 1 = 2
prec := 20;
SetLogFile("188.log");

/*
import "3200.2.a.bn.m": MakeNewformModFrm_3200_2_a_bn, MakeNewformModSym_3200_2_a_bn;
N := 3200;
f := MakeNewformModFrm_3200_2_a_bn();
S := MakeNewformModSym_3200_2_a_bn(: sign := 0);
R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(-10*x^6 + 100*x^5 - 320*x^4 + 400*x^3 - 380*x^2 + 200*x - 40);
p := 7;
degree := 1;
precision := 5;
prec := 20;*/

/*
SetSeed(3926386080);
import "23.2.a.a.m": MakeNewformModFrm_23_2_a_a, MakeNewformModSym_23_2_a_a;
N := 23;
f := MakeNewformModFrm_23_2_a_a();
S := MakeNewformModSym_23_2_a_a(: sign := 0);
//S1 := MakeNewformModSym_23_2_a_a(: sign := +1);
//S`Sign1Space := S1;
R<x> := PolynomialRing(Rationals());
C := X0NQuotient(23, []);
p := 11;
degree := 1;
precision := 5;
prec := 10;*/

f`mod_sym := S;
printf "Computing L_p(f,T) with f = %o of conductor %o.\n", f, N;

C := SimplifiedModel(C);
f`curve := C;
canonical_periods := CanonicalPeriods(f : prec := prec);
f`canonical_periods := canonical_periods;

sign := +1;
print "Computing the first", precision, "moments.\n";

verbose := true;

if degree eq 2 then
	for Conj, j in [1..2] do
		printf "Conj = %o, j = %o:\n", Conj, j;
		time Phi, phi, alpha, scaling_exponent := form_Up_eigensymbol(f, p, sign, precision : Conj := Conj, j := j, verbose := verbose);
		Lp := pAdicLFunction(Phi, alpha, scaling_exponent);
		printf "L_p(f,T) = ";
		PrintLFunction(Lp);
		printf "\n\n";
	end for;
elif degree eq 1 then
	error "For split primes use Sage.\n";
end if;