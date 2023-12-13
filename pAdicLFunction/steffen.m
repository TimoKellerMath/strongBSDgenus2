SetDebugOnError(true);
AttachSpec("p_adic_L_function.spec");
SetVerbose("pAdicLFunction", 2);
SetVerbose("ManinConstant", 2);
//SetVerbose("ModularSymbols", true);

//import "p_adic_L_function.magma": pAdicLFunctionCoefficient, precompute_basic_integrals, loggam_binom;
//import "modsym.magma": eval_modsym_pt, eval_modsym_unimodpath;
//import "../EvaluateModularSymbols.m": CombinationOfIntegralBasis;

/*
import "321.2.a.a.m": MakeNewformModFrm_321_2_a_a, MakeNewformModSym_321_2_a_a;
N := 3 * 107;
f := MakeNewformModFrm_321_2_a_a();
S := MakeNewformModSym_321_2_a_a();
Splus := MakeNewformModSym_321_2_a_a(: sign := +1);
R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(R![8, -5, -14, 2, 6, 0, -1], R![1, 1, 0, 1]);
p := 3;
degree := 2;
precision := 2;
prec := 10;*/

import "145.2.a.b.m": MakeNewformModFrm_145_2_a_b, MakeNewformModSym_145_2_a_b;
N := 145;
f := MakeNewformModFrm_145_2_a_b();
S := MakeNewformModSym_145_2_a_b(: sign := 0);
R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(20*x^5 - 19*x^4 + 118*x^3 - 169*x^2 + 50*x + 25);
p := 5;
degree := 2;
precision := 10; // scaling exponent = 3 => exact up to precision 3
prec := 20;

C := SimplifiedModel(C);
f`curve := C;
f`mod_sym := S;
canonical_periods := CanonicalPeriods(f : prec := prec);
f`canonical_periods := canonical_periods;

/*//Splus := MakeNewformModSym_145_2_a_b(: sign := +1);
Splusdual := DualVectorSpace(Splus);

//alphas := CombinationOfIntegralBasis(f,Splus);

modular_path := function(r, S)
	return Vector(Rationals(), Eltseq(S!<1, [Cusps()| Infinity(), r]>));
end function;

for r in [1/a : a in [1..100]] do
	phifrsMagma := [InnerProduct(Splusdual.i, modular_path(r, Splus)) : i in [1..Dimension(Splusdual)]];
	phifr := &+[f`alphas[i] * phifrsMagma[i] : i in [1..#phifrsMagma]];
	phifrsEval := EvaluateModularSymbol(f, r : prec := prec);
	//printf "r = %o: Magma: %o (sum of %o), Eval: %o\n", r, &+[f`alphas[i] * phifrs[i] : i in [1..#phifrs]], phifrs, EvaluateModularSymbol(f, r : prec := prec);
	printf "r = %o: %o\n", r, [phifrsEval[i] eq 0 select 0 else phifrsEval[i]/phifr : i in [1..#phifrsEval]];
end for;*/


SetLogFile("steffen.log");

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