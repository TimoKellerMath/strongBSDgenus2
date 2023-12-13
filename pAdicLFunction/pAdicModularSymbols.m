
function CombinationOfIntegralBasis(f, S) // f::ModFrmElt
    Kf := CoefficientField(f);
    bas := qIntegralBasis(S, HeckeBound(S) + 1);
    mat := Matrix(Kf, #bas,HeckeBound(S), [[Coefficient(bas[i],j) : j in [1..HeckeBound(S)]] : i in [1..#bas]]);
    alphas, ker := Solution(mat, Vector(Kf, [Coefficient(f, i) : i in [1..HeckeBound(S)]]));
    assert Dimension(ker) eq 0;
    alphas := Eltseq(alphas);
    assert forall{n : n in [1..HeckeBound(S)] | Coefficient(f,n) eq &+[alphas[i] * Coefficient(bas[i], n): i in [1..#alphas]]};
    return alphas;
  end function;
  
  declare attributes ModFrmElt: complex_embeddings, Nterms;
  
  intrinsic PeriodIntegrals(S::ModSym, alphas::SeqEnum, gamma::ModSymElt : prec := 20) -> SeqEnum
  { Compute the period integrals over fs over the element gamma of H_1(X_0(N),Z)[I_f]. }
    g := #alphas;
    assert Dimension(S) in {g, 2*g};
    Nterms := NumberOfFourierCoefficientsForPeriodMatrixOfPrecision(S, prec);
    phi := PeriodMappingModSym(S, prec, Nterms);
    periods := phi(gamma);
    periods_f := [ComplexField(prec) | &+[Conjugate(alphas[i], j) * periods[i]: i in [1..g]] : j in [1..g]];
    return periods_f;
  end intrinsic;
  
  function C_to_Q(x, denom_bound)
    assert Abs(Im(x)) lt 10^(-0.5 * Precision(x));
    // Try to recognize precision from Im(x) \approx 0.
    prec := Im(x) eq 0 select Round(0.8*Precision(x)) else Round(-0.8 * Log(10, Abs(Im(x))));
    x := RealField(prec)!Re(x);
    fx, qualityx := MinimalPolynomial(x, 1); // recognize as elements of \Q
    assert Degree(fx) eq 1;
    xQ := -Coefficients(fx)[1] / Coefficients(fx)[2]; // the unique root of fx
    assert Abs(xQ - x) lt 10^(-0.5 * prec) and Denominator(xQ) le denom_bound;
    return xQ;
  end function;
  
  import "../HeegnerPoint.m": polC_to_polQ;
  
  declare attributes CrvHyp: canonical_periods;
  declare attributes ModFrmElt: canonical_periods, curve, mod_sym, denom_bound,
                                period_integrals,
                                modular_symbols, // Assoc
                                alphas;
  declare attributes ModSym: Sign1Space;
  
  intrinsic CanonicalPeriods(f::ModFrmElt : prec := 20) -> SeqEnum
  { If Jac(C) is modular with newform f, returns Omega_(f^\sigma)^+. }
    assert assigned f`curve;
    C := f`curve;
    if assigned C`canonical_periods then
      return C`canonical_periods;
    end if;
    // compute Omega_J
    Omega_J, err := RealPeriod(C : prec := prec); // TODO: prec
    if err ne [] then 
      printf "WARNING (RealPeriod): err = %o\n", err;
    end if;
    printf "Omega_J = %o\n", Omega_J;
  
    // compute multiples sigma(b) Omega_{f^\sigma}^\pm for some b \in K_f^\times
    if f cmpeq 0 then
      printf "newform must be given!\n";
      assert false;
    end if;
    assert assigned f`mod_sym;
    S := f`mod_sym;
    Kf := CoefficientField(f);
    Zf := Integers(Kf);
  
    den := ideal<Zf | 0>;
    for p in [p : p in PrimesUpTo(2*Level(f)) | not IsDivisibleBy(Level(f), p)] do
      den := den + ideal<Zf | p + 1 - Coefficient(f, p)>;
      if den eq ideal<Zf | 1> then 
        break;
      end if;
    end for;
    cfcpi := ManinConstant(f`curve, f);
    denom_bound := Norm(4^Degree(Kf) * cfcpi * den); // * Discriminant(Zf);
    f`denom_bound := denom_bound;
    //denom_bound := Norm(ideal<Integers(Kf) | [p + 1 - Coefficient(f, p) : p in PrimesUpTo(2*Level(f)) |
    //                    not IsDivisibleBy(Level(f), p)]>);
    printf "bound on denominator = %o\n", denom_bound;
    assert 10^-prec lt denom_bound; // usually prec is enough
  
    alphas := CombinationOfIntegralBasis(f, S);
    f`alphas := alphas;
    gamma := IntegralBasis(S)[1];
  
    bOmega_fs := PeriodIntegrals(S, alphas, gamma : prec := prec);
    printf "phi{f^sigma}(%o) = %o\n", gamma, bOmega_fs;
  
    if Maximum([Abs(period) : period in bOmega_fs]) lt 10^(-0.8 * Precision(bOmega_fs[1])) then
      // TODO: choose a different gamma if result is approximately 0
      error "WARNING: choose a different gamma!";
    end if;
    Omega_fs := [];
    bOmega_fs_plus := &*[Re(bOmega_f) : bOmega_f in bOmega_fs];
    bOmega_fs_minus := &*[Im(bOmega_f) : bOmega_f in bOmega_fs]; // not used at the moment since we don't know Omega_J^-
    printf "Omega_{A_f}^+ = %o\nOmega_{A_f}^- = %o\n", bOmega_fs_plus, bOmega_fs_minus;
  
    b_norm := Omega_J / bOmega_fs_plus;
    printf "found Nm(b) = %o\n", b_norm;
    b_norm := C_to_Q(b_norm, denom_bound);
    printf "in Q: %o\n", b_norm;
    b_is_norm, b := NormEquation(Kf, b_norm);  // b must be a norm from K
    assert b_is_norm;
    b := b[1];
    //print Factorization(Norm(Zf!Numerator(b))), Factorization(Norm(Zf!Denominator(b)));
    printf "using b = %o (unique up to Z[f]^*)\n", b;
    if b eq 0 then 
      error "b = 0";
    end if;
    assert Abs(Norm(b)) eq Abs(b_norm);
    canonical_periods := [Re(bOmega_fs[j]) * Conjugate(b, j : Precision := prec) : j in [1..#bOmega_fs]];
  
    assert Abs(Omega_J - &*canonical_periods) 
              lt 10^-(0.6 * Minimum([Precision(Omega_J), Precision(canonical_periods[1])]));
    C`canonical_periods := canonical_periods;
    f`canonical_periods := canonical_periods;
    return canonical_periods;
  end intrinsic;
  
  intrinsic EvaluateModularSymbol(f::ModFrmElt, alpha::FldRatElt, p::RngIntElt : prec := 20, pAdic_prec := 7) -> SeqEnum
  { Returns the modular symbols of f^sigma integrated from i\infty to alpha. }
    if not assigned f`canonical_periods then
      canonical_periods := CanonicalPeriods(f : prec := prec);
      f`canonical_periods := canonical_periods;
    else
      canonical_periods := f`canonical_periods;
    end if;
  
    if assigned f`modular_symbols then
      flag, modsym := IsDefined(f`modular_symbols, alpha);
      if flag then
        return modsym;
      end if;
    else
      f`period_integrals := AssociativeArray(Rationals());
      f`modular_symbols := AssociativeArray(Rationals());
    end if;
  
    Qf := CoefficientField(f);
    Zf := Integers(Qf);
    require IsInert(p, Zf): "p must be inert in Z[f].";
    Qfp, iQfp := Completion(Qf, ideal<Zf | p> : Precision := pAdic_prec);
    assert assigned f`mod_sym;
    S := f`mod_sym;
    gamma := S!<1, [Cusps() | Infinity(), alpha]>;
    alphas := f`alphas;
    integrals := PeriodIntegrals(S, alphas, gamma : prec := prec);
  
    f`period_integrals[alpha] := integrals;
    Px<x> := PolynomialRing(Parent(canonical_periods[1]));
    polC := &*[Px| x - Re(integrals[i]) / canonical_periods[i] : i in [1..#integrals]]; 
    flag, polQ := polC_to_polQ(polC);
    assert flag;
    //assert forall{a : i -> a in Coefficients(polQ) | a eq 0 or IsDivisibleBy(f`denom_bound^Degree(Kf), Denominator(a))};
    K := SplittingField(polQ);
    OK := Integers(K);
    polK := PolynomialRing(K)!polQ;
    modular_symbolsK := &cat[[beta[1] : i in [1..beta[2]]] : beta in Roots(polK)];
    assert #modular_symbolsK eq Degree(polQ);
    Kp, iKp := Completion(K, ideal<OK | p> : Precision := pAdic_prec); // assumes p inert
    function closest(real, values)
        differences := [RealField(prec)| Abs(real - Conjugate(value, 1)) : value in values];
        min, i := Minimum(differences);
        assert Abs(min) lt 10^-(prec - 5);
        return values[i];
    end function;
    modular_symbolsK := [closest(Re(integrals[i]) / canonical_periods[i], modular_symbolsK) : i in [1..#modular_symbolsK]];
    if Degree(Kp) eq 1 then // values of modular symbols are in Z[f]
        f`modular_symbols[alpha] := [iQfp(phii)@@iQfp : phii in modular_symbolsK];
    else
        assert IsIsomorphic(Kp, Qfp);
        function Kp_to_Qfp(x)
            minpol := PolynomialRing(Qfp)!MinimalPolynomial(x);
            return Roots(minpol)[1,1]; // note: choice of root!
        end function;
        function pAdicallyClosest(x, modular_symbolsK) // x in Qf
          differences := [x - Kp_to_Qfp(value)@@iQfp : value in modular_symbolsK];
          valuations := [Valuation(difference, ideal<Zf | p>) : difference in differences];
          max, i := Maximum(valuations);
          assert max gt 0;
          return x - differences[i];
        end function;
        modular_symbolsKpalpha := [iKp(phii) : phii in modular_symbolsK];
        f`modular_symbols[alpha] := [pAdicallyClosest(Kp_to_Qfp(modular_symbolsKpalpha[i])@@iQfp, modular_symbolsK) : i in [1..#modular_symbolsKpalpha]];
    end if;
    //printf "phi(%o) = %o\n", alpha, f`modular_symbols[alpha];
    return f`modular_symbols[alpha];
  end intrinsic;
  