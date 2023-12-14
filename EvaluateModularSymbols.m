
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

function C_to_K(x, K, denom_bound)
  minpol := MinimalPolynomial(x, Degree(K));
  Kx := NumberField(minpol : DoLinearExtension);
  flag, m := IsSubfield(Kx, K);
  if not flag then 
    if Precision(x) lt 5 then
      error "couldn't recognize x as element of K";
    end if;
    CC := ComplexField(Precision(x) - 1); // recompute with less precision
    return $$(CC!x, K, denom_bound);
  end if;
  xK := m(Kx.1); // well-defined only up to conjugacy
  auts := Automorphisms(K);
  sigma := InfinitePlaces(K)[1]; // choose the first complex embedding
  min, pos := Minimum([Abs(x - Evaluate(aut(xK), sigma)) : aut in auts]);
  assert min lt 10^-(0.7 * Precision(x)) and Denominator(Norm(xK)) le denom_bound;
  return xK@auts[pos];
end function;

import "HeegnerPoint.m": polC_to_polQ;

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
  Qf := CoefficientField(f);
  Zf := Integers(Qf);

  // compute Omega_{A_f/Q}
  N := Level(S);
  bpmseq, alphaseq, Mseq := DiagramData(C, N);
  // bpmseq = [bpmAfdual, bpmAf, bpmJ]
  // alphaseq = [Id, alpha_pi_Z, alpha_gen, alpha_Z],
  // Mseq = [imat, M_pi, M_gen, M_round]
  flag := true;
  try
    corr := CompensationFactor(C);
  catch e
    printf "ERROR in CompensationFactor: %o\n", e;
    printf "using corr = 1 instead.\n";
    corr := 1;
    flag := false;
  end try;
  // compensation factor involves a factor 4 from changing to a minimal model
  // when given model is not minimal -- correct for this
  if IspMinimal(C, 2) then corr /:= 4; end if;
  cfcpi := corr*Abs(Determinant(alphaseq[2]));
  Mpi := Mseq[2];
  Mtau := ComplexConjugationOnHomology(bpmseq[3]);
  _, _, kerpiR, cokerpiR := KerAndCokerOfPiR(Mpi, Mtau); // #ker and #coker of \pi_R^K
  corr_period := cfcpi * #cokerpiR / #kerpiR;
  printf "dividing Omega_J by %o.\n", corr_period;
  Omega_J := Omega_J / corr_period;

  den := ideal<Zf | 0>;
  for p in [p : p in PrimesUpTo(2*Level(f)) | not IsDivisibleBy(Level(f), p)] do
    den := den + ideal<Zf | p + 1 - Coefficient(f, p)>;
    if den eq ideal<Zf | 1> then 
      break;
    end if;
  end for;
  denom_bound := Norm(4^Degree(Qf) * cfcpi * den);
  f`denom_bound := denom_bound;
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
  b_is_norm, b := NormEquation(Qf, b_norm);  // b must be a norm from K
  assert b_is_norm;
  b := b[1];
  printf "b = %o\n", b;
  num_bad_ps   := {Integers()| p[1] : p in Factorization(Norm(Zf!Numerator(b))) | not IsInert(p[1], Zf)};
  denom_bad_ps := {Integers()| p[1] : p in Factorization(Norm(Zf!Denominator(b)))| not IsInert(p[1], Zf)};
  for p in num_bad_ps meet denom_bad_ps do 
    frps := Decomposition(Zf, p);
    if #frps eq 2 then // norms of numerator and denominator cancel
      pis := [];
      for frp in frps do 
        flag, pi := IsPrincipal(frp[1]);
        assert flag;
        Append(~pis, pi);
      end for;
      adapt := Minimum(Valuation(b, frps[1][1]), -Valuation(b, frps[2][1]));
      b := b / (pis[1]^adapt / pis[2]^adapt);
    end if;
  end for;
  printf "using b = %o (unique up to Z[f]_p^*)\n", b;
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

intrinsic EvaluateModularSymbol(f::ModFrmElt, alpha::FldRatElt : prec := 20) -> SeqEnum
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

  Kf := CoefficientField(f);
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
  assert forall{a : i -> a in Coefficients(polQ) | a eq 0 or IsDivisibleBy(f`denom_bound^Degree(Kf), Denominator(a))};
  polZf := PolynomialRing(Kf)!polQ;
  modular_symbols := &cat[[beta[1] : i in [1..beta[2]]] : beta in Roots(polZf)];
  assert #modular_symbols eq Degree(Kf);
  function closest(real, values)
    differences := [RealField(prec)| Abs(real - Conjugate(value, 1)) : value in values];
    min, i := Minimum(differences);
    assert Abs(min) lt 10^-(prec - 5);
    return values[i];
  end function;
  f`modular_symbols[alpha] := [closest(Re(integrals[i]) / canonical_periods[i], modular_symbols) : i in [1..#modular_symbols]];
  return modular_symbols;
end intrinsic;
