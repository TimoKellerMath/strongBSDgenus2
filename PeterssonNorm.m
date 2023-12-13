// Compute Petersson norm and heights via Gross-Zagier

declare verbose PeterssonNorm, 2;

intrinsic MinimalQuadraticTwist(f::ModFrmElt) -> RngIntElt, SeqEnum, ModFrm, GrpDrchElt
{ Determine the quadratic twist of the newform f of minimal level.
  This function returns the level of the minimal twist, a sequence of pairs
  consisting of the prime divisors of N and the corresponding coefficient of the minimal twist,
  the associated modular symbols space and the twisting character. }
  // Determine multiplicative bound for conductor of twisting character
  N := Level(f);
  fN := Factorization(N);
  D := &*[Integers()| e[1]^(e[2] div 2) : e in fN];
  // Determine the nontrivial quadratic characters of conductor dividing D.
  DG := DirichletGroup(D);
  chars := [ch : ch in Elements(DG) | ch ne DG!1];
  badpseq := [e[1] : e in fN];
  badp := {e[1] : e in fN};
  Kf := BaseField(f);
  pmax := NextPrime(Max(badp));
  while not IsIsomorphic(sub<Kf | Coefficient(f, pmax)>, Kf) do
    pmax := NextPrime(pmax);
  end while;
  // set up modular symbols space
  M := ModularSymbols(N);
  Nmin := N; // current minimal level
  cofs := [<p, Coefficient(f, p)> : p in badpseq];
  Mmin := ModularSymbols(f);
  chmin := DG!1;
  // loop over characters
  for ch in chars do
    Mch := Kernel([<p, MinimalPolynomial(ch(p)*Coefficient(f, p))>
                    : p in PrimesUpTo(HeckeBound(M)) | p notin badp], M);
    Mchdec := NewformDecomposition(Mch);
    if not IsEmpty(Mchdec) then
      assert #Mchdec eq 1;
      Mchnew := AssociatedNewSpace(Mchdec[1]);
      Nch := Level(Mchnew);
      if Nch lt Nmin then
        // found lower level: update info
        Nmin := Nch;
        ser := Eigenform(Mchnew, pmax+1);
        Ks := Parent(Coefficient(ser, pmax));
        // identify coefficient fields correctly
        flag, iso := IsIsomorphic(Ks, Kf); assert flag;
        if iso(Coefficient(ser, pmax)) eq ch(pmax)*Coefficient(f, pmax) then
          cofs := [<p, iso(Coefficient(ser, p))> : p in badpseq];
        else
          // find correct isomorphism
          isos := [iso<Ks -> Kf | r[1]> : r in Roots(MinimalPolynomial(Ks.1), Kf)];
          isos := [m : m in isos | m(Coefficient(ser, pmax)) eq ch(pmax)*Coefficient(f, pmax)];
          assert #isos eq 1;
          iso := isos[1];
          cofs := [<p, iso(Coefficient(ser, p))> : p in badpseq];
        end if;
        Mmin := Mchnew;
        chmin := ch;
      end if;
    end if;
  end for;
  return Nmin, cofs, Mmin, chmin;
end intrinsic;

intrinsic MinimalQuadraticTwistForm(f::ModFrmElt) -> ModFrmElt, Map
{ Returns a quadratic twist of f of minimal level and the isomorphism of coefficient
  fields that maps the coefficients of the returned form to ±the coefficients of f. }
  N := Level(f);
  Kf := BaseField(f);
  Nmin, cofs, Mmin, ch := MinimalQuadraticTwist(f);
  // Identify the correct form
  if Nmin lt Level(f) then
    nf := [* e[1] : e in Newforms(CuspForms(Nmin)) | #e eq Degree(BaseField(f)) *];
    for f1 in nf do
      K := BaseField(f1);
      flag, iso := IsIsomorphic(K, Kf);
      if flag then
        isos := [iso<K -> Kf | r[1]> : r in Roots(MinimalPolynomial(K.1), Kf)];
        for p in [p : p in PrimesUpTo(HeckeBound(Mmin)) | not IsDivisibleBy(N, p)] do
          isos := [i : i in isos | i(Coefficient(f1, p)) eq ch(p)*Coefficient(f, p)];
        end for;
        if #isos eq 1 then
          return f1, isos[1];
        end if;
      end if;
    end for;
    error "minimal quadratic twist could not be identified";
  else
    return f, iso<Kf -> Kf | Kf.1>;
  end if;
end intrinsic;

MyPrec := Precision; // to be able to call "Precision" when there is a local variable of the same name

function ToSeries(c,d)
  B := Type(c) in [RngUPolElt,FldFunRatUElt,RngSerPowElt,RngSerLaurElt]
         select BaseRing(Parent(c))
         else Parent(c);
  return PowerSeriesRing(B, 1+d)!c;
end function;

function CoefficientsFromLocalFactors(f, N, R)
  // Compute the vector of the first N coefficients of an L-series
  // from the local factors provided by f = func<p, d | ...>.
  // R is the coefficient ring.
  V := [R| 1 : k in [1..N]];
  for p in PrimesUpTo(N) do
    d := Ilog(p,N);
    S := 1/ToSeries(f(p, d), d);
    A:= [Coefficient(S, j) : j in [1..d]];
    pk := 1;
    for k in [1..d] do
      pk *:= p;
      for j in [1..N div pk] do
        if j mod p ne 0 then
          V[j*pk] *:= A[k];
        end if;
      end for;
    end for;
  end for;
  return V;
end function;

function ChangeSign(V, p)
  // Replace Euler factor 1-p*x by 1+p*x:
  // Change the sign of all coefficients whose p-adic valuation is odd.
  R := Universe(V);
  N := #V;
  d := Ilog(p,N);
  pk := p;
  for k in [1..d by 2] do
    for j in [1..N div pk] do
      if j mod p ne 0 then
        V[j*pk] := -V[j*pk];
      end if;
    end for;
    pk *:= p^2;
  end for;
  return V;
end function;

intrinsic SymmetricSquareLSeries(f::ModFrmElt : Precision := MyPrec(GetDefaultRealField()))
  -> SeqEnum[LSer], RngElt
{ Given a weight-2 newform f for Gamma_0(N), produce the symmetric square
  L-series associated to the various complex embeddings of f with the given precision.
  The second reutrn value is the "fudge factor" the value at 2 has to be multiplied
  by to obtain the value of the "imprimitive" symmetric square L-function. }

  require Weight(f) eq 2: "only implemented for weight k = 2 so far.";
  R := BaseField(f);
  P<x> := PolynomialRing(R : Global := false);
  N := Level(f);
  fN := Factorization(N);

  // Determine minimal quadratic twist (has same symmetric square L-series)
  fmin, iso := MinimalQuadraticTwistForm(f);
  Nmin := Level(fmin);
  fNmin := Factorization(Nmin);
  vprintf PeterssonNorm, 1: "Level of minimal quadratic twist is %o\n", Nmin;

  // Worst case conductor
  maxcond := &*[Integers()|e[1]^(e[2] le 2 select 2 else 2*e[2]-1) : e in fNmin];
  // Tame part of conductor
  tamecond := &*[Integers()| e[1]^2 : e in fNmin | e[2] le 2];
  // Number of coefficients needed in worst case
  numcof := LCfRequired(LSeries(3, [0,0,1], maxcond, 0) : Precision := Precision);
  numcof := Max(numcof, Max([e[1] : e in fN]));
  vprintf PeterssonNorm, 1: "Need %o coefficients\n", numcof;

  //   compute the relevant coefficients of fmin
  cofs := Coefficients(qExpansion(fmin, numcof + 1));
  vprintf PeterssonNorm, 2: " ... computed coefficients of f_min\n";
  // trailing zeros are removed when applying Coefficients() :-(
  cofs cat:= [R| 0 : n in [#cofs+1..numcof]];
  cofs := [iso(c) : c in cofs];

  // Determine possible bad Euler factors and conductor exponents
  cf := func<p, d | not IsDivisibleBy(Nmin, p)
                      select (1 - p*x)*((1 + p*x)^2 - cofs[p]^2*x)
                      else Valuation(Nmin, p) eq 1 select 1 - x
                      else Valuation(Nmin, p) eq 2 select 1 - p*x // first choice, can also be 1 + p*x
                      else P!1>;
  // Compute coefficients in R for the first choice of Euler factors
  cvec := CoefficientsFromLocalFactors(cf, numcof, R);
  cvecseq := [<tamecond, cvec>];
  // Now extend to all possible pairs <conductor, coefficients>.
  for e in fNmin do
    if e[2] eq 2 then
      // update coefficients in second choice with the signs corresponding to 1 + p*x
      cvecseq := &cat[[pair, <pair[1], ChangeSign(pair[2], e[1])>] : pair in cvecseq];
    elif e[2] gt 2 then
      // update possible conductor values
      cvecseq := &cat[[<pair[1]*e[1]^np, pair[2]> : np in [4..2*e[2]-1]] : pair in cvecseq];
    end if;
  end for;
  vprintf PeterssonNorm, 2: " ... computed %o candidate coefficient sequences\n", #cvecseq;

  // Find out which combination of Euler factors and conductor is correct.
  // We use the first of the complex embeddings; one choice must work for all.
  Lsseq := [LSeries(3, [0,0,1], pair[1], [Conjugate(c, 1 : Precision := Precision + 5) : c in pair[2]]
                     : Sign := 1, Precision := Precision)
             : pair in cvecseq];
  testvals := [Abs(CFENew(L)) : L in Lsseq];
  min, pos := Min(testvals);
  vprintf PeterssonNorm, 2: "minimal test value = %o\n", ChangePrecision(testvals[pos], 6);
  // Check that functional equation is numerically satisfied for the best choice
  // and is not satisfied for all other choices.
  assert min lt 10^(5-Precision)
          and forall{i : i in [1..#testvals] | i eq pos or testvals[i] gt 10^(-0.3*Precision)};
  cond, cvec := Explode(cvecseq[pos]);
  result := [Lsseq[pos]]
              cat [LSeries(3, [0,0,1], cond, [Conjugate(c, j : Precision := Precision + 5) : c in cvec]
                            : Sign := 1, Precision := Precision)
                    : j in [2..Degree(R)]];
  // Check the functional equation for the remaining series.
  assert forall{L : L in result[2..#result] | Abs(CFENew(L)) lt 10^(5-Precision)};

  // Compute the fudge factor.
  C := R!1;
  for pair in fN do
    l, e := Explode(pair);
    if e gt 1 then
      // if e <= 1, then C_l = 1
      vlNmin := Valuation(Nmin, l);
      if vlNmin eq 0 then // Lemma 3.5.4 (1)
        C *:= (l-1)/((l+1)^2 - l*cofs[l]^2)/l^3;
      elif vlNmin eq 1 then // Lemma 3.5.4 (2)
        C *:= 1 - 1/l^2;
      elif vlNmin eq 2 then // Lemma 3.5.4 (3)
        C *:= 1 - cvec[l]/l^2;
      end if; // no correction factor when v_l(Nmin) > 2; see Lemma 3.5.4 (4)
    end if;
  end for;
  vprintf PeterssonNorm, 2: "fudge factor is %o\n", C;

  return result, C;
end intrinsic;

intrinsic PeterssonNorm(f::ModFrmElt : Precision := MyPrec(GetDefaultRealField())) -> FldReElt
{ Return the Petersson norms of the conjugates of the newform f. }
  require Weight(f) eq 2: "only implemented for weight k = 2 so far.";
  N := Level(f);
  // Get symmetric square L-functions and fudge factor
  Ls, C := SymmetricSquareLSeries(f : Precision := Precision);
  c := N/(8 * Pi(RealField(Precision))^3);
  return [c * Conjugate(C, j : Precision := Precision) * Evaluate(Ls[j], 2) : j in [1..#Ls]];
end intrinsic;

intrinsic FirstDerivativeOverHeegnerField(f::ModFrmElt, D::RngIntElt, IsZeroAt1::BoolElt
                                           : Precision := MyPrec(RealField())) -> SeqEnum
{ Computes L'(f^sigma/Q(Sqrt(D)), 1) for all complex embeddings sigma of the coefficient
  field of f. We assume that L(f, s) has order of vanishing 0 or 1 at s=1, as specified
  by IsZeroAt1 and that L(f/Q(sqrt(D)), s) vanishes to first order at s=1. }

  N := Level(f);
  K := BaseField(f);
  d := Degree(K);
  // The quadratic character we twist by
  chi_K := BaseChange(KroneckerCharacter(D), Rationals());
  // The sign of the functional equation for the twisted L-series = opposite to sign of original
  sign := IsZeroAt1 select 1 else -1;

  // Set up L-series manually:
  //   determine number of coefficients needed
  n1 := LCfRequired(LSeries(2, [0,1], N, 0 : Sign := -sign, Precision := Precision));
  n2 := LCfRequired(LSeries(2, [0,1], N*D^2, 0 : Sign := sign, Precision := Precision));
  //   compute the relevant coefficients of f
  cofs := Coefficients(qExpansion(f, n2 + 1));
  // trailing zeros are removed when applying Coefficients :-(
  cofs cat:= [K| 0 : n in [#cofs+1..n2]];

  // Construct the L-series of f^sigma and the twisted version
  Lsp := [<LSeries(2, [0,1], N,
                   [Conjugate(c, j : Precision := Precision+5) : c in cofs[1..n1]]
                    : Sign := -sign, Precision := Precision),
           LSeries(2, [0,1], N*D^2,
                   [chi_K(n)*Conjugate(cofs[n], j : Precision := Precision+5) : n in [1..n2]]
                    : Sign := sign, Precision := Precision)>
            : j in [1..d]];

  vprintf HeegnerPoint, 2: "required coefficients for twisted L-series: %o\n", n2;
  vprintf HeegnerPoint, 2: "Evaluating L'(f/K, 1) to precision %o ...\n", Precision;
  if IsZeroAt1 then
    // L-rank 1
    return [Evaluate(Lp[1], 1 : Derivative := 1, Leading) * Evaluate(Lp[2], 1) : Lp in Lsp];
  else
    // L-rank 0
    return [Evaluate(Lp[1], 1) * Evaluate(Lp[2], 1 : Derivative := 1, Leading) : Lp in Lsp];
  end if;
end intrinsic;

intrinsic HeegnerHeightsAfdual(f::ModFrmElt, D::RngIntElt, LIsZeroAt1::BoolElt
                                : Precision := MyPrec(RealField())) -> SeqEnum
{ For a newform and a Heegner discriminant D,
  return the heights of the isotypic components pf the Heegner point y_K in A_f^v. }

//   // MS, 2023-10-09: The following does not work as expected:
//   //                 ModularSymbols(f) gives the _full_ modular symbols space for Gamma_0(N)!
//   LIsZeroAt1 := LRatio(ModularSymbols(f), 1) eq 0;
  L_prime_f_K_1s := FirstDerivativeOverHeegnerField(f, D, LIsZeroAt1 : Precision := Precision);
  // u_K = #O_K^\times/\Z^\times
  if D lt -4 then
    u_K := 1;
  elif D eq -4 then
    u_K := 2;
  elif D eq -3 then
    u_K := 3;
  end if;
  // See Theorem 3.6.1
  f_norms := PeterssonNorm(f : Precision := Precision);
  c := u_K^2 * Sqrt(RealField(Precision)!-D) / (16 * Pi(RealField(Precision))^2);
  return [c * L_prime_f_K_1s[i] / f_norms[i] : i in [1..#f_norms]];
end intrinsic;

intrinsic CheckHeegnerHeight(y_K::JacHypPt, alpha::FldNumElt, f::ModFrmElt, LIsZeroAt1::BoolElt
                              : Precision := MyPrec(RealField()))
  -> FldReElt, SeqEnum[FldReElt], FldReElt
{ For a Heegner point y_K in J(K), verify that the height agrees with the Gross-Zagier formula.
  Returns (1) the normalized canonical height of y_K; (2) the sequence of heights of the
  various sigma-components of the Heegner point on A_f^v; (3) the distance from the
  height of y_K to the appropriate linear combination of these heights. }

  JK := Parent(y_K);
  K := BaseField(JK);
  D := Discriminant(Integers(K));
  // Compute the Gross-Zagier heights on A_f^v.
  Afhts := HeegnerHeightsAfdual(f, D, LIsZeroAt1 : Precision := Precision);
  // Get the canonical height of y_K.
  hty := HeightOnJK(y_K : Precision := Precision);
  // Take linear combination with the (real) conjugates of alpha.
  ass := ChangeUniverse(Conjugates(alpha), Universe(Afhts));
  assert #ass eq #Afhts;
  lc := &+[ass[j]*Afhts[j] : j in [1..#ass]];
  return hty, Afhts, Abs(lc - hty);
end intrinsic;

/*
// This requires that the database is loaded
procedure check(idx : prec := Precision(RealField()))
  e := DB[idx];
  C := e`C; N := e`N; D := e`H_discs[1];
  y_K, kernel_bound, LIsZeroAt1, M, discA, discJ := HeegnerPoint(C, N, D);
  bpms, alphas, Ms, ainO, JC, f, isom := DiagramData(C, N);
  alp := isom(ainO);
  hty, hts, err := CheckHeegnerHeight(y_K[1], alp, f, LIsZeroAt1 : Precision := prec);
  printf "\n=========================================================\n";
  printf "index = %o: N = %o, D = %o\n", idx, N, D;
  printf "y_K = %o\n", y_K;
  printf "h(y_K) = %o\nerror = %o\n", hty, err;
  printf "=========================================================\n";
end procedure;
*/
