declare verbose HeegnerPoint, 4;

// declare attributes JacHyp: D_K, h_y_K, y_K;
// declare attributes ModFrmElt: LIsZeroAt1, L_prime_f_K_1s;
declare attributes CrvHyp: Snew, newforms, DiagramData; //LIsZeroAt1, L_prime_f_K_1s,

MyPrec := Precision;

//==========================================================================

// Compute the big period matrix of A_f associated to S_2(f, Z) and an
// integral homology basis.

pi := Pi(RealField(100));

// Return N such that
//   sum_{n >= N} n exp(tau * n) < err  with  tau < 0
// We use that the l.h.s. is   exp(tau*N) * (N/(1 - exp(tau)) + exp(tau)/(1 - exp(tau))^2) .
// So we need that (with z := 1 - exp(tau))
//   exp(tau*N) * (N * z + (1-z)) = exp(tau*N + log(N*z + 1-z)) < err * z^2
// We can bound  log(N*z + 1 - z) = log(1 + (N-1)*z) <= (N-1)*z,  so it suffices to have
//   exp(N * (tau + z)) < err * z^2 * exp(z)  <==>  N < (log(err * z^2) + z)/(tau + z)
function PrecisionForError(err, tau)
  z := 1 - Exp(tau);
  // Implement binary search to get optimal bound
  // Nu is the upper bound coming from the argument above
  Nu := Ceiling((Log(err * z^2) + z) / (tau + z));
  // We want the smalles N such that test(N) holds
  test := func<N | Exp(tau*N) * (N*z + 1-z) lt err*z^2>;
  // Find some Nl such that test(Nl) does not hold
  Nl := Nu;
  repeat
    Nl := Nl div 2;
  until not test(Nl);
  // No do binary search
  while Nl lt Nu-1 do
    N := (Nl + Nu) div 2;
    if test(N) then
      Nu := N;
    else
      Nl := N;
    end if;
  end while;
  assert test(Nu) and not test(Nu-1);
  return Nu;
end function;

function IsEvenRank(Snew)
  AL := AtkinLehner(Snew, Level(Snew));
  if AL eq Parent(AL)!-1 then
    return true;
  elif AL eq Parent(AL)!1 then
    return false;
  else
    error "Atkin-Lehner operator on modular symbols space is not ±1";
  end if;
end function;

intrinsic NumberOfFourierCoefficientsForPeriodMatrixOfPrecision(Snew::ModSym, prec::RngIntElt) -> RngIntElt
{ Given a newform space, compute the number of Fourier coefficients needed to compute its period matrix up to precision prec. }
  _ := PeriodMapping(Snew, 50); // compute Snew`PeriodGens
  //printf "Snew`PeriodGens =\n%o\n", Snew`PeriodGens;
  d_max := Max([Pg[2][4] : Pg in Snew`PeriodGens]); // Pg[2][4] = d
  //printf "d_max = %o\n", d_max; // d_max depends on the random seed
  tau := -2 * pi / Sqrt(Level(Snew));
  err := 0.1^(prec + 3);
  // make sum_{n >= N1}|eps - 1||a_n(f)| * exp(-2pi * n/Sqrt(N)) < err
  // use |a_n(f)| <= sqrt(3)n (see Stein BSD paper with correction factor sqrt(3))
  N1 := IsEvenRank(Snew) select PrecisionForError(err, tau) else 0;
    // eps = + 1 => (1 - eps)... = 0 because L(f,1) = 0
  // make sum_{n >= N2}|a_n(f)|exp(-2pi * n/(d * Sqrt(N)) * (... <= 2)) < err
  N2 := PrecisionForError(err, tau/d_max);
  return Max(N1, N2);
end intrinsic;

// Compute the big period matrix of a ModularAbelianVariety or a ModularSymbolsSpace
// to given precision.
intrinsic BigPeriodMatrix(Snew::ModSym, prec::RngIntElt) -> Mtrx
{ Compute the big period matrix of a modular symbols space. }
  Nterms := NumberOfFourierCoefficientsForPeriodMatrixOfPrecision(Snew, prec);
  vprintf HeegnerPoint, 2: "Computing %o terms of the Fourier expansion for"*
                           " the period matrix of A_f of precision %o ...\n",
                           Nterms, prec;
  oldprec := Precision(RealField());
  try
    SetDefaultRealFieldPrecision(prec);
    result := Transpose(Matrix(Periods(Snew, Nterms)));
  catch e
    SetDefaultRealFieldPrecision(oldprec);
    error e;
  end try;
  SetDefaultRealFieldPrecision(oldprec);
  return result;
end intrinsic;

intrinsic BigPeriodMatrix(A::ModAbVar, prec::RngIntElt) -> Mtrx
{ Compute the big period matrix of a modular abelian variety to the given precision. }
  // convert to modular symbols space
  seq := ModularSymbols(A);
  assert #seq eq 1;
  Nterms := NumberOfFourierCoefficientsForPeriodMatrixOfPrecision(seq[1], prec);
  vprintf HeegnerPoint, 2: "Computing %o terms of the Fourier expansion for"*
                           " the period matrix of A_f of precision %o ...\n",
                           Nterms, prec;
  oldprec := Precision(RealField());
  try
    SetDefaultRealFieldPrecision(prec);
    result := Transpose(Matrix(Periods(A, Nterms)));
  catch e
    SetDefaultRealFieldPrecision(oldprec);
    error e;
  end try;
  SetDefaultRealFieldPrecision(oldprec);
  return result;
end intrinsic;

//==========================================================================

// Recognize numerical points on the analytic Jacobian as Q- or K-rational points.

function RecognizeRationalElement(x)
  //if Type(x) in {RngIntElt, FldRatElt} then
  //    return x;
  //end if;
  assert Abs(Im(x)) lt 10^(-0.5 * Precision(x));
  // Try to recognize precision from Im(x) \approx 0.
  prec := Round(0.8*Precision(x));
  if Im(x) ne 0 then
    prec := Min(prec, Round(-0.8 * Log(10, Abs(Im(x)))));
  end if;
  x := RealField(prec)!Re(x);
  fx := MinimalPolynomial(x, 1); // recognize as elements of \Q
  assert Degree(fx) eq 1;
  xQ := -Coefficient(fx, 0) / Coefficient(fx, 1); // the unique root of fx
  assert Abs(xQ - x) lt 10^(-0.5 * prec);
  return xQ;
end function;

// Given a list of numerical points on a hyperelliptic curve y² = pol(x) of genus g,
// try to recognize the Mumford representation of the rational divisor D
// that is the formal sum of the points.
// Returns two polynomials a and b and the degree d of D,
// where a is monic and has roots the x-coordinates of the finite points in D (with multiplicity)
// and b(xi) = eta for all points (xi, eta) in the support of D.
function pts_to_abpol(pts, g, pol)
  if IsEmpty(pts) then
    return 1, 1, 0;
  end if;
  CC<i> := Parent(pts[1][1]);
  PC := PolynomialRing(CC); x := PC.1;

  // find Mumford representation of the divisor pts as complex polynomials
  if IsOdd(Degree(pol)) then
    d := #pts;
    assert d le g;
    apolC := &*[PC | x - pt[1] : pt in pts]; // apol has as zeroes exactly the x-coordinates of the divisor
    bpolC := Interpolation([CC| pt[1] : pt in pts], [CC| pt[2] : pt in pts]);
  else
    assert #pts eq g;
    d := g;
    pts_fin := [pt : pt in pts | pt[3] ne 0]; // does this really work for numerical points?
    pts_inf := [pt : pt in pts | pt[3] eq 0];
    apolC := &*[PC | x - pt[1] : pt in pts_fin]; // apol has as zeros exactly the x-coordinates of the divisor
    bpolC := Interpolation([CC| pt[1] : pt in pts_fin], [CC| pt[2] : pt in pts_fin]); // bpol(x_i) = y_i
    if not IsEmpty(pts_inf) then
      if #pts_inf gt 1 then
        if #pts_inf gt 2 then
          error "pts_to_abpol: more than two points at infinity!";
        end if;
        pt1, pt2 := Explode(pts_inf);
        assert pt1[1] eq 1 and pt2[1] eq 1;
        if Abs(pt1[2] + pt2[2]) lt 1e-10 then
          // points cancel
          d -:= 2;
        else
          assert pt1[2] eq pt2[2];
          cofa := Degree(apolC) eq 0 select 0 else Coefficient(apolC, Degree(apolC)-1);
          cof := (Coefficient(pol, 2*g+1)/Coefficient(pol, 2*g+2) - cofa)/2;
          bpolC +:= apolC*pt1[2]*x^(g-Degree(apolC))*(x + cof);
        end if;
      else
        pt := pts_inf[1];
        assert pt[1] eq 1;
        bpolC +:= apolC*pt[2]*x^(g+1-Degree(apolC));
      end if;
    end if;
  end if;
  return apolC, bpolC, d;
end function;

function polC_to_polQ(polC)
  // Recognize polC as a polynomial with coefficients in the rationals.
  Qx := PolynomialRing(Rationals());
  prec := Precision(BaseRing(polC));
  if exists{c : c in Coefficients(polC) | Abs(Im(c)) gt 0.1^(Floor(0.8*prec))} then
    return false, _;
  end if;

  try
    pol := Qx![RecognizeRationalElement(c) : c in Coefficients(polC)];
  catch e
    return false, _;
  end try;
  return true, pol;
end function;

function polC_to_polK(polC, K)
  // Recognize polC as a polynomial with coefficients in the Heegner field K.
  // We use the real and imaginary parts of the coefficients.
  Kx := PolynomialRing(K);
  sqrtD := Sqrt(CC!-K.1^2) where CC := BaseRing(polC);
  try
    polK := Kx![RecognizeRationalElement(Re(c)) + K.1*RecognizeRationalElement(Im(c)/sqrtD)
                  : c in Coefficients(polC)];
  catch e
//     print e;
    return false, _;
  end try;
  return true, polK;
end function;

intrinsic RecognizePointOnAnalyticJacobian(pt::ModMatFldElt, JC::AnHcJac, J::JacHyp) -> BoolElt, JacHypPt
{ Try to recognize a column vector representing a point on the analytic Jacobian JC
  as a point on J over its base field, which must be the rationals or imaginary quadratic. }
  // TODO: Check that J and JC are compatible
  K := BaseField(J);
  require K cmpeq Rationals() or
          (Type(K) eq FldNum and Degree(K) eq 2 and Discriminant(K) lt 0 and K.1^2 in Rationals()):
          "The base field of the Jacobian must be Q or Q(sqrt(-D)).";
  try
    vprintf HeegnerPoint, 4: "RecognizePointOnAnalyticJacobian:\n  pt = %o\n", pt;
    pts_y := FromAnalyticJacobianXYZ(pt, JC);
  catch e
    vprintf HeegnerPoint, 4: "FromAnalyticJacobianXYZ failed\n";
    return false, _;
  end try;
  vprintf HeegnerPoint, 4: "pts_y = %o\n", pts_y;
  // Convert list of points to Mumford polynomials
  pol := HyperellipticPolynomials(Curve(K cmpeq Rationals() select J else BaseChange(J, Rationals())));
  try
    apolC, bpolC, d := pts_to_abpol(pts_y, Dimension(JC), pol);
  catch e
    vprintf HeegnerPoint, 4: "pts_to_abpol failed\n";
    return false, _;
  end try;
  vprintf HeegnerPoint, 4: "(apolC, bpolC, d) = %o, %o, %o\n", apolC, bpolC, d;
  if d eq 0 then return true, J!0; end if;
  // Recognize coefficients.
  if K cmpeq Rationals() then
    flaga, apol := polC_to_polQ(apolC);
    flagb, bpol := polC_to_polQ(bpolC);
  else
    flaga, apol := polC_to_polK(apolC, K);
    flagb, bpol := polC_to_polK(bpolC, K);
  end if;
  if not (flaga and flagb) then
     vprintf HeegnerPoint, 4: "Could not recognize polynomial coefficients\n";
    return false, _;
  else
// // elt<J | apol, bpol, d> below gives an error anyway if the polynomials are not correct
//        vprintf HeegnerPoint, 4: "Heegner point given by\n apol = %o\n bpol = %o\n", apol, bpol;
//        ptsJ := RationalPoints(JK, apol, d);
//        if not IsEmpty(ptsJ) then
//          vprintf HeegnerPoint, 4: "apol seems to be correct\n";
//          if bpol notin {pt[2] : pt in ptsJ} then
//            vprintf HeegnerPoint, 4: " ... but bpol is not\n";
//          end if;
//        end if;
    try
      pt_K := elt<J | apol, bpol, d>;
      return true, pt_K;
    catch e
      vprintf HeegnerPoint, 4: "recognized polynomials do not give rise to a point in J(K)\n:  %o\n  %o\n",
              apol, bpol;
      return false, _;
    end try;
  end if;
end intrinsic;

intrinsic RecognizeAnalyticTwoTorsionPoint(pt::ModMatFldElt, JC::AnHcJac, J::JacHyp) -> JacHypPt
{ Try to recognize a column vector representing a 2-torsion point on the analytic Jacobian JC
  as a point on J over its base field, which must be the rationals or imaginary quadratic. }
  T, mT := TwoTorsionSubgroup(J);
  g := Dimension(J);
  tors := [mT(t) : t in T];
  // compute analytic images of all 2-torsion points
  K := BaseField(J);
  plc := InfinitePlaces(K);
  require #plc eq 1: "The base field of the Jacobian must be the rationals or imaginary quadratic.";
  if K cmpeq Rationals() then
    images := [ToAnalyticJacobianMumford(t, JC) : t in tors];
  else
    images := [ToAnalyticJacobianMumford(t, JC, 1) : t in tors];
  end if;
  bpm := BigPeriodMatrix(JC);
  basmat := Matrix([[Real(bpm[j,i]) : j in [1..g]] cat [Imaginary(bpm[j,i]) : j in [1..g]] :
                        i in [1..2*g]]);
  basmati := basmat^-1;
  L := Lattice(basmat);
  imL := [Vector([Real(z) : z in Eltseq(v)] cat [Imaginary(z) : z in Eltseq(v)]) : v in images];
  V := Universe(imL);
  // find vectors in L close to 2*v
  two_im := [ClosestVector(L, 2*v) : v in imL];
  assert Min([Norm(V!two_im[j] - 2*imL[j]) : j in [1..#imL]]) lt 10^(-Precision(BaseField(JC)));
  two_im := [Vector(GF(2), [Round(x) : x in Eltseq((V!v) * basmati)]) : v in two_im];
  ptL := Vector([Real(z) : z in Eltseq(pt)] cat [Imaginary(z) : z in Eltseq(pt)]);
  two_pt := ClosestVector(L, 2*ptL);
  assert Norm(V!two_pt - 2*ptL) lt 10^(-Precision(BaseField(JC)));
  two_pt := Vector(GF(2), [Round(x) : x in Eltseq((V!two_pt) * basmati)]);
  pos := Position(two_im, two_pt);
  assert pos gt 0;
  return tors[pos];
end intrinsic;

intrinsic ActionOnJacobian(pt::JacHypPt, JC::AnHcJac, act::AlgMatElt) -> JacHypPt
{ Find the image of pt (a point over the rationals or an imaginary quadratic field
  on a hyperelliptic Jacobian J) under the action of act, represented on the analytic
  Jacobian JC associated to J. }
  J := Parent(pt);
  C := Curve(J);
  prec := Precision(BaseField(JC));
  K := BaseField(J);
  plc := InfinitePlaces(K);
  require #plc eq 1: "The base field of the Jacobian must be the rationals or imaginary quadratic.";
  plc := plc[1];
  if pt eq J!0 then return pt; end if;
  if 2*pt eq J!0 then
    while true do
      success := true;
      actCC := ChangeRing(act, BaseField(JC));
      try
        // map to analytic Jacobian
        pt_JC := K cmpeq Rationals() select ToAnalyticJacobianMumford(pt, JC)
                                     else ToAnalyticJacobianMumford(pt, JC, 1);
        im := RecognizeAnalyticTwoTorsionPoint(actCC*pt_JC, JC, J);
      catch e
        success := false;
      end try;
      if success then
        return im;
      else
        prec := Round(Sqrt(2)*prec);
        JC := K cmpeq Rationals() select AnalyticJacobian(Curve(C) : Precision := prec)
                                  else AnalyticJacobian(Curve(C), plc : Precision := prec);
      end if;
    end while;
  else
    while true do
      success := true;
      actCC := ChangeRing(act, BaseField(JC));
      try
        // map to analytic Jacobian
        pt_JC := K cmpeq Rationals() select ToAnalyticJacobianMumford(pt, JC)
                                    else ToAnalyticJacobianMumford(pt, JC, 1);
      catch e
        success := false;
      end try;
      if success then
        flag, im := RecognizePointOnAnalyticJacobian(actCC*pt_JC, JC, J);
        success and:= flag;
      end if;
      if success then
        return im;
      else
        prec := Round(Sqrt(2)*prec);
        JC := K cmpeq Rationals() select AnalyticJacobian(Curve(C) : Precision := prec)
                                  else AnalyticJacobian(Curve(C), plc : Precision := prec);
      end if;
    end while;
  end if;
  return J!0; // we never get here
end intrinsic;

//===========================================================================

// Helper functions for matrices

function compare(M1, M2)
  return ChangePrecision(Max([Abs(M1[i,j] - M2[i,j]) : i in [1..Nrows(M1)], j in [1..Ncols(M1)]]), 6);
end function;

matAct := func<M, f | Matrix([[f(M[i,j]) : j in [1..Ncols(M)]] : i in [1..Nrows(M)]])>;

matRe := func<M | matAct(M, Real)>;
matIm := func<M | matAct(M, Imaginary)>;
matConj := func<M | matAct(M, Conjugate)>;
matRound := func<M | matAct(M, Round)>;

matCP := func<M, prec | matAct(M, func<z | ChangePrecision(z, prec)>)>;

function rat_approx(x, prec)
  // x: real number
  pol := MinimalPolynomial(x, 1, 10^Floor(prec/3));
  return -Coefficient(pol, 0)/Coefficient(pol, 1);
end function;

matRatApprox := func<M, prec | matAct(M, func<x | rat_approx(x, prec)>)>;

function quotBPM(bpm1, bpm2)
  // Find integral matrix M such that bpm1 * M = bpm2,
  // where bpm1 and bpm2 are big period matrices of the same genus.
  // The second return value indicates the error in rounding to an integer matrix.
  M1 := VerticalJoin(matRe(bpm1), matIm(bpm1));
  M2 := VerticalJoin(matRe(bpm2), matIm(bpm2));
  M := M1^-1 * M2;
  MZ := matRound(M);
  return MZ, compare(M, ChangeRing(MZ, BaseRing(M)));
end function;

function get_alpha(bpm1, bpm2, M)
  // Get the matrix alpha such that alpha*bpm1 = bpm2*M,
  // where bpm1 and bpm2 are big period matrices of the same genus.
  // The second return value indicates the error between the two solutions
  // obtained from the two halves of the big period matrices.
  g := Nrows(bpm1);
  assert Nrows(bpm2) eq g and Ncols(bpm1) eq 2*g and Ncols(bpm2) eq 2*g;
  bpm2a := bpm2*ChangeRing(M, BaseRing(bpm2));
  A1 := Submatrix(bpm1, 1, 1, g, g); A2 := Submatrix(bpm1, 1, g+1, g, g);
  B1 := Submatrix(bpm2a, 1, 1, g, g); B2 := Submatrix(bpm2a, 1, g+1, g, g);
  // must have alpha*A1 = B1 and alpha*A2 = B2
  alpha1 := B1*A1^-1;
  alpha2 := B2*A2^-1;
  return (alpha1 + alpha2)/2, compare(alpha1, alpha2);
end function;

//===========================================================================

intrinsic DiagramData(C::CrvHyp, N::RngIntElt :
                      prec := 20, max_prec := 500, quiet := false,
                      Snew := ModularSymbolsSpaceFromCurve(C : N := N),
                      L_is_zero_at_1 := not IsEvenRank(Snew))
  -> SeqEnum, SeqEnum, SeqEnum, RngElt, AnHcJac, ModFrmElt, Map, ModSym, BoolElt, ModAbVar
{ Computes data related to the diagram linking J_0(N), A_f, J = Jac(C) and their duals.
  Returns the following: (1) a sequence containing big period matrices of A_f^v, A_f, J;
  (2) a sequence containing the alpha-matrices for the isogenies A_f^v -lambda_f-> A_f,
  A_f -pi-> J, J --> J (given by a generator of End_Q(J)), J --> J (the "roundtrip isogeny"
  J -~-> J^v -pi^v-> A_f^v -lambda_f-> A_f -pi-> J); (3) a sequence containing the
  corresponding M-matrices (such that for an isogeny A --> B, we have alpha * P(A) = P(B) * M,
  where P(A) and P(B) are big period matrices for A and B, respectively); (4) the roundtrip
  isogeny as an element of the abstract endomorphism ring of J; (5) the analytic Jacobian of C;
  (6) a newform associated to C; (7) the isomorphism End(J)⁰ --> Q(f) induced by the isogeny;
  (8) the modular symbols space associated to C; (9) a flag indicating whether the L-rank is odd or not.
}
  // Check if already computed.
  // C`DiagramData = <prec, [* seq1, seq2, seq3, ainO, JC, f, isom, Snew, L_is_zero_at_1, Af_dual *]>
  if assigned C`DiagramData then
    bpms, alphas, Ms, ainO, f := Explode(C`DiagramData[2]);
    if C`DiagramData[1] lt prec then
      // We trust the computation of the BPM of the analytic Jacobian and use
      // it to update the other ones.
      JC := AnalyticJacobian(C : Precision := prec);
      // We have to be careful: in some cases the new period matrix is computed
      // with a different homology basis, so correct that if necessary
      bpmJ := BigPeriodMatrix(JC);
      M, err := quotBPM(bpmJ, bpms[3]);
      if err ge 0.1^(C`DiagramData[1] - 6) then
        printf "DiagramData: prec = %o, err = %o\n", prec, ChangePrecision(err, 6);
      end if;
      CC := BaseRing(bpmJ);
      bpmJ := bpmJ * ChangeRing(M, CC);
      bpmAf := ChangeRing(alphas[2], CC)^-1 * bpmJ * ChangeRing(Ms[2], CC);
      bpmAfdual := bpmAf * ChangeRing(Ms[1], CC);
      // Update stored data
      C`DiagramData[1] := prec;
      C`DiagramData[2][1] := [bpmAfdual, bpmAf, bpmJ];
      C`DiagramData[2][5] := JC;
    end if;
    // Return values to required precision.
    val := C`DiagramData[2];
    val[1] := [matCP(bpm, prec) : bpm in val[1]];
    return Explode(val);
  end if;

  pol, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve must be given in the form y^2 = f(x).";

  if prec gt max_prec then
    error "HeegnerPoint: prec > max_prec ==> abort.\n";
  end if;
  g := Genus(C);
  require g eq 2 and BaseField(C) cmpeq Rationals():
          "Curve must be of genus 2 and be defined over the rationals.";
  // One could check that Conductor(C) eq N^2.
  J := Jacobian(C);
  alpha_gen, OtoEnd := EndomorphismRingGenus2(J);

  Qx<x> := PolynomialRing(Rationals() : Global := false); // don't overwrite variable name
  if not quiet then
    vprintf HeegnerPoint, 1: "DiagramData: N = %o\n", N;
    vprintf HeegnerPoint, 1: "             C: y^2 = %o\n", Qx!pol;
    vprintf HeegnerPoint, 1: "             L-rank = %o, prec = %o\n\n",
                             L_is_zero_at_1 select 1 else 0, prec;
  end if;

  // Fix a newform associated to C
  f := NewformFromCurve(C : N := N);

  // Determine the associated modular abelian variety.
  assert Dimension(Snew) eq 2*g;
  // NOTE: We use "[Snew]" instead of "Snew", because ModularAbelianVariety(Snew)
  //       first computes the modular abelian variety associated to the full ambient space,
  //       which can take a long time.
//   A := ModularAbelianVariety([Snew]);
  // However, the above version does not seem to always do the right thing...
  // So back to
  A := ModularAbelianVariety(Snew);
  // The matrix of the intersection pairing on the integral homology of A,
  // as an integral matrix. The polarization  lambda_f: A = A_f^v --> A_f
  // is given by the pair (I_2, imat).
  imat := ChangeRing(IntersectionPairingIntegral(A), Integers());

  // The matrix giving the canonical polarization of J on the lattice.
  jmat := Matrix([[0,0,1,0], [0,0,0,1], [-1,0,0,0], [0,-1,0,0]]);

  // Compute big period matrices with increasing precision until the computation works
  // to obtain the isogeny A_f --> J.
  function ComputeBPMsEtc(prec)
    if prec gt max_prec then
      error "ERROR: found no isogeny A_f -> Jac(C) at precision max_prec, giving up!\n";
    end if;
    // Set up analytic Jacobian.
    try
      JC := AnalyticJacobian(C : Precision := prec);
    catch e
      vprintf HeegnerPoint, 2:
              "Error when calling AnalyticJacobian with precision %o, increasing precision ...\n", prec;
      return $$(Ceiling(1.5*prec));
    end try;
    // Compute/extract its big period matrix.
    bpmJ := BigPeriodMatrix(JC); // this is w.r.t. a symplectic homology basis
    CC := BaseRing(bpmJ);
    // TODO: the precision is correct only if using fast period integrals
    bpmAfdual := ChangeRing(BigPeriodMatrix(A, prec), CC);

    // The big period matrix of A_f w.r.t. a good homology basis.
    bpmAf := bpmAfdual * ChangeRing(imat, CC)^-1;

    // find an isogeny A_f -> Jac(C) over \C
    flag, M, alpha := IsIsogenousPeriodMatrices(bpmAf, bpmJ);
    if flag then
      vprintf HeegnerPoint, 2: "period matrices are isogenous";
      vprintf HeegnerPoint, 2: " by an isogeny of degree %o\n", Abs(Determinant(M));
    else
      new_prec := Ceiling(prec * 1.5);
      vprintf HeegnerPoint, 1: "no isogeny found with precision %o, increasing precision to %o ...\n",
                               prec, new_prec;
      return $$(new_prec);
    end if;
    return prec, alpha, JC, bpmJ, M, bpmAf, bpmAfdual;
  end function;

  target := prec;

  while true do
    success := true;
    newprec, alpha_pi, JC, bpmJ, M_pi, bpmAf, bpmAfdual := ComputeBPMsEtc(prec);
    CC := BaseRing(alpha_pi);

    // alpha_pi as a rational matrix
    alpha_pi_Q := matRatApprox(matRe(alpha_pi), target-5);
    eps := compare(ChangeRing(alpha_pi_Q, CC), alpha_pi);
    if eps ge 10^(3-target) then
      vprintf HeegnerPoint, 4:
              "alpha_pi not close enough to a rational matrix:\n  10^target*eps = %o\n",
              ChangePrecision(10^target*eps, 5);
    end if;
    success and:= eps lt 10^(3-target);

    // Matrices for generator of End_Q(J)
    alpha_gen := ChangeRing(alpha_gen, Rationals());
    M_gen, eps := quotBPM(bpmJ, ChangeRing(alpha_gen, CC)*bpmJ);
    if eps ge 10^(3-target) then
      vprintf HeegnerPoint, 4:
              "M_gen not close enough to an integral matrix:\n  10^target*eps = %o\n",
              ChangePrecision(10^target*eps, 5);
    end if;
    success and:= eps lt 10^(3-target);

    // Compute "roundtrip" endomorphism.
    M_round := M_pi*imat*Transpose(M_pi)*jmat;
//     printf "M_round =\n%o\n", M_round;
//     printf "minpol: %o\n", MinimalPolynomial(M_round);
    alpha_round, eps := get_alpha(bpmJ, bpmJ, M_round);
    if eps ge 10^(3-target) then
      vprintf HeegnerPoint, 4:
              "alpha_round not sufficiently precise:\n  10^target*eps = %o\n",
              ChangePrecision(10^target*eps, 5);
    end if;
    success and:= eps lt 10^(3-target);
    alpha_Q := matRatApprox(matRe(alpha_round), target-5);
    eps := compare(ChangeRing(alpha_Q, CC), alpha_round);
    if eps ge 10^(3-target) then
      vprintf HeegnerPoint, 4:
              "alpha_Q not close enough to a rational matrix:\n  10^target*eps = %o\n",
              ChangePrecision(10^target*eps, 5);
    end if;
    success and:= eps lt 10^(3-target);
    if success then
      prec := newprec;
      break;
    else
      prec := Ceiling(1.5*newprec);
      vprintf HeegnerPoint, 1: "precision target not reached, increasing precision to %o\n", prec;
    end if;
  end while;

  // Now optimize the roundtrip alpha matrix by post-composing the isogeny A_f --> J
  // with an automorphism u. This multiplies alpha_Z by u^2. We minimize the trace
  // (which is positive, since the roundtrip map is a polarization, so is a totally
  // positive element of End_Q(J)).
  OJ := Domain(OtoEnd);
  U, mU := UnitGroup(OJ);
  assert #Invariants(U) eq 2; // U = Z/2 x Z
  u := Parent(alpha_Q)!OtoEnd(mU(U.2));
  u2 := Parent(alpha_Q)!OtoEnd(mU(2*U.2)); // a generator of the group of squares of units
  shift := 0;
  if Trace(alpha_Q*u2) lt Trace(alpha_Q) then
    repeat
      alpha_Q := alpha_Q * u2;
      alpha_pi_Q := u * alpha_pi_Q;
      shift +:= 1;
    until Trace(alpha_Q*u2) ge Trace(alpha_Q);
  elif Trace(alpha_Q*u2^-1) lt Trace(alpha_Q) then
    u2 := u2^-1;
    u := u^-1;
    repeat
      alpha_Q := alpha_Q * u2;
      alpha_pi_Q := u * alpha_pi_Q;
      shift -:= 1;
    until Trace(alpha_Q*u2) ge Trace(alpha_Q);
  end if;

  // Check that alpha_Q is in End_Q(J).
  flag, sol := IsConsistent(Matrix([[1,0,0,1], Eltseq(alpha_gen)]), Vector(Eltseq(alpha_Q)));
  assert flag;
  alpha_in_End := Domain(OtoEnd)!(sol[1] + Domain(OtoEnd).2*sol[2]);
  assert MinimalPolynomial(alpha_Q) eq MinimalPolynomial(alpha_in_End);

  // Update M_pi and M_round.
  epsseq := ChangeUniverse(Eltseq(mU(shift*U.2)), Integers());
  M_eps := epsseq[1]*IdentityMatrix(Integers(), 4) + epsseq[2]*M_gen;
  M_pi := M_eps*M_pi;
  M_round := M_pi*imat*Transpose(M_pi)*jmat;

  // Check
  assert compare(bpmAfdual, bpmAf*ChangeRing(imat, CC)) lt 10^(5-target);
  assert compare(ChangeRing(alpha_pi_Q, CC)*bpmAf, bpmJ*ChangeRing(M_pi, CC)) lt 10^(5-target);
  assert compare(ChangeRing(alpha_gen, CC)*bpmJ, bpmJ*ChangeRing(M_gen, CC)) lt 10^(5-target);
  assert compare(ChangeRing(alpha_Q, CC)*bpmJ, bpmJ*ChangeRing(M_round, CC)) lt 10^(5-target);

  // Update big period matrices of A_f and A_f^v, based on that of J
  // (which we trust more).
  bpmAf := ChangeRing(alpha_pi_Q, CC)^-1*bpmJ*ChangeRing(M_pi, CC);
  bpmAfdual := bpmAf*ChangeRing(imat, CC);

  // Find embedding of End(J) into Q(f).
  // First find a Hecke operator whose image in End(A)⁰ generates Q(f).
  vprintf HeegnerPoint, 2: "  setting up isomorphism between endomorphism algebras:\n";
  p := 1;
  repeat
    p := NextPrime(p);
    while IsDivisibleBy(N, p) do p := NextPrime(p); end while;
  until Degree(MinimalPolynomial(Coefficient(f, p))) eq Degree(BaseField(f));
  vprintf HeegnerPoint, 2: "    a_%o generates endomorphism algebra\n", p;
  TpMat := ChangeRing(Transpose(IntegralMatrix(HeckeOperator(A, p))), Rationals());
  vprintf HeegnerPoint, 2: "    ... matrix of T_%o computed\n", p;
  MM := ChangeRing(M_pi * imat, Rationals());
  alphaTCC := get_alpha(bpmJ, bpmJ, MM * TpMat * MM^-1);
  alphaT := matRatApprox(alphaTCC, target);
  eps := compare(alphaTCC, ChangeRing(alphaT, CC));
  assert eps lt 10^(5-target);
  // Check that alphaT is in End_Q(J)⁰.
  flag, sol := IsConsistent(Matrix(Rationals(), [[1,0,0,1], Eltseq(alpha_gen)]), Vector(Eltseq(alphaT)));
  assert flag;
  EndAlgJ := NumberField(Domain(OtoEnd));
  alphaT_in_End := EndAlgJ!Eltseq(sol);
  alphaT_pol := Polynomial(Eltseq(alphaT_in_End));
  alphaT_in_Qf := BaseField(f)!Coefficient(f, p);
  rts := [r[1] : r in Roots(MinimalPolynomial(EndAlgJ.1), BaseField(f))];
  images := [Evaluate(alphaT_pol, r) : r in rts];
  pos := Position(images, alphaT_in_Qf);
  assert pos gt 0;
  // Set up isomorphism End(J)⁰ --> Q(f).
  isom := iso<EndAlgJ -> BaseField(f) | rts[pos]>;

  // Store data / update stored data.
  C`DiagramData := <prec, [* [bpmAfdual, bpmAf, bpmJ],
                             [IdentityMatrix(Rationals(), 2), alpha_pi_Q, alpha_gen, alpha_Q],
                             [imat, M_pi, M_gen, M_round],
                             alpha_in_End,
                             JC,
                             f,
                             isom,
                             Snew,
                             L_is_zero_at_1,
                             A *]>;

  // Return data to required precision.
  val := C`DiagramData[2];
  val[1] := [matCP(bpm, target) : bpm in val[1]];
  return Explode(val);
end intrinsic;

intrinsic NextHeegnerDiscriminant(N::RngIntElt, D::RngIntElt) -> RngIntElt
  { Return the largest Heegner discriminant for N which is smaller than D.}
  require N gt 1:
    "N must be > 1";
  D := Min(D, -3); // -7 ist the largest possible D
  require (D mod 4) eq 1:
    "D must be the discriminant of a number field unramified at 2";
  repeat
    D -:= 4;
  until (Gcd(2*N, D) eq 1) // (D, 2N) = 1
      and IsSquare(Integers(4*N)!D) // and D = square (mod 4N) [all primes dividing D split completely in \Q(\sqrt{D})]
      and D eq Discriminant(QuadraticField(D)); // and D is a discriminant of an imaginary quadratic field
  return D;
end intrinsic;

// Determine a Heegner point y_K in J(K).
// Here K is Q(sqrt(D)) (with K.1 = sqrt(D), D < 0) and J is the Jacobian of C.
intrinsic HeegnerPoint(C::CrvHyp, N::RngIntElt, D::RngIntElt :
                       prec := 20, max_prec := 500,
                       Snew := ModularSymbolsSpaceFromCurve(C : N := N),
                       L_is_zero_at_1 := not IsEvenRank(Snew)) -> SeqEnum[JacHypPt]
{ Computes a Heegner point and its image undeer a generator of the endomorphism ring
  on the Jacobian J of a genus 2 curve C such that J is modular of level N. }
  pol, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve must be given in the form y^2 = f(x).";

  if prec gt max_prec then
    error "HeegnerPoint: prec > max_prec ==> abort.\n";
  end if;
  g := Genus(C);
  require g eq 2 and BaseField(C) cmpeq Rationals():
          "Curve must be of genus 2 and be defined over the rationals.";
  // One could check that Conductor(C) eq N^2.

  assert Dimension(Snew) eq 2*g;

  Qx<x> := PolynomialRing(Rationals() : Global := false); // don't overwrite variable name
  vprintf HeegnerPoint, 1: "HeegnerPoint: N = %o\n", N;
  vprintf HeegnerPoint, 1: "              C: y^2 = %o\n", Qx!pol;
  vprintf HeegnerPoint, 1: "              D = %o, L-rank = %o, prec = %o\n\n",
                           D, L_is_zero_at_1 select 1 else 0, prec;

  // Define the Heegner field.
  K<w> := NumberField(x^2 - D);
  // Its class number gives the degree of the Heegner cycle on X_0(N).
  h := ClassNumber(K);
  vprintf HeegnerPoint, 2: "The Heegner cycle has degree h = %o\n", h;

  // Determine the quadratic forms defining the points in the Heegner cycle.
  forms := HeegnerForms(N, D);
  taupols := [Qx| ];
  for form in forms do
    // The polynomial whose root with positive imaginary part maps to a point in the cycle.
    taupol := Qx![form[3], form[2], form[1]];
    // A sanity check:
    assert Discriminant(taupol) eq D and IsDivisibleBy(Integers()!Coefficient(taupol, 2), N);
    Append(~taupols, taupol);
  end for;
  vprintf HeegnerPoint, 4: "[tau] = %o\n", taupols;

  // Compute big period matrices etc. at low precision first (default precision is 20).
  bpms, alphas, Ms, ainO, JC, f, _, _, _, A
    := DiagramData(C, N : max_prec := max_prec, quiet, Snew := Snew, L_is_zero_at_1 := L_is_zero_at_1);
  vprintf HeegnerPoint, 4: "f = %o\n", f;

  discA := Discriminant(BaseRing(f));

  J := Jacobian(C);
  Jtw := Jacobian(QuadraticTwist(C, D));
  JK := BaseChange(J, K);
  gen, OtoEnd := EndomorphismRingGenus2(J);
  discJ := Discriminant(Domain(OtoEnd));

  // Compute a multiplicative bound on the size of the kernel
  // of the isogeny on A_f(K).
  M := Ms[2];
  kernel_bound := GCD(TorsionMultiple(BaseExtend(A, K), 100), Determinant(M)); // needed?
  vprintf HeegnerPoint, 1: "bound for #ker(isogeny)|A_f(K) is %o\n", kernel_bound;

  vprintf HeegnerPoint, 4: "alpha = %o\n", alphas[2];
  repeat
    // Map the Heegner cycle on the upper half plane to \C^2/\Lambda_f
    // via period integrals tau -> 2\pi i \sum_n a_n exp(2pi i n tau).
    bpms, alphas, Ms, ainO, JC := DiagramData(C, N : prec := prec, max_prec := max_prec,
                                                 Snew := Snew, L_is_zero_at_1 := L_is_zero_at_1);
    // The big period matrix of J
    bpmJ := bpms[3];
    CC<i> := BaseRing(bpmJ); // use the precision of the computed isogeny
    // alpha is the matrix giving the map C^2/Lambda_f = A_f(C) --> J(C) = C^2/Lambda_J .
    alpha := ChangeRing(alphas[2], CC);
    prec := Precision(CC);
    twopi := 2*Pi(CC);

    // Initialize the Heegner point in C^2/Lambda_J.
    y_K_CC := ZeroMatrix(CC, g, 1);
    for taupol in taupols do
      // Get tau in upper half plane and q = e^(2 pi i tau)
      tau := Roots(taupol, CC)[2,1]; assert Imaginary(tau) gt 0;
      twopiImtau := twopi * Imaginary(tau);
      Nterms := Max(50, 10 + Ceiling((prec*Log(10) + Log(Sqrt(3)/(1-Exp(-twopiImtau)))) / twopiImtau));
      vprintf HeegnerPoint, 2:
              "computing %o terms of the q-expansion for y_K of precision %o ...\n",
              Nterms, prec;
      // Get enough terms of the q-expansions of the integral basis
      // (which is also used in the computation of the big period matrix of A_f).
      fqbas := qIntegralBasis(Snew, Nterms + 1);
      f1, f2 := Explode(fqbas); // Here genus = 2 is hard-coded!
      // Compute
      // \int_{i\infty}^tau omega_j = \int_{i\infty}^tau f_j(q) dq/q
      //                            = \sum_{n >= 1} a_n(f_j)/n exp(2pi i tau)
      // to map the Heegner point tau on the upper half plane to \C^2.
      period_integrals_f1f2 := [CC | 0, 0];
      q := Exp(twopi * i * tau);
      qn := CC!1;
      for n := 1 to Nterms do
        qn *:= q; // qn = q^n = exp(2 pi i n tau)
        exp := qn / n; // Abs(exp) <= 1
        period_integrals_f1f2[1] +:= CC!Coefficient(f1, n) * exp;
        period_integrals_f1f2[2] +:= CC!Coefficient(f2, n) * exp;
      end for;
      ptC := alpha * Matrix(g, 1, period_integrals_f1f2);
      vprintf HeegnerPoint, 4: "ptC = %o\n", ptC;
      y_K_CC +:= ptC;
    end for;
    // Now y_K_CC in C^2 represents the Heegner point in C^2/Lambda_J = J(C).
    vprintf HeegnerPoint, 4: "y_K_CC = %o\n", y_K_CC;

    // find divisor representation of y_K_CC
    success1, y_K := RecognizePointOnAnalyticJacobian(ChangeRing(y_K_CC, CC), JC, JK);
    ay_K_CC := ChangeRing(gen, CC)*y_K_CC;
    success2, ay_K := RecognizePointOnAnalyticJacobian(ChangeRing(ay_K_CC, CC), JC, JK);
    if not (success1 and success2) then
      vprintf HeegnerPoint, 1: "could not recognize numerical point as point over K,";
      prec := Round(prec * Sqrt(2));
      vprintf HeegnerPoint, 1: " increasing precision to %o\n", prec;
    end if;
  until success1 and success2;

  vprintf HeegnerPoint, 1: "y_K given by\n  apol = %o\n  bpol = %o\n", y_K[1], y_K[2];
  vprintf HeegnerPoint, 1: "gen*y_K given by\n  apol = %o\n  bpol = %o\n", ay_K[1], ay_K[2];
  return [y_K, ay_K], kernel_bound, L_is_zero_at_1, M, discA, discJ;
end intrinsic;

intrinsic SomeHeegnerPoint(C::CrvHyp, N::RngIntElt : D := 0, prec := 20, max_prec := 500) -> SeqEnum[JacHypPt]
{ Compute a Heegner point for the first or next Heegner discriminant. }
  pol, h := HyperellipticPolynomials(C);
  if h ne 0 then
    printf "Replacing curve by simplified model!\n";
    C := SimplifiedModel(C);
  end if;
  D := NextHeegnerDiscriminant(N, D);
  y_Ks, kernel_bound, L_is_zero_at_1, deg, discA, discJ
    := HeegnerPoint(C, N, D : prec := prec, max_prec := max_prec);
  return y_Ks, kernel_bound, L_is_zero_at_1, deg, D, discA, discJ;
end intrinsic;

intrinsic IndexOfSubmodule(pts::[JacHypPt] : SearchBound := 1000)
  -> GrpAb, Map
{ Compute the index of the submodule over the endomorphism ring of the parent J
  of the point pt (assumed to have real multiplication) generated by pt inside
  the Mordell-Weil group. }
  J := Universe(pts);
  K := BaseField(J);
  assert K.1^2 in Integers() and Integers()!(K.1^2) lt 0;
  repeat
    MW, MWtoJ, fl := MordellWeilGroupJK(J, pts : MaxBound := SearchBound);
    if not fl then
      vprintf HeegnerPoint, 1:
              "\nIndexOfSubmodule: WARNING: J(K) not determined with certainty! (search bound %o)\n",
              SearchBound;
      SearchBound := Round(SearchBound * Sqrt(2));
    end if;
  until fl;
  vprintf HeegnerPoint, 1: "J(K) has invariants %o\n", Invariants(MW);
  // Now pull points back to abstract group.
  result := quo<MW | pts[1] @@ MWtoJ, pts[2] @@ MWtoJ>;
  vprintf HeegnerPoint, 3: "\ngroup structure of quotient: %o, index = %o\n\n",
                           Invariants(result), #result;
  return result, MWtoJ, MW;
end intrinsic;

intrinsic CharacteristicIdealOfSubmodule(pts::[JacHypPt], JC::AnHcJac : SearchBound := 1000)
  -> GrpAb, Map
{ Compute the index of the submodule over the endomorphism ring of the parent J
  of the point pt (assumed to have real multiplication) generated by pt inside
  the Mordell-Weil group. }
  J := Universe(pts);
  K := BaseField(J);
  assert K.1^2 in Integers() and Integers()!(K.1^2) lt 0;
  repeat
    MW, MWtoJ, fl := MordellWeilGroupJK(J, pts : MaxBound := SearchBound);
    if not fl then
      vprintf HeegnerPoint, 1:
              "\nIndexOfSubmodule: WARNING: J(K) not determined with certainty! (search bound %o)\n",
              SearchBound;
      SearchBound := Round(SearchBound * Sqrt(2));
    end if;
  until fl;
  vprintf HeegnerPoint, 1: "J(K) has invariants %o\n", Invariants(MW);
  // Now pull points back to abstract group.
  qu, mqu := quo<MW | pts[1] @@ MWtoJ, pts[2] @@ MWtoJ>;
  vprintf HeegnerPoint, 3: "\ngroup structure of quotient: %o, index = %o\n\n",
                           Invariants(qu), #qu;
  // find action of generator of End on generators of MW
  JQ := BaseChange(J, Rationals());
  gen, OtoEnd := EndomorphismRingGenus2(JQ);
  O := Domain(OtoEnd);
  action := hom<MW -> MW | [ActionOnJacobian(MWtoJ(g), JC, gen) @@ MWtoJ : g in OrderedGenerators(MW)]>;
  action_on_qu := hom<qu -> qu | [mqu(action(q @@ mqu)) : q in OrderedGenerators(qu)]>;
  index := #qu;
  result := [Parent(<ideal<O | 1>, 1>)| ];
  if index eq 1 then
    // nothing to do
    return result, qu, MWtoJ, MW;
  end if;
  primes := &cat[[e[1] : e in Decomposition(O, p)] : p in PrimeDivisors(index)];
  // peel off primes successively
  qu1 := qu;
  for pr in primes do
    e := 0;
    while true do
      prgens := Generators(pr);
      impr := sub<qu1 | [s[1]*q + s[2]*action_on_qu(q)
                           where s := ChangeUniverse(Eltseq(pg), Integers()) :
                         q in Generators(qu1), pg in prgens]>;
      if impr eq qu1 then break; end if;
      m := Round(Log(Norm(pr), ExactQuotient(#qu1, #impr)));
      assert ExactQuotient(#qu1, #impr) eq Norm(pr)^m;
      e +:= m;
      action_on_qu := hom<impr -> impr | [impr!(action_on_qu(qu1!i)) : i in OrderedGenerators(impr)]>;
      qu1 := impr;
    end while;
    if e gt 0 then Append(~result, <pr, e>); end if;
  end for;
  return result, qu, MWtoJ, MW;
end intrinsic;

// A simpler version that does not require the Mordell-Weil group to be computed
intrinsic HeightOnJK(pt::JacHypPt : Precision := MyPrec(RealField())) -> FldReElt
{ Compute the normalized canonical height of a point on the base-change
  of a genus 2 Jacobian over Q to a quadratic number field K. }
  JK := Parent(pt);
  J := BaseChange(JK, Rationals()); // will give an error if JK is not a base change
  K := BaseField(JK);
  require Degree(K) eq 2: "The Jacobian pt is on must be over a quadratic number field";
  assert K.1^2 in Rationals(); // should not be necessary
  D := Rationals()!(K.1^2); //SquarefreeFactorization(Discriminant(Integers(K)));
  JD := Jacobian(QuadraticTwist(Curve(J), D));
  // Use that the K/Q-conjugate pt' of pt has the same height and the formula
  //   4 h^(pt) = 2 h^(pt) + 2 h^(pt') = h^(pt + pt') + h^(pt - pt'),
  // where pt + pt' comes from J and pt - pt' comes from JD.
  mpol := MinimalPolynomial(K.1);
  PK := PolynomialRing(K);
  isoPK := hom<PK -> PK | hom<K -> PK | -Coefficient(mpol, 1) - K.1>, PK.1>; // map to other root
  conj := func<pt | elt<JK | isoPK(pt[1]), isoPK(pt[2]), pt[3]>>;
  ptc := conj(pt);
  pt1 := J!(pt+ ptc);
  dif := pt - ptc;
  pt2 := elt<JD | ChangeRing(dif[1], Rationals()), ChangeRing(dif[2]*K.1, Rationals()), dif[3]>;
  return (Height(pt1 : Precision := Precision) + Height(pt2 : Precision := Precision))/4;
end intrinsic;

intrinsic HeegnerIndexJ(C::CrvHyp, f::ModFrmElt :
                            D := 0, prec := 20, max_prec := 500, SearchBound := 1000)
  -> RngIntElt, RngIntElt, BoolElt, FldRatElt, SeqEnum[JacHypPt], Map, RngIntElt
{ Compute the Heegner index for the Jacobian J of C (assuming it is isogenous to A_f).
  The further return values are: the Heegner discriminant D; a flag that is true if the
  L-function of f vanishes at s=1, else false;
  the square root of disc Z[f]/disc End(J); a sequence containing the Heegner point
  and its image under a generator of End(J); the map from the abstract group J(K)
  to the Jacobian of C over K; a bound on the kernel of the isogeny from A_f to J
  on K-rational points.
}
  N := Level(f);
  // If D is not given, find first Heegner discriminant.
  if D eq 0 then D := NextHeegnerDiscriminant(N, D); end if;
  // First compute a Heegner point.
  vprintf HeegnerPoint: "\nHeegnerIndex: N = %o, D = %o\n", N, D;
  ys, kernel_bound, L_is_zero_at_1, M, discA, discJ
    := HeegnerPoint(C, N, D : prec := prec, max_prec := max_prec);

  vprintf HeegnerPoint: "                L-rank = %o, isogeny degree = %o\n",
                        L_is_zero_at_1 select 1 else 0, Abs(Determinant(M));
  vprintf HeegnerPoint: "                disc(End(A_f)) = %o, disc(End(J)) = %o, kernel_bound = %o\n",
                        discA, discJ, kernel_bound;
  vprintf HeegnerPoint: "                y = %o\n\n",
                        ys[1];
  // Then determine the index of End(J)*y in J(K).
  quotient, MWtoJ, MW := IndexOfSubmodule(ys : SearchBound := SearchBound);
  vprintf HeegnerPoint: "                index_J = %o, D = %o\n", #quotient, D;
  flag, rt := IsSquare(discA/discJ); assert flag;
  return #quotient, D, L_is_zero_at_1, rt, ys, MWtoJ, kernel_bound;
end intrinsic;

intrinsic HeegnerIndex(C::CrvHyp, f::ModFrmElt :
                           D := 0, prec := 20, max_prec := 500, SearchBound := 1000)
  -> RngIntElt, RngIntElt
{ Compute a multiplicative upper bound for the Heegner index of the modular
  abelian surface of level N that is isogenous to the Jacobian of C. }
  I, D, L_is_zero_at_1, rt, ys, MWtoJ, kernel_bound := HeegnerIndexJ(C, f
      : D := D, prec := prec, max_prec := max_prec, SearchBound := SearchBound);
  return Integers()!(I*kernel_bound*rt), kernel_bound, L_is_zero_at_1, D, rt, ys, MWtoJ;
end intrinsic;
