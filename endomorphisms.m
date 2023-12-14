// Compute endomorphism rings of genus 2 Jacobians
// and their action on rational points.
//
// M. Stoll, started 2021-03-05

// We use the AnalyticJacobian machinery of Magma and hope for the best...

declare attributes JacHyp: AnalyticJacobian, Endgen, OtoEnd, JQ, JQ_to_J, alpha_JQfree, project_onto_free_part;

declare verbose JacHypEnd, 2;

MyPrec := Precision;

// First, obtain the endomorphism ring (over Q).
// For the moment, we assume that J has real multiplication
// and that the geometric endomorphism ring equals that over Q.
intrinsic EndomorphismRingGenus2(J::JacHyp : Precision := 300) -> AlgMatElt, Map
{ For a genus 2 Jacobian J over Q with real multiplication over Q,
  compute the analytic Jacobian and a matrix generating the endomorphism
  ring in the analytic representation. Returns the matrix gen and stores
  the analytic Jacobian and the matrix as attributes of J. The second
  return value is the homomorphism from the abstract endomorphism ring O
  to the endomorphism ring of the analytic Jacobian. One has O.2 eq gen. }
  if assigned J`Endgen and assigned J`AnalyticJacobian
       and MyPrec(BaseField(J`AnalyticJacobian)) ge Precision then
    assert assigned J`OtoEnd;
    return J`Endgen, J`OtoEnd;
  end if;

  require Dimension(J) eq 2: "J must be a genus 2 Jacobian";
  require BaseField(J) cmpeq Rationals(): "J must be defined over Q";
  X := Curve(J);
  f, h := HyperellipticPolynomials(X);
  require h eq 0: "The curve of J must have the form y^2 = f(x)";
  // Compute the analytic Jacobian
  if Precision lt 20 then Precision := 20; end if; // this needs prec >= 20
  vprintf JacHypEnd, 1: "EndomorphismRingGenus2: computing the analytic Jacobian (prec = %o)...\n", Precision;
  CC := ComplexField(Precision);
  fC := ChangeRing(f, CC);
  AJ := AnalyticJacobian(fC);
  //AJ := RiemannSurface(f, 2); // create a hyperelliptic Riemann surface
  vprintf JacHypEnd, 1: "EndomorphismRingGenus2: computing the endomorphism ring...\n";
  EndAJ, alphas := EndomorphismRing(AJ);
  //print EndAJ, alphas;
  assert Degree(EndAJ) eq 4;
  vprintf JacHypEnd, 1: "EndomorphismRingGenus2: discriminant is %o\n", [Determinant(EndAJ.i) : i in [1..#Generators(EndAJ)]];
  // Recognize the alphas as integral matrices
  vprintf JacHypEnd, 1: "EndomorphismRingGenus2: determining a generator...\n";
  //alphasZ := [Matrix([[Round(Real(a[i,j])) : j in [1..2]] : i in [1..2]]) : a in alphas];
  // recognize entries of alphas as elements of quadratic number field
  QuadraticFieldElement := function(x, K)
    minpol := MinimalPolynomial(x, 2); // find minimal polynomial of quadratic irrationality
    K := CompositeFields(K, NumberField(minpol));
    assert #K eq 1;
    K := K[1];
    assert Degree(K) le 2;
    assert Discriminant(K) gt 0; // real quadratic field?
    roots := Roots(PolynomialRing(K)!minpol);
    min, pos := Min([Abs(x - Parent(x)!r[1]) : r in roots]);
    return roots[pos][1], K;
  end function;
  //alphasQbar := [Matrix([[QuadraticFieldElement(a[i,j]) : j in [1..2]] : i in [1..2]]) : a in alphas];
  K := RationalsAsNumberField();
  alphasQbar := [];
  for a in alphas do
    amat := [];
    for i,j in [1..2] do
      anum, K := QuadraticFieldElement(a[i,j], K);
      Append(~amat, anum);
    end for;
    alphasQbar := [ChangeRing(aa, K) : aa in alphasQbar];
    Append(~alphasQbar, Matrix(K, 2,2, amat));
  end for;
  info := [<a, Degree(pol), Discriminant(pol)> where pol := MinimalPolynomial(a)
             : a in alphasQbar];
  info2 := [e : e in info | e[2] eq 2];
  min, pos := Min([e[3] : e in info2]);
  min := Integers()!min;
  assert min gt 1 and forall{e : e in info2 | flag and IsSquare(q) where flag, q := IsDivisibleBy(e[3], min)};
  gen := info2[pos][1];
  vprintf JacHypEnd, 1: "EndomorphismRingGenus2: generator is\n%o of determinant %o\n", gen, Determinant(gen);
  //J`Endgen := gen;
  J`AnalyticJacobian := AJ;


  OE := EquationOrder(ChangeRing(MinimalPolynomial(gen), Integers()));
  assert OE.1 eq One(OE);
  assert MinimalPolynomial(OE.2) eq MinimalPolynomial(gen);

  rts := [OE!r[1] : r in Roots(MinimalPolynomial(OE.2), FieldOfFractions(OE))];
  mats := [Parent(gen)!1, gen];
  OtoEnd := hom<OE -> Parent(gen) | [mats[1], &+[s[i] * mats[i] : i in [1..#s]] where s := Eltseq(rts[1])]>;
  J`Endgen := OE.2@OtoEnd;
  J`OtoEnd := OtoEnd;

  return J`Endgen, J`OtoEnd;
end intrinsic;

// Apply the generator to a rational point.
intrinsic EndgenAction(P::JacHypPt : max := 10) -> JacHypPt
{ Apply the generator of the endomorphism ring of P's parent to P. WARNING: Might not work if P is torsion! }
  J := Parent(P);
  if not assigned J`Endgen then
    alpha := EndomorphismRingGenus2(J);
  else
    alpha := J`Endgen;
  end if;
  return EndomorphismAction(alpha, P : max := 10);
end intrinsic;

// Apply the generator to a rational point.
intrinsic EndomorphismAction(alpha::AlgMatElt, P::JacHypPt : max := 10) -> JacHypPt
{ Apply the endomorphism alpha to P. WARNING: Might not work if P is torsion! }
  J := Parent(P);
  AJ := J`AnalyticJacobian;
  CC := BaseField(AJ);
  alphaC := ChangeRing(alpha, CC);
  f, h := HyperellipticPolynomials(Curve(J));
  require h eq 0: "The hyperelliptic curve must be in reduced form.";
  // Helper function
  function act_on_AJ(pt, htbd)
    apol := pt[1];
    bpol := pt[2];
    if Degree(apol) lt pt[3] then
      // representation involves points at infinity
      vprintf JacHypEnd, 1: "EndomorphismAction:   point on J involves points at infinity\n";
      return false, _;
    end if;
    facta := Factorization(apol);
    // Compute image on analytic Jacobian
    try
      vec := &+[e[2]*&+[ToAnalyticJacobian(r[1], Evaluate(bpol, r[1]), AJ) : r in Roots(e[1], CC)]
                : e in facta];
    catch e
      vprintf JacHypEnd, 1: "EndomorphismAction:   error %o in ToAnalyticJacobian\n", e`Object;
      return false, _;
    end try;
    // move back to a divisor on the curve
    vec := alphaC*vec;
    try
      list := FromAnalyticJacobian(vec, AJ);
    catch e
      vprintf JacHypEnd, 1: "EndomorphismAction:   error %o in FromAnalyticJacobian\n", e`Object;
      return false, _;
    end try;
    if #list ne 2 then
      return false, _;
    end if;
    // Recognize the effective degree 2 divisor
    x1, y1 := Explode(list[1]);
    x2, y2 := Explode(list[2]);
    if Abs(x1 - x2) lt 0.1^(Precision(CC) div 2) then
      if Abs(y1 - y2) lt 0.1^(Precision(CC) div 2) then
        // twice the same point
        xc := BestApproximation(Real(x1), htbd);
        yc := BestApproximation(Real(y1), htbd);
        if Evaluate(f, xc) ne yc^2 then
          vprintf JacHypEnd, 1: "EndomorphismAction:   point not in J(Q) [equal points]\n";
          return false, _;
        end if;
        lin := Polynomial([-xc, 1]);
        return true, elt<J | lin^2, yc + Evaluate(Derivative(f), xc)/2*lin, 2>;
      elif Abs(y1 + y2) lt 0.1^(Precision(CC) div 2) then
        // zero
        return true, J!0;
      else
        vprintf JacHypEnd, 1: "EndomorphismAction:   point not in J(Q) [equal x-coordinates]\n";
        return false, _;
      end if;
    else
      a0 := BestApproximation(Real(x1*x2), htbd);
      a1 := -BestApproximation(Real(x1 + x2), htbd);
      apol := Polynomial([a0, a1, 1]);
      facta := Factorization(apol);
      if #facta eq 2 then
        x1 := BestApproximation(Real(x1), htbd);
        x2 := BestApproximation(Real(x2), htbd);
        y1 := BestApproximation(Real(y1), htbd);
        y2 := BestApproximation(Real(y2), htbd);
        b0 := (y1*x2 - y2*x1)/(x2 - x1);
        b1 := (y2 - y1)/(x2 - x1);
        try
          pt := elt<J | Polynomial([a0, a1, 1]), Polynomial([b0, b1]), 2>;
          return true, pt;
        catch e
          vprintf JacHypEnd, 1: "EndomorphismAction:   point not in J(Q) [two rat'l points]\n";
          return false, _;
        end try;
      else
        pts := Points(J, apol, 2);
        if IsEmpty(pts) then
          vprintf JacHypEnd, 1: "EndomorphismAction:   point not in J(Q) [wrong apol]\n";
          return false, _;
        end if;
        yseq := [[Evaluate(pt[2], x1), Evaluate(pt[2], x2)] : pt in pts];
        diffs := [Min(Norm(e[1]-y1) + Norm(e[2]-y2), Norm(e[1]-y2) + Norm(e[2]-y1))
                    : e in yseq];
        min, pos := Min(diffs);
        if min gt 0.1^(Precision(CC) div 2) then
          vprintf JacHypEnd, 1: "EndomorphismAction:   point not in J(Q) [generic case]\n";
          return false, _;
        end if;
        return true, pts[pos];
      end if;
    end if;
  end function;
  // Height bound for result is Floor(Exp(hf*htP + hc))
  htP := CanonicalHeight(P);
  if IsZero(htP) then
    vprintf JacHypEnd, 1: "EndomorphismAction: WARNING: P is torsion.\n";
  end if;
  hf := Max([r[1]^2 : r in Roots(CharacteristicPolynomial(alpha), RealField())]);
  hc := HeightConstant(J);
  vprintf JacHypEnd, 1: "EndomorphismAction: h^(P) = %o, hf = %o, hc = %o\n",
                        ChangePrecision(htP, 5), ChangePrecision(hf, 5), ChangePrecision(hc, 5);
  // First try with P directly.
  htbd := 10*Floor(Exp(hf*htP + hc));
  flag, aP := act_on_AJ(P, htbd);
  if flag then
    vprintf JacHypEnd, 1: "EndomorphismAction: n = 1 successful --> %o\n", aP;
    return aP;
  end if;
  // Write P = (n+1)*P - n*P for n = 0, 1, ... until everything works.
  success := false;
  n := 1;
  anP := J!0;
  nP := 2*P;
  while n lt max do
    n +:= 1;
    if IsZero(nP) then
      vprintf JacHypEnd, 1: "EndomorphismAction: WARNING %o * P = 0\n", n;
    end if;
    htbd := 10*Floor(Exp(hf*n^2*htP + hc));
    vprintf JacHypEnd, 1: "EndomorphismAction: n = %o; htbd = %o ...\n", n, htbd;
    if success then old := anP; end if;
    flag, anP := act_on_AJ(nP, htbd);
    if success and flag then
      aP := anP - old;
      vprintf JacHypEnd, 1: "EndomorphismAction: n = %o successful --> %o\n", n, aP;
      return aP;
    end if;
    success := flag;
    nP +:= P;
  end while;
  error "EndomorphismAction: no success!";
end intrinsic;


intrinsic EndomorphismRingActionOnMordellWeilGroup(J::JacHyp) -> Map
{ Returns the action of the chosen generator of End(J) on the Mordell-Weil group J(\Q). }

  // Avoid recomputing stuff (which can change data).
  if assigned J`alpha_JQfree then
    assert assigned J`project_onto_free_part and assigned J`JQ and assigned J`JQ_to_J;
    return J`alpha_JQfree;
  end if;
  // compute the Mordell-Weil group of J
  if not assigned J`JQ then
    vprintf HeegnerPoint, 2: "Computing Mordell-Weil group of %o ... ", J;
    JQ, JQ_to_J := MordellWeilGroupGenus2(J : Rankbound := 2);
    vprintf HeegnerPoint, 2: "done.\n";
    assert TorsionFreeRank(JQ) eq 2;
    J`JQ := JQ;
    J`JQ_to_J := JQ_to_J;
  else
    JQ := J`JQ;
    JQ_to_J := J`JQ_to_J;
  end if;

  JQfree, m := FreeAbelianQuotient(JQ);
  r := #Generators(JQfree);
  mordell_weil_free_basis := [(JQfree.i)@@m@JQ_to_J : i in [1..r]]; // basis of the free part of J(\Q)
  alphaPs := [EndgenAction(P) : P in mordell_weil_free_basis]; // image of the free basis elements under the actin of the endomorphism alpha generating End
  phi_alpha := Matrix(Integers(), r,r, [Eltseq(alphaP@@JQ_to_J@m) : alphaP in alphaPs]);

  // endom as endomorphism of JQ_free
  phi_alpha_JQfree := [&+[phi_alpha[i,j]*JQfree.j : j in [1..r]]: i in [1..r]];
  alpha_JQfree := hom<JQfree -> JQfree | phi_alpha_JQfree>;
  J`alpha_JQfree := alpha_JQfree;
  J`project_onto_free_part := m;
  return alpha_JQfree;
end intrinsic;

// Produce elements of the maximal order from field elements
function integral_elements(a)
  pol := MinimalPolynomial(a);
  den := LCM([Denominator(c) : c in Coefficients(pol)]);
  if Degree(pol) eq 1 then
    // no interesting information
    return [Parent(a)|];
  elif den eq 1 then
    // a is already integral
    return [a];
  else
    // scale minimal polynomial to have integral coefficients;
    // if pol = c_n*x^n + ... + c_0, then
    // c_n*a^k + c_{n-1}*a^{k-1} + ... + c_{n-k+1}*a is integral for all 1 <= k < n
    cofs := Reverse(ChangeUniverse(Coefficients(den*pol), Integers()));
    result := [Parent(a)| ];
    b := Parent(a)!cofs[1];
    for k := 1 to Degree(pol) - 1 do
      b *:= a;
      Append(~result, b);
      b +:= cofs[k+1];
    end for;
    return result;
  end if;
end function;

function max_order(elements)
  K := Universe(elements);
  /*time O := Order(&cat[integral_elements(a) : a in [K.1] cat elements]);
  time OK := MaximalOrder(O);*/
  O := Order(&cat[integral_elements(a) : a in [K.1] cat elements]);
  OK := MaximalOrder(O);
  return OK;
end function;

function EndKernelAJPts(J, mat : prec := 100)
  // find the points in the kernel of mat as points on the analytic Jacobian
  if not assigned J`Endgen or Precision(BaseField(J`AnalyticJacobian)) lt prec then
    vprintf JacHypEnd, 1: "Computing endomorphism ring at precision %o...\n", prec;
    alpha := ChangeRing(EndomorphismRingGenus2(J : Precision := prec), Integers());
    vprintf JacHypEnd, 1: "... done.\n";
  else
    alpha := ChangeRing(J`Endgen, Integers());
  end if;
  AJ := J`AnalyticJacobian;
  CC := BaseField(AJ);
  alphaC := ChangeRing(alpha, CC);
  // Verify that mat is in the endomorphism ring
  mat := ChangeRing(mat, Integers());
  minpol := MinimalPolynomial(alpha);
  basis := [alpha^j : j in [0..Degree(minpol)-1]];
  error if not IsConsistent(Matrix([Eltseq(b) : b in basis]), Vector(Eltseq(mat))),
          "mat does not seem to specify an endomorphism";
  // Find kernel of mat on analytic Jacobian.
  bpm := BigPeriodMatrix(AJ);
  mat_bpm := ChangeRing(mat, CC)*bpm;
  alpha_bpm := alphaC*bpm;
  bpmext := Matrix(&cat[[[Real(bpm[i,j]) : j in [1..Ncols(bpm)]],
                         [Imaginary(bpm[i,j]) : j in [1..Ncols(bpm)]]]
                         : i in [1..Nrows(bpm)]]);
  mat_bpmext := Matrix(&cat[[[Real(mat_bpm[i,j]) : j in [1..Ncols(mat_bpm)]],
                             [Imaginary(mat_bpm[i,j]) : j in [1..Ncols(mat_bpm)]]]
                         : i in [1..Nrows(mat_bpm)]]);
  alpha_bpmext := Matrix(&cat[[[Real(alpha_bpm[i,j]) : j in [1..Ncols(alpha_bpm)]],
                             [Imaginary(alpha_bpm[i,j]) : j in [1..Ncols(alpha_bpm)]]]
                         : i in [1..Nrows(alpha_bpm)]]);
  MC := bpmext^-1*mat_bpmext;
  MCalpha := bpmext^-1*alpha_bpmext;
  M := Matrix([[Round(Real(MC[i,j])) : j in [1..Ncols(MC)]] : i in [1..Nrows(MC)]]);
  Malpha := Transpose(Matrix(Rationals(),
              [[Round(Real(MCalpha[i,j])) : j in [1..Ncols(MCalpha)]] : i in [1..Nrows(MCalpha)]]));
  assert MinimalPolynomial(M) eq MinimalPolynomial(mat); // sanity check
  assert MinimalPolynomial(Malpha) eq MinimalPolynomial(alpha);
  // Find representatives of the nontrivial points in the kernel
  L := Lattice(ChangeRing(Transpose(M), Rationals())^-1);
  qL, qLmap := quo<L | Lattice(IdentityMatrix(Rationals(), 4))>;
  vprintf JacHypEnd, 1: "EndKernelDivisors: kernel has invariants %o\n", Invariants(qL);
  reps := [<q, q @@ qLmap> : q in qL];
  return [r[1] : r in reps], [bpm*Transpose(Matrix(ChangeRing(r[2], CC))) : r in reps],
         hom<qL -> qL | [((q @@ qLmap)*Malpha) @ qLmap : q in OrderedGenerators(qL)]>, AJ;
//   reps1 := reps[2..#reps]; // remove 0
//   ptsAJ := [ZeroMatrix(CC, 2, 1)] cat [bpm*Transpose(Matrix(ChangeRing(r[2], CC))) : r in reps];
//   return qL, ptsAJ, map<Set(qL) -> Set(ptsAJ) | [<reps[i,1], ptsAJ[i]> : i in [1..#reps]]>,
//                     map<Set(ptsAJ) -> Set(qL) | [<ptsAJ[i], reps[i,1]> : i in [1..#reps]]>,
//                     hom<qL -> qL | [((q @@ qLmap)*Malpha) @ qLmap : q in OrderedGenerators(qL)]>,
//                     AJ;
end function;

intrinsic EndKernelDivisors(J::JacHyp, mat::AlgMatElt : prec := 100) -> GrpAb, SeqEnum, Map
{ This constructs the geometric points in the kernel of the endomorphism
  of the genus 2 Jacobian J over Q given by mat.
  The first return value is the kernel as an abstract group,
  the second return value are the points as a set of sequences of pairs of complex coordinates
  specifying the divisors corresponding to the points.
  The third return value is a map from the abstract group to the set. }
  // Find representatives of the nontrivial points in the kernel
  ker, ptsAJ, action, AJ := EndKernelAJPts(J, mat : prec := prec);
  // and represent them as effective divisors of degree 2 over CC.
  vprintf JacHypEnd, 1: "EndKernelDivisors: converting analytic points into divisors...\n";
  function FAJ(pt)
    try res := FromAnalyticJacobianXYZ(pt, AJ);
    catch e
      return [];
    end try;
    return res;
  end function;
  divisors := [FAJ(pt) : pt in ptsAJ];
  vprintf JacHypEnd, 1: "... done.\n";
  return ker, divisors, action;
end intrinsic;

intrinsic EndPreimageDivisors(pt::JacHypPt, mat::AlgMatElt : prec := 100) -> SeqEnum
{ This constructs the geometric points in the preimage of pt under the endomorphism
  of the genus 2 Jacobian J over Q given by mat, as numerical approximations to divisors
  over the complex numbers (given as a sequence of projective coordinate tuples). }
  J := Parent(pt);
  // Find representatives of the nontrivial points in the kernel
  kerseq, ptsAJ, action, AJ := EndKernelAJPts(J, mat : prec := prec);
  CC := BaseField(AJ);
  matC := ChangeRing(mat, CC);
  // Find preimage of pt under mat on analytic Jacobian.
  ptAJ := ToAnalyticJacobianMumford(pt, AJ);
  preim := matC^-1*ptAJ;
  return [FromAnalyticJacobianXYZ(preim + ptAJ, AJ) : ptAJ in ptsAJ];
end intrinsic;

function div_to_mumford(plist, f)
  // Convert a divisor on a curve of genus 2, given as a sequence of length at most 2
  // of triples <x,y,z> with z = 0 or z = 1,
  // into the coefficients <[a0, a1, a2], [b0, b1, b2, b3], d> of the associated
  // Mumford representation.
  if IsEmpty(plist) then return <[1, 0, 0], [0, 0, 0, 0], 0>; end if;
  assert #plist le 2;
  CC := Parent(plist[1,1]);
  inf := [pt : pt in plist | pt[3] eq 0];
  fin := [pt : pt in plist | pt[3] eq 1];
  assert #inf + #fin eq #plist;
  PCC := PolynomialRing(CC);
  fCC := PCC!f;
  apol := &*[PCC| PCC.1 - pt[1] : pt in fin];
  if #fin eq 2 then
    x1, y1 := Explode(fin[1]);
    x2, y2 := Explode(fin[2]);
    if Abs(x1 - x2) lt 0.1^(0.5*Precision(CC)) then
      b1 := &+[Coefficient(fCC, j)*&+[CC| x1^k*x2^(j-1-k) : k in [0..j-1]] : j in [1..6]]/(y1+y2);
    else
      b1 := (y1 - y2)/(x1 - x2);
    end if;
    b0 := y1 - b1*x1;
    return <[Coefficient(apol, j) : j in [0..2]], [b0, b1, 0, 0], 2>;
  elif #fin eq 1 and #inf eq 1 then
    return <[Coefficient(apol, j) : j in [0..2]], [fin[1,2] - inf[1,2]*fin[1,1]^3, 0, 0, inf[1,2]], 2>;
  elif #inf eq 2 then
    return <[Coefficient(apol, j) : j in [0..2]], [0, 0, Coefficient(fCC, 5)/2/inf[1,2], inf[1,2]], 2>;
  elif #fin eq 1 then
    return <[Coefficient(apol, j) : j in [0..2]], [fin[1,2], 0, 0, 0], 1>;
  else // #fin = 0, #inf = 1
    error "this case should not occur";
  end if;
end function;

function get_Qpol(seq, B)
  // guess the polynomial over Q whose roots are the entries of seq
  polCC := &*[Polynomial(Universe(seq), [-t, 1]) : t in seq];
  // Make sure the coefficients are numerically real.
  assert Max([Abs(Im(c)) : c in Coefficients(polCC)]) lt 0.1^(Precision(Universe(seq))/5);
  return Polynomial([BestApproximation(Re(c), B) : c in Coefficients(polCC)]);
end function;

function mum_to_pt(a, b, J)
  d := Degree(b) eq 3 select 2 else Degree(a);
  try
    pt := elt<J | a, b, d>;
    return [pt];
  catch e
    return [J| ];
  end try;
end function;

function dist(pt1, pt2)
  return &+[Abs(pt1[1,j]-pt2[1,j]) : j in [1..3]] + &+[Abs(pt1[2,j]-pt2[2,j]) : j in [1..4]]
             + Abs(pt1[3] - pt2[3]);
end function;

function recognize_alg_points(pts, J : reps := false)
  // pts: a sequence of triples <apol_coeffs, bpol_coeffs, d>
  //      encoding Mumford representations of complex approximations to a
  //      Galois-stable set of points on J (a genus 2 Jacobian over Q)
  prec := Precision(Universe(pts[1,1]));
  B := 10^(prec div 3);
  a0pol := get_Qpol([m[1,1] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: a0pol =\n  %o\n", a0pol;
  a1pol := get_Qpol([m[1,2] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: a1pol =\n  %o\n", a1pol;
  a2pol := get_Qpol([m[1,3] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: a2pol =\n  %o\n", a2pol;
  b0pol := get_Qpol([m[2,1] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: b0pol =\n  %o\n", b0pol;
  b1pol := get_Qpol([m[2,2] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: b1pol =\n  %o\n", b1pol;
  b2pol := get_Qpol([m[2,3] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: b2pol =\n  %o\n", b2pol;
  b3pol := get_Qpol([m[2,4] : m in pts], B);
  vprintf JacHypEnd, 2: "EndKernel: b3pol =\n  %o\n", b3pol;
  if IsSquarefree(b0pol) then
    pol := b0pol;
    vals := [m[2,1] : m in pts];
  elif IsSquarefree(b1pol) then
    pol := b1pol;
    vals := [m[2,2] : m in pts];
  else
    b0b1pol := get_Qpol([m[2,1] + m[2,2] : m in pts], B);
    if IsSquarefree(b0b1pol) then
      pol := b0b1pol;
      vals := [m[2,1] + m[2,2] : m in pts];
    else
      b0b3pol := get_Qpol([m[2,1] + m[2,4] : m in pts], B);
      if IsSquarefree(b0b3pol) then
        pol := b0b3pol;
        vals := [m[2,1] + m[2,4] : m in pts];
      else
        b0b2pol := get_Qpol([m[2,1] + m[2,3] : m in pts], B);
        if IsSquarefree(b0b2pol) then
          pol := b0b2pol;
          vals := [m[2,1] + m[2,3] : m in pts];
        else
          bd := 1;
          repeat
            cofs := [Random(-bd, bd) : i in [1..7]];
            vals := [&+[cofs[i]*m[1,i] : i in [1..3]] + &+[cofs[3+i]*m[2,i] : i in [1..4]] : m in pts];
            pol := get_Qpol(vals, B);
            bd +:= 1;
          until IsSquarefree(pol);
//           error "No squarefree polynomial found";
        end if;
      end if;
    end if;
  end if;
  va0pol := get_Qpol([vals[i] + pts[i][1,1] : i in [1..#pts]], B);
  va1pol := get_Qpol([vals[i] + pts[i][1,2] : i in [1..#pts]], B);
  va2pol := get_Qpol([vals[i] + pts[i][1,3] : i in [1..#pts]], B);
  vb0pol := get_Qpol([vals[i] + pts[i][2,1] : i in [1..#pts]], B);
  vb1pol := get_Qpol([vals[i] + pts[i][2,2] : i in [1..#pts]], B);
  vb2pol := get_Qpol([vals[i] + pts[i][2,3] : i in [1..#pts]], B);
  vb3pol := get_Qpol([vals[i] + pts[i][2,4] : i in [1..#pts]], B);

  function get_cof(rt, cands, i, j)
    // rt a root of pol, cands a sequence of candidates for pt[i,j]
    // return the cand that is closest to the numerical value corresponding to rt
    if #cands eq 1 then return cands[1]; end if;
    rtC := Conjugate(rt, 1);
    min, pos := Min([Abs(rtC - v) : v in vals]);
    target := pts[pos][i,j];
    min, pos := Min([Abs(Conjugate(c, 1) - target) : c in cands]);
    return cands[pos];
  end function;

  function get_pt(rt)
    // rt a root of pol
    K := Parent(rt);
    JK := BaseChange(J, K);
    PK := PolynomialRing(K);
    a0 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(va0pol, K), Evaluate(a0pol, PK.1-rt)), K)], 1, 1);
    a1 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(va1pol, K), Evaluate(a1pol, PK.1-rt)), K)], 1, 2);
    a2 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(va2pol, K), Evaluate(a2pol, PK.1-rt)), K)], 1, 3);
    b0 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(vb0pol, K), Evaluate(b0pol, PK.1-rt)), K)], 2, 1);
    b1 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(vb1pol, K), Evaluate(b1pol, PK.1-rt)), K)], 2, 2);
    b2 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(vb2pol, K), Evaluate(b2pol, PK.1-rt)), K)], 2, 3);
    b3 := get_cof(rt, [r[1] - rt : r in Roots(GCD(ChangeRing(vb3pol, K), Evaluate(b3pol, PK.1-rt)), K)], 2, 4);
    points := mum_to_pt(Polynomial([a0, a1, a2]), Polynomial([b0, b1, b2, b3]), JK);
    if IsEmpty(points) then
      vprintf JacHypEnd, 1: "no point found for root %o\n", rt;
      return false, _;
    else
      return true, points[1];
    end if;
  end function;

  if reps then
    fpol := Factorization(pol);
    result := [* *];
    for e in fpol do
      K := NumberField(e[1]);
      assert Evaluate(e[1], K.1) eq 0;
      flag, pt := get_pt(K.1);
      if flag then
        Append(~result, pt);
      else
        return false, _;
      end if;
    end for;
    return true, result;
  else
    K := SplittingField(pol);
    JK := BaseChange(J, K);
    result := [JK| ];
    for r in Roots(pol, K) do
      flag, pt := get_pt(r[1]);
      if flag then
        Append(~result, pt);
      else
        return false, _;
      end if;
    end for;
    return true, result;
  end if;
end function;

function recognize_subgroup(m)
  // m: a map from the set of elements of a finite abelian group
  //    to the points over K of some hyperelliptic Jacobian
  // checks whether the map is a homomorphism
  ker := Universe(Domain(m));
  J := Codomain(m);
  gens := OrderedGenerators(ker);
  invs := Invariants(ker);
  genpts := [m(g) : g in gens];
  if not forall{i : i in [1..#invs] | invs[i]*genpts[i] eq J!0} then
    vprintf JacHypEnd, 1: "EndKernel: orders don't match\n";
    return false;
  end if;
  if not forall{k : k in ker | &+[s[j]*genpts[j] : j in [1..#s]] eq m(k) where s := Eltseq(k)} then
    vprintf JacHypEnd, 1: "EndKernel: relations not valid\n";
    return false;
  end if;
  return true;
end function;

intrinsic EndKernel(J::JacHyp, mat::AlgMatElt : prec := 50) -> Map
{ Find the points in the kernel of the endomorphism given by mat on the analytic Jacobian
  as algebraic points. }
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  success := false;
  while not success do
    success := true;
    vprintf JacHypEnd, 1: "EndKernel: using precision %o\n", prec;
    kerseq, divseq := EndKernelDivisors(J, mat : prec := prec);
    // move to Mumford rep.
    mumseq := [div_to_mumford(d, f) : d in divseq];
    flag, all_points := recognize_alg_points(mumseq, J);
    success and:= flag;
    if success then
      K := BaseField(Universe(all_points));
      JK := BaseChange(J, K);
      // match
      approx := [<[Conjugate(Coefficient(pt[1], j), 1) : j in [0..2]],
                  [Conjugate(Coefficient(pt[2], j), 1) : j in [0..3]], pt[3]> : pt in all_points];
      ker_to_pts := map<Set(kerseq) -> JK |
                        [<kerseq[i], all_points[pos]> where _, pos := Min([dist(mumseq[i], pt) : pt in approx])
                           : i in [1..#kerseq]]>;
      success and:= recognize_subgroup(ker_to_pts);
    end if;
    prec *:= 2;
  end while;
  return ker_to_pts;
end intrinsic;

intrinsic EndPreimages(pt::JacHypPt, mat::AlgMatElt : kermap := 0, prec := 50) -> SeqEnum, Map
{ Given a rational point on a genus 2 Jacobian J and an endomorphism of J given
  by the matrix of its action on the complex tangent space at the origin,
  determine the set of preimages of the point under the endomorphism. }
  J := Parent(pt);
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  if kermap cmpeq 0 then
    kermap := EndKernel(J, mat : prec := prec);
  end if;
  ker := Universe(Domain(kermap));
  success := false;
  while not success do
    success := true;
    vprintf JacHypEnd, 1: "EndPreimages: using precision %o\n", prec;
    divseq := EndPreimageDivisors(pt, mat : prec := prec);
    // move to Mumford rep.
    mumseq := [div_to_mumford(d, f) : d in divseq];
    flag, all_points := recognize_alg_points(mumseq, J : reps);
    success and:= flag;
    // TODO: check that the points form a coset
    prec *:= 2;
  end while;
  return all_points;
end intrinsic;

intrinsic KernelChars(J::JacHyp, mat::AlgMatElt : minprec := 100) -> List
{ Find the characters occurring in the Galois representation J[pr], where pr is a
  prime ideal of norm a prime p in the endomorphism ring. }
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  htbd := HeightConstant(J : Modified);
  mat := ChangeRing(mat, Integers());
  p := Abs(Determinant(mat));
  assert IsPrime(p);
  // Height bound for coefficients of polQ below:
  cofbd := (p+1)*(Log(p-1) + (p-1)/2*htbd);
  // Use sufficient precision.
  prec := Max(minprec, 2*Ceiling(cofbd/Log(10)) + 50);
  vprintf JacHypEnd, 1: "KernelChars: asking for precision %o\n", prec;
  // First find the projective representation
  ker, divseq := EndKernelDivisors(J, mat : prec := prec);
  // Check that the kernel is an F_p-vector space.
  assert p eq Exponent(Universe(ker));
  // move to Mumford rep.
  mumseq := [div_to_mumford(d, f) : d in divseq];
  // Set prec to precision actually used (which may be larger than the precision given).
  CC := Parent(mumseq[1,1,1]);
  prec := Precision(CC);
  vprintf JacHypEnd, 1: "KernelChars: actual precision is %o\n", prec;
  // Determine generators of the one-dimensional subspaces.
  function test(g)
    if g eq Parent(g)!0 then return false; end if;
    s := Eltseq(g);
    i := 1;
    while s[i] eq 0 do i +:= 1; end while;
    return s[i] eq 1;
  end function;
  subgens := [g : g in ker | test(g)];
  // partition points into one-dimensional subgroups
  p2 := p div 2;
  subgroups := [[mumseq[Position(ker, n*g)] : n in [1..p2]] : g in subgens];
  // find a function on the a-polynomials that separates
  function check(c0, c1)
    // consider the trace of c0*a0 + c1*a1 on the subgroups
    traces := [&+[c0*m[1,1] + c1*m[1,2] : m in mseq] : mseq in subgroups];
    bd := Ceiling(100*Max([Abs(c0), Abs(c1)])^(p+1)*Exp(cofbd));
    polQ := get_Qpol(traces, bd);
    return IsSquarefree(polQ), polQ, traces;
  end function;
  c0 := 1; c1 := 0;
  flag, polQ, traces := check(c0, c1);
  if not flag then
    c0 := 0; c1 := 1;
    flag, polQ, traces := check(c0, c1);
  end if;
  bd := 1;
  while not flag do
    bd +:= 1;
    c0 := Random(-bd, bd);
    c1 := Random(-bd, bd);
    if c0 ne 0 or c1 ne 0 then
      flag, polQ, traces := check(c0, c1);
    end if;
  end while;
  polQrts := [r[1] : r in Roots(polQ)];
  if #polQrts eq 0 then
    vprintf JacHypEnd, 1: "KernelChars: representation is irreducible\n";
  elif #polQrts eq 2 then
    vprintf JacHypEnd, 1: "KernelChars: representation is split\n";
  elif #polQrts eq 1 then
    vprintf JacHypEnd, 1: "KernelChars: representation is reducible, non-semisiple\n";
  else
    error "inconsistent number of rational fixed points on P(kernel)";
  end if;
  // Function for extracting Galois character acting on a one-dim'l F_p-vector space.
  function find_char(rt)
    // rt is a rational trace
    // recognize algebraic points in the subspace
    min, pos := Min([Abs(t - rt) : t in traces]);
    assert min lt 0.1^(prec div 2);
    subgen := subgens[pos];
    ptseq := [mumseq[Position(ker, n*subgen)] : n in [0..p-1]];
    flag, points := recognize_alg_points(ptseq, J);
    assert flag;
    K := BaseField(Universe(points));
    if Degree(K) eq 1 then
      return DirichletGroup(1, GF(p))!1;
      vprintf JacHypEnd, 1: "KernelChars: points defined over Q\n";
    else
      OK := LLL(max_order(&cat[Coefficients(pt[1]) cat Coefficients(pt[2]) : pt in points]));
      i := 1;
      while Degree(MinimalPolynomial(OK.i)) ne Degree(K) do i +:= 1; end while;
      Kold := K;
      K := NumberField(MinimalPolynomial(OK.i));
      flag, Kold_to_K := IsIsomorphic(Kold, K); assert flag;
      JK := BaseChange(J, K);
      points := [elt<JK | Polynomial([K| Kold_to_K(c) : c in Coefficients(pt[1])]),
                          Polynomial([K| Kold_to_K(c) : c in Coefficients(pt[2])]),
                          pt[3]> : pt in points];
      assert IsDivisibleBy(p-1, Degree(K)) and IsAbelian(K);
      Kab := AbelianExtension(K);
      cond, cond_inf := Conductor(Kab);
      _, cond := IsPrincipal(cond);
      cond := Integers()!cond;
      vprintf JacHypEnd, 1: "KernelChars: points defined over field of degree %o and conductor %o\n",
                            Degree(K), cond;
      // check that points form a subgroup
      i := points[1] eq JK!0 select 2 else 1;
      gen := points[i];
      posseq := [Position(points, n*gen) : n in [0..p-1]];
      assert Set(posseq) eq {1..p};
      // set up logarithm map
      logpt := map<Set(points) -> GF(p) | [<n*gen, GF(p)!n> : n in [0..p-1]]>;
      // embed into cyclotomic field
      L := NumberField(CyclotomicPolynomial(cond));
      flag, KtoL := IsSubfield(K, L); assert flag;
      // Set up suitable group of Dirichlet characters.
      D := DirichletGroup(cond, GF(p));
      U, mU := UnitGroup(Integers(cond));
      // Set up automorphisms generating the Galois group.
      Ugens := [Integers()!mU(u)  : u in OrderedGenerators(U)];
      autsL := [hom<L -> L | L.1^u> : u in Ugens];
      autsK := [hom<K -> K | K.1 @ KtoL @ a @@ KtoL> : a in autsL];
      // Find action on gen.
      act_on_pt := func<aut, pt | elt<JK | Polynomial([aut(c) : c in Coefficients(pt[1])]),
                                           Polynomial([aut(c) : c in Coefficients(pt[2])]),
                                           pt[3]>>;
      act := [logpt(act_on_pt(a, gen)) : a in autsK];
      chars := [ch : ch in Elements(D) | forall{i : i in [1..#Ugens] | ch(Ugens[i]) eq act[i]}];
      assert #chars eq 1;
      return chars[1];
    end if;
  end function;
  // shortcut
  if #polQrts eq 1 and IsDivisibleBy(#TorsionSubgroup(J), p) then
    return [* DirichletGroup(1, GF(p))!1 *];
  else
    return [* find_char(r) : r in polQrts *];
  end if;
end intrinsic;

intrinsic Chars(J::JacHyp, p::RngIntElt) -> SeqEnum
{ Find the characters corresponding to the one-dimensional subrepresentations of
  the Galois representations J[pr], where pr is a prime ideal above the non-inert
  prime p.}
  endgen, OtoE := EndomorphismRingGenus2(J);
  O := Domain(OtoE);
  prs := [e[1] : e in Decomposition(O, p)];
  assert forall{pr : pr in prs | Degree(pr) eq 1}; // split or ramified
  gens := [g where _, g := IsPrincipal(pr) : pr in prs];
  mats := [ChangeRing(OtoE(g), Integers()) : g in gens];
  return [<mat, KernelChars(J, mat)> : mat in mats];
end intrinsic;


intrinsic ProjIm(J::JacHyp, p::RngIntElt : minprec := 100) -> GrpPerm
{ Assuming that p is an inert prime in the real quadratic endomorphism ring of J,
  determine the image of the Galois group in PGL_2(F_p²) determined by the action
  on J[p]. }
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  htbd := HeightConstant(J : Modified);
  mat := p*IdentityMatrix(Integers(), 2);
  assert IsPrime(p);
  // Height bound for coefficients of polQ below:
  cofbd := (p^2+1)*(Log(p^2-1) + (p^2-1)/2*htbd);
  // Use sufficient precision.
  prec := Max(minprec, 2*Ceiling(cofbd/Log(10)) + 50);
  vprintf JacHypEnd, 1: "ProjIm: asking for precision %o\n", prec;
  kerseq, divseq, alpha_map := EndKernelDivisors(J, mat : prec := prec);
  ker := Universe(kerseq);
  // Check that the kernel is an F_p-vector space.
  assert p eq Exponent(ker);
  // move to Mumford rep.
  mumseq := [div_to_mumford(d, f) : d in divseq];
  // Set prec to precision actually used (which may be larger than the precision given).
  CC := Parent(mumseq[1,1,1]);
  prec := Precision(CC);
  vprintf JacHypEnd, 1: "ProjIm: actual precision is %o\n", prec;
  subgens := [];
  temp := Exclude(Set(ker), ker!0);
  while not IsEmpty(temp) do
    g := Rep(temp);
    ga := alpha_map(g);
    gmults := {i*g + j*ga : i, j in [0..p-1] | i ne 0 or j ne 0};
    temp diff:= gmults;
    Append(~subgens, gmults);
  end while;
  assert #subgens eq p^2 + 1; // #P^1(F_{p^2})
  // partition points into one-dimensional subgroups
  subgroups := [[mumseq[Position(kerseq, g)] : g in s] : s in subgens];
  // find a function on the a-polynomials that separates
  function check(c0, c1)
    // consider the trace of c0*a0 + c1*a1 on the subgroups
    traces := [&+[c0*m[1,1] + c1*m[1,2] : m in mseq] : mseq in subgroups];
    bd := Ceiling(100*Max([Abs(c0), Abs(c1)])^(p+1)*Exp(cofbd));
    polQ := get_Qpol(traces, bd);
    return IsSquarefree(polQ), polQ, traces;
  end function;
  c0 := 1; c1 := 0;
  flag, polQ, traces := check(c0, c1);
  if not flag then
    c0 := 0; c1 := 1;
    flag, polQ, traces := check(c0, c1);
  end if;
  bd := 1;
  while not flag do
    bd +:= 1;
    c0 := Random(-bd, bd);
    c1 := Random(-bd, bd);
    if c0 ne 0 or c1 ne 0 then
      flag, polQ, traces := check(c0, c1);
    end if;
  end while;
  return GaloisGroup(polQ), polQ;
end intrinsic;
