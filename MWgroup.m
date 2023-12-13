function covering_radius_ub(mat, scale)
  // mat:   a pos. def. symm, matrix of size n over a real field,
  // scale: a positive integer.
  // Returns an upper bound on the covering radius of the lattice
  // with Gram matrix mat.
  n := Nrows(mat);
  // scale entries by scale and round off-diagonal entries
  //  --> max. error <= 1/2
  // so add (n-1)/2 to diagonal entries and take the ceiling
  L := LatticeWithGram(Matrix([[i eq j select Ceiling(mat[i,j]*scale + (n-1)/2)
                                       else Round(mat[i,j]*scale)
                                  : j in [1..n]] : i in [1..n]]));
  // scaling the Gram matrix scales the (square of the) covering radius
  // by the same amount
  return CoveringRadius(L)/scale;
end function;

function successive_minima_lb(mat, scale)
  // mat:   a pos. def. symm, matrix of size n over a real field,
  // scale: a positive integer.
  // Returns a sequence containing lower bounds
  // on the successive minima of mat.
  n := Nrows(mat);
  repeat
    // Approximate as above, but subtracting from the diagonal.
    // Refine if necessary to get a positive definite matrix.
    sc := scale;
    mat1 := Matrix([[i eq j select Floor(mat[i,j]*scale - (n-1)/2)
                            else Round(mat[i,j]*scale)
                      : j in [1..n]] : i in [1..n]]);
    scale *:= 2;
  until IsPositiveDefinite(mat1);
  L := LatticeWithGram(mat1);
  return [m/sc : m in SuccessiveMinima(L)];
end function;

// Find all points of canonical height below a given bound
// in the subgroup generated by bas and the torsion.
function points_of_bounded_height(bas, hmat, T, mT, bound)
  // bas:   sequence of independent points in J(Q)
  // hmat:  the height pairing matrix of bas
  // T, mT: as returned by TorsionSubgroup(J)
  // bound: a positive real number

  // Returns all points of canonical height <= bound in the group generated
  // by bas and the torsion, as a set.

  // Find the sufficiently short vectors in the relevant lattice.
  sv := [[Round(c) : c in Eltseq(e[1])]
           : e in ShortVectors(LatticeWithGram(hmat), bound)];
  // Now produce the relevant linear combinations.
  tors := {mT(t) : t in T}; // the set of torsion points
  result := tors;
  for v in sv do
    pt := &+[Universe(bas)| v[i]*bas[i] : i in [1..#bas]];
    result join:= {t + pt : t in tors};
    result join:= {t - pt : t in tors};
  end for;
  return result;
end function;

intrinsic IsDivisibleBy2(pt::JacHypPt) -> BoolElt, JacHypPt
{ Decide whether pt is of the form 2*pt2. If so, return pt2 as second value. }
  // Use the duplication map on the Kummer surface.
  // This is slow, but works over any exact field.
  J := Parent(pt);
  K := KummerSurface(J);
  delta := K`Delta;
  eqns := Minors(Matrix(Universe(delta), [delta, Eltseq(K!pt)]), 2);
  halves := Points(Scheme(ProjectiveSpace(Universe(eqns)), Append(eqns, K`Equation)));
  halvesJ := &join[Points(J, K!Eltseq(h)) : h in halves];
  flag := exists(pt2){pt2 : pt2 in halvesJ | 2*pt2 eq pt};
  if flag then
    return true, pt2;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic MWSaturate(pts::[JacHypPt], MaxBound::RngIntElt : Raw := false)
  -> GrpAb, Map, BoolElt
{ Saturate the subgroup of the universe J of pts (the Jacobian variety of a
  curve of genus 2 over Q of the form y^2 = f(x)). }
  J := Universe(pts);
  C := Curve(J);
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The underlying curve must be of the form y^2 = f(x)";
  require BaseField(C) cmpeq Rationals(): "The Jacobian must be defined over the rationals";
  // Compute torsion subgroup
  T, mT := TorsionSubgroup(J);
  // Saturate
  success := false;
  hc, hc2 := HeightConstant(J : Modified);
  vprintf MordellWeilGroup, 1:
          "Height difference bound is %o.\n", ChangePrecision(hc, 5);
  // Find covering radius if rank is small.
  if Raw then
    bas := pts;
    hmat := HeightPairingMatrix(bas);
  else
    bas, hmat := ReducedBasis(pts);
  end if;
  if IsEmpty(bas) then
    success := true;
  elif #bas le 6 then
    // Compute an upper bound on the covering radius.
    cr := 1.0*covering_radius_ub(hmat, 2^10);
    vprintf MordellWeilGroup, 1:
            "The MW lattice has (squared) covering radius <= %o.\n",
            ChangePrecision(cr, 5);
    // Compute the multiplicative height bound necessary to get generators.
    satbd := Floor(Exp(hc + cr));
    if satbd le MaxBound then
      // Search for points on J
      vprintf MordellWeilGroup, 1:
              "Search for points up to height %o to saturate...\n", satbd;
      oldhmat := hmat;
      points := Points(J : Bound := satbd, ReturnAll);
      vprintf MordellWeilGroup, 1:
              "Found %o point%o.\n",
              #points, #points eq 1 select "" else "s";
      // Remove points that are already in the known subgroup.
      vprintf MordellWeilGroup, 2: "  Generating known points...\n";
      vtime MordellWeilGroup, 2:
            known := points_of_bounded_height(bas, hmat, T, mT,
                                              Log(satbd) + hc2 + 2.0);
      points := [pt : pt in points | pt notin known];
      vprintf MordellWeilGroup, 2:
              "  ... %o new point%o remaining.\n",
              #points, #points eq 1 select "" else "s";
      if not IsEmpty(points) then
        bas, hmat := ReducedBasis(bas cat points);
        if IsVerbose("MordellWeilGroup") then
          index := Round(Sqrt(Determinant(oldhmat)/Determinant(hmat)));
          if index gt 1 then
            printf "Saturation enlarges group by index %o\n", index;
          end if;
        end if;
      end if;
      success := true;
    end if;
  end if; // IsEmpty(bas) / #bas le 6
  // At this point, success is (still) false
  // when satbd is greater than MaxBound.
  if not success then
    // Try to get a good bound on the index of the known subgroup
    // inside J(Q).
    if hc ge Log(MaxBound) then
      // Give up when we cannot determine the set of points in J(Q)
      // of canonical height bounded by any positive epsilon.
      vprintf MordellWeilGroup, 1:
              "The height constant is too large: saturation not possible.\n";
    else
      // We are allowed to search up to MaxBound, so do that.
      vprintf MordellWeilGroup, 1:
              "Search for points up to height %o to saturate...\n",
              MaxBound;
      oldhmat := hmat;
      points := Points(J : Bound := MaxBound, ReturnAll);
      vprintf MordellWeilGroup, 1:
              "Found %o point%o.\n",
              #points, #points eq 1 select "" else "s";
      // Remove points that are already in the known subgroup.
      vprintf MordellWeilGroup, 2: "  Generating known points...\n";
      vtime MordellWeilGroup, 2:
            known := points_of_bounded_height(bas, hmat, T, mT,
                                              Log(MaxBound) + hc2 + 2.0);
      points := [pt : pt in points | pt notin known];
      vprintf MordellWeilGroup, 2:
              "  ... %o new point%o remaining.\n",
              #points, #points eq 1 select "" else "s";
      if not IsEmpty(points) then
        bas, hmat := ReducedBasis(bas cat points);
        if IsVerbose("MordellWeilGroup") then
          index := Round(Sqrt(Determinant(oldhmat)/Determinant(hmat)));
          if index gt 1 then
            printf "This leads to a larger group by index %o.\n", index;
          end if;
        end if;
      end if;
      // Get lower bounds for the successive minima
      // of the lattice of known points.
      sm := successive_minima_lb(hmat, 2^10);
      // B is a lower bound for the canonical height
      // up to which we know all points.
      B := Log(MaxBound) - hc;
      vprintf MordellWeilGroup, 1:
              "We know all points up to canonical height %o.\n",
              ChangePrecision(B,5);
      // Compute the bound on the index using the Hermite constant
      // and the successive mins.
      indexbound := Floor(Sqrt(Determinant(hmat)*HermiteConstant(#bas)
                                / &*[Min(m,B) : m in sm]));
      vprintf MordellWeilGroup, 1:
              "We obtain an index bound of %o.\n\n", indexbound;
      p := 2;
      // Now saturate at all primes up to indexbound
      while p le indexbound do
        vprintf MordellWeilGroup, 1: "Saturating at p = %o...\n", p;
        oldhmat := hmat;
        bas := Saturation(bas, p : Raw);
        hmat := HeightPairingMatrix(bas);
        if IsVerbose("MordellWeilGroup") then
          index := Round(Sqrt(Determinant(oldhmat)/Determinant(hmat)));
          if index gt 1 then
            printf "  --> we get a larger group by index %o.\n", index;
            // update indexbound
            sm := successive_minima_lb(hmat, 2^10);
            indexbound := Floor(Sqrt(Determinant(hmat)*HermiteConstant(#bas)
                                / &*[Min(m,B) : m in sm]));
            vprintf MordellWeilGroup, 1:
            "We obtain a new index bound of %o.\n\n", indexbound;
          end if;
        end if;
        p := NextPrime(p);
      end while;
      success := true;
    end if;
  end if; // not success

  // Now construct return values.
  // Set up the Mordell-Weil group as an abstract abelian group.
  MW := AbelianGroup(Invariants(T) cat [0 : b in bas]);
  // Set up the map from the abstract group into J(Q).
  // The following are the points on J corresponding to the generators.
  // The map will compute the correct linear combination.
  gens := [mT(t) : t in OrderedGenerators(T)] cat bas;
  // Set up the inverse map from J(Q) to the abstract MW group.
  // This uses the height pairing.
  hpmati := HeightPairingMatrix(bas : Precision := 30)^-1;
  // We need the inverse of mT, which we obtain by enumeration (T is small).
  mTinv := map<{mT(t) : t in T} -> T | [<mT(t), t> : t in T]>;
  // This is the inverse function:
  function JtoMW(pt)
    if not IsEmpty(bas) then
      // Project to the free part using the height pairing.
      vec := Vector([HeightPairing(pt, b : Precision := 30) : b in bas]);
      vec := ChangeRing(vec, BaseRing(hpmati))*hpmati; // work-around for annoying bug
      cofs := [Round(vec[i]) : i in [1..#bas]];
      pttors := pt - &+[cofs[i]*bas[i] : i in [1..#bas]];
    else
      pttors := pt;
      cofs := [Integers()| ];
    end if;
    if Order(pttors) gt 0 then
      return MW!(Eltseq(mTinv(pttors)) cat cofs);
    elif Height(pttors : Precision := 30) lt 0.5*Height(pt : Precision := 30) then
      // Repeat with the new candidate
      // (the first attempt might have failed because of precision problems).
      return JtoMW(pttors) + MW!(Eltseq(T!0) cat cofs);
    else
      error "JtoMW: failed to find preimage in MW";
    end if;
  end function;
  // Put both functions together in a map<...>
  MWtoJ := map<MW -> J | a :-> &+[J| s[i]*gens[i] : i in [1..#s]] where s := Eltseq(a),
                         pt :-> JtoMW(pt)>;

  return MW, MWtoJ, success;
end intrinsic;

intrinsic MordellWeilGroupJK(J::JacHyp, pts::[JacHypPt] : MaxBound := 10000)
  -> GrpAb, Map, BoolElt, GrpAb, Map, GrpAb, Map
{ Compute the Mordell-Weil group of J, the Jacobian variety of a genus 2 curve over Q
  of the form y^2 = f(x), base-changed to a quadratic number field K.
  pts is a sequence of points on J that generate a finite-index subgroup. }
  K := BaseField(J);
  require Degree(K) eq 2: "Jacobian must be defined over a quadratic field.";
  f, h := HyperellipticPolynomials(Curve(J));
  require h eq 0: "The curve must be of the form y^2 = f(x).";
  require forall{c : c in Coefficients(f) | c in Rationals()}:
          "The Jacobian must be base-changed from one over the rationals.";
  fQ := PolynomialRing(Rationals())!f;
  CQ := HyperellipticCurve(fQ);
  JQ := Jacobian(CQ);
  D := SquarefreeFactorization(Discriminant(Integers(K)));
  sqrtD := Roots(Polynomial(K, [-D, 0, 1]))[1,1];
  Ctw := QuadraticTwist(CQ, D);
  Jtw := Jacobian(Ctw);
  JQtoJ := map<JQ -> J | pt :-> J!pt>;
  JtwtoJ := map<Jtw -> J | pt :-> elt<J | ChangeRing(pt[1], K), ChangeRing(pt[2], K)/sqrtD, pt[3]>>;
  // projections
  conjpol := func<pol | Parent(pol)![tau(c) : c in Coefficients(pol)]>
              where tau := Automorphisms(K)[2];
  conj := map<J -> J | pt :-> elt<J | conjpol(pt[1]), conjpol(pt[2]), pt[3]>>;
  JtoJQ := map<J -> JQ | pt :-> JQ!(pt + conj(pt))>;
  JtoJtw := map<J -> Jtw | pt :-> elt<Jtw | Parent(fQ)!pt1[1], Parent(fQ)!(pt1[2]*sqrtD), pt1[3]>
                                   where pt1 := pt - conj(pt)>;
  // Determine Mordell-Weil groups of J and J^D over Q.
  MW, MWtoJQ, fl := MWSaturate(ReducedBasis([JtoJQ(pt) : pt in pts]), MaxBound);
  MWtw, MWtoJtw, fltw := MWSaturate(ReducedBasis([JtoJtw(pt) : pt in pts]), MaxBound);
  JK2, JK2toJK := TwoTorsionSubgroup(J);
  JKtoJK2 := pmap<J -> JK2 | [<JK2toJK(t), t> : t in JK2]>;
  // Find the maps J(Q)[2] -~-> J^D(Q)[2] and J(Q)[2] --> J(K)[2].
  J2 := Kernel(hom<MW -> MW | [2*m : m in OrderedGenerators(MW)]>);
  J2toJtw := hom<J2 -> MWtw | [(Jtw!(MWtoJQ(t))) @@ MWtoJtw : t in OrderedGenerators(J2)]>;
  J2toJK2 := hom<J2 -> JK2 | [JKtoJK2(J!(MWtoJQ(t))) : t in OrderedGenerators(J2)]>;
  // Take direct sum of groups modulo these identifications.
  DS, injs, projs := DirectSum([MW, MWtw, JK2]);
  MWK, q := quo<DS | [injs[1](t) - injs[2](J2toJtw(t)) : t in OrderedGenerators(J2)]
                       cat [injs[1](t) - injs[3](J2toJK2(t)) : t in OrderedGenerators(J2)]>;
  bas := [JQtoJ(MWtoJQ(projs[1](lift))) + JtwtoJ(MWtoJtw(projs[2](lift))) + JK2toJK(projs[3](lift))
            where lift := gen @@ q
           : gen in OrderedGenerators(MWK)];
  MWKtoJ := map<MWK -> J | m :-> &+[J| s[j]*bas[j] : j in [1..#s]] where s := Eltseq(m)>;
  // We have isogenies inducing maps
  // a : J(Q) + J^D(Q) --> J(K)  and  b : J(K) --> J(Q) + J^D(Q), P |--> (P+P', P-P'),
  // where P' is the image of P under the nontrivial automorphism of K.
  // Both compositions are multiplication by 2. This gives exact sequences
  //  0 --> J(Q)[2] --> J(Q)[2] + J^D(Q)[2] --> ker(b)
  //    --> coker(a) --> J(Q)/2J(Q) + J^D(Q)/2J^D(Q) --> coker(b) --> 0  and
  //  0 --> ker(b) --> J(K)[2] -b-> J(Q)[2] --> coker(b) --> J(K)/2J(K) --> coker(a) --> 0 .
  // In particular, the cokernel of b is killed by 2.
  // So we just need to find out which elements in the image of MWKtoJ are divisible by 2.
  MWKmod2, q2 := quo<MWK | 2*MWK>;
  known_subgroup := sub<MWKmod2 | >;
  generators := [Parent(<MWK!0, J!0>)| ];
  remaining := {m : m in MWKmod2 | m ne MWKmod2!0};
  while not IsEmpty(remaining) do
    new := Rep(remaining);
    lift := new @@ q2;
    flag, half := IsDivisibleBy2(MWKtoJ(lift));
    if flag then
      // enlarge known subgroup
      Append(~generators, <lift, half>);
      known_subgroup := sub<MWKmod2 | known_subgroup, new>;
      // we know about everything in the subgroup
      remaining := {r : r in remaining | r notin known_subgroup};
    else
      // we know that the full coset of new w.r.t. known_subgroup
      // is not divisible by 2
      remaining diff:= {new + s : s in known_subgroup};
    end if;
  end while;
  // Enlarge MWK.
  new_part := FreeAbelianGroup(#generators);
  newtoJ := map<new_part -> J | m :-> &+[J| s[j]*generators[j,2] : j in [1..#s]] where s := Eltseq(m)>;
  DS, inj1, inj2, pr1, pr2 := DirectSum(MWK, new_part);
  MWKnew, qnew := quo<DS | [inj1(generators[j,1]) - 2*inj2(new_part.j) : j in [1..#generators]]>;
  basnew := [MWKtoJ(pr1(lift)) + newtoJ(pr2(lift)) where lift := g @@ qnew
              : g in OrderedGenerators(MWKnew)];
  MWtoMWKnew := injs[1]*q*inj1*qnew;
  MWtwtoMKnew := injs[2]*q*inj1*qnew;
  MWKdouble := hom<MWKnew -> MWKnew | [2*m : m in OrderedGenerators(MWKnew)]>;
  tors := Kernel(MWKdouble);
  inverse :=  function(pt)
                // Use projections
                inMW := JtoJQ(pt) @@ MWtoJQ;
                inMWtw := JtoJtw(pt) @@ MWtoJtw;
                double_in_MWKnew := MWtoMWKnew(inMW) + MWtwtoMKnew(inMWtw);
                half := double_in_MWKnew @@ MWKdouble;
                halves := [half + t : t in tors];
                for h in halves do
                  image := &+[J| s[j]*basnew[j] : j in [1..#s]] where s := Eltseq(h);
                  if image eq pt then
                    return h;
                  end if;
                end for;
                error "problem in inverse map for MordellWeilGroupJK";
              end function;
  MWKnewtoJ := map<MWKnew -> J | m :-> &+[J| s[j]*basnew[j] : j in [1..#s]] where s := Eltseq(m),
                                 pt :-> inverse(pt)>;
  return MWKnew, MWKnewtoJ, fl and fltw, MW, MWtoJQ, MWtw, MWtoJtw;
end intrinsic;