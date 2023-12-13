declare verbose CrvHypFromModAbVar, 3;

declare attributes JacHyp: newforms, Snew;

function SturmBound(N, k)
// Returns the Sturm bound for eigenforms of level N and weight k.
  return Ceiling(k/12.0 * N * &*[1 + 1/p : p in PrimeDivisors(N)]) + 1;
end function;

intrinsic SmallPeriodMatrixFromBigPeriodMatrix(P::Mtrx) -> Mtrx
{ Computes the small period matrix from a big one. }
  g := Nrows(P);
  require Ncols(P) eq 2*g: "P must be a g x 2g matrix.";
  A_f := Submatrix(P, 1,1,g,g);
  B_f := Submatrix(P, 1,g+1,g,g);
  //vprintf CrvHypFromModAbVar, 3: "A_f =\n%o\nB_f =\n%o\n", A_f, B_f;
  small_period_matrix := A_f^-1 * B_f;
  //vprintf CrvHypFromModAbVar, 3: "small_period_matrix =\n%o\n", small_period_matrix;
  return small_period_matrix;
end intrinsic;

intrinsic SmallPeriodMatrix(A::ModAbVar : CC := 0) -> Mtrx
{ Computes the small period matrix of the modular abelian variety A. }
  return SmallPeriodMatrixFromBigPeriodMatrix(BigPeriodMatrix(A : CC := CC));
end intrinsic;

/*
intrinsic HasTheSameNewformGaloisOrbitAs(C::CrvHyp, f::ModFrmElt) -> BoolElt
{ Returns L(C,s) = L(f,s)L(f^sigma,s) is Jac(C) is modular of dimension 2. }
  if Genus(C) ne 2 then
    print "C must be a genus 2 hyperelliptic curve";
    return false;
  end if;

  Nsquared := Conductor(C);
  is_square, N := IsSquare(Nsquared);
  if not is_square then
    vprintf CrvHypFromModAbVar, 2: "The conductor %o of C must be a square. Otherwise C does not have RM", Factorization(Nsquared);
    return false;
  end if;
  if N ne Level(f) then
    vprintf CrvHypFromModAbVar, 2: "The conductor %o^2 of C squared must equal the level of f", Factorization(N);
    return false;
  end if;

  // need enough coefficients of L(C,s)
  sturm_bound := SturmBound(N,2);
  _, OtoEnd := EndomorphismRingGenus2(Jacobian(C));
  Ef := Domain(OtoEnd);
  print Ef, CoefficientRing(f);
  if (Degree(NumberField(Ef)) ne 2) or (Discriminant(Ef) ne Discriminant(CoefficientRing(f))) then
    print "End(Jac(C)) is not isomorphic to the coefficient ring of f";
    return false;
  end if;

  Efx<x> := PolynomialRing(Ef);

  //printf "computing a_p with p <= %o ...", sturm_bound;
  coeffs := [];
  for p in [p : p in PrimesUpTo(sturm_bound)] do
    f_p := Factorization(Efx!Reverse(EulerFactor(C,p)))[1][1];
    // minimal polynomial of a_p
    // nur für Degree(f_p) eq 2; aber Discriminant(f_p) < 0 by Weil bounds
    coeffs cat:= [<p, MinimalPolynomial(-Coefficient(f_p, 1))>];
  end for;
  fs := Newforms(coeffs, CuspidalSubspace(ModularForms(N, 2)));
  if #fs ne 1 then
    print "Found more than 1 newform with the same Hecke eigenvalues up to Galois conjugacy.";
    return false;
  end if;
  // the Galois conjugates of f
  f_alphas := fs[1];
  assert IsNewform(f_alphas[1]);
  if #f_alphas ne 2 then
    print "The Galois orbit does not have 2 elements.";
    return false;
  end if;
  return true;
end intrinsic;*/

function FrobeniusPolynomialsOfCurve(C : N := 0, Ef := 0, bound := 0)
    // We can give the level of the newform(s) as an optional argument. If it is 0, compute the level.
    if N eq 0 then
      Ng := Conductor(C);
      N := Integers()!Root(Ng, Genus(C));
    end if;
  
    // need enough coefficients of L(C,s)
    if bound eq 0 then
      sturm_bound := SturmBound(N,2);
    else
      sturm_bound := bound;
    end if;
    if Ef cmpeq 0 then
      _, OtoEnd := EndomorphismRingGenus2(Jacobian(C));
      Ef := NumberField(Domain(OtoEnd)); //EndomorphismAlgebra(C);
    end if;
  
    Efx<x> := PolynomialRing(Ef);
  
    coeffs := [];
    for p in [p : p in PrimesUpTo(sturm_bound) | not IsDivisibleBy(N, p)] do
      try
        euler_p := Efx!Reverse(EulerFactor(C,p)); // this can raise an "Runtime error: Fibre blowups over number fields not yet implemented"
        f_p := Factorization(euler_p)[1][1];
        // minimal polynomial of a_p
        coeffs cat:= [<p, MinimalPolynomial(-Coefficient(f_p, 1))>];
        catch e
          continue; // ignore the primes p for which we cannot determine the Euler factor at p
        end try;
    end for;
    return coeffs;
end function;

intrinsic ModularSymbolsSpaceFromCurve(C::CrvHyp : N := 0) -> ModFrm
{ Returns the newforms f such that L(C,s) = L(f,s)L(f^sigma,s) if C is a genus 2
  curve with endomorphism algebra a real quadratic number field with
  non-trivial automorphism sigma. WORKS FOR ANY GENUS }
  if assigned C`Snew then
    return C`Snew;
  end if;
  coeffs := FrobeniusPolynomialsOfCurve(C : N := N);
  Snew := Kernel(coeffs, CuspidalSubspace(ModularSymbols(N, 2)));
  assert Dimension(Snew) eq 2 * Genus(C);
  C`Snew := Snew;
  if N ne 0 then
    C`Conductor := N;
  end if;
  return Snew;
end intrinsic;

intrinsic NewformSpaceFromCurve(C::CrvHyp : N := 0) -> ModFrm
{ Returns the newforms f such that L(C,s) = L(f,s)L(f^sigma,s) if C is a genus 2
  curve with endomorphism algebra a real quadratic number field with
  non-trivial automorphism sigma. WORKS FOR ANY GENUS }
  if assigned C`newforms then
    return C`newforms;
  end if;
  coeffs := FrobeniusPolynomialsOfCurve(C : N := N);
  fs := Newforms(coeffs, CuspidalSubspace(ModularForms(N, 2)));
  assert #fs eq 1;
  C`newforms := fs[1];
  if N ne 0 then
    C`Conductor := N;
  end if;
  return fs[1];
end intrinsic;

intrinsic NewformOrbitFromCurve(C::CrvHyp : N := 0) -> SeqEnum
{ Returns the newforms f such that L(C,s) = L(f,s)L(f^sigma,s) if C is a genus 2
  curve with endomorphism algebra a real quadratic number field with
  non-trivial automorphism sigma. }
  f_alphas := NewformSpaceFromCurve(C : N := N);
  assert IsNewform(f_alphas[1]);
  assert #f_alphas eq 2;
  return f_alphas;
end intrinsic;

intrinsic NewformFromCurve(C::CrvHyp : N := 0) -> ModFrmElt
{ Returns a newform f such that L(C,s) = L(f,s)L(f^sigma,s) if C is a genus 2
  curve with endomorphism algebra a real quadratic number field with
  non-trivial automorphism sigma. }
  return NewformOrbitFromCurve(C : N := N)[1];
end intrinsic;