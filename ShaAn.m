// Compute #Sha(J/Q)_an exactly

import "HeegnerPoint.m": quotBPM, matConj;

// Find newform corresponding to a genus 2 curve with RM Jacobian of given level
intrinsic find_f(C::CrvHyp, N::RngIntElt) -> ModFrmElt, ModSym
{ Compute a newform associated to C of level N and the modular symbols space. }
    // C: genus 2 curve
    // N: level

    // determine representatives of all Galois orbits of size 2 of newforms at level N
    nf := [* e[1] : e in Newforms(CuspForms(N)) | #e eq 2 *];

    // for an increasing sequence of primes l not dividing disc(C),
    // compare the traces of a_l(f) with the relevant coefficient of the zeta function of C
    disc := Integers()!Discriminant(C);
    l := 1;
    repeat
      repeat l := NextPrime(l); until not IsDivisibleBy(disc, l);
      Tl := Numerator(ZetaFunction(BaseChange(C, Bang(Rationals(), GF(l)))));
      trC := -Coefficient(Tl, 1);
      nf := [* f : f in nf | trC eq Trace(Coefficient(f, l)) *];
      error if IsEmpty(nf), "no matching newform found";
    until #nf eq 1;
    f := nf[1];

    S := NewSubspace(CuspidalSubspace(ModularSymbols(N,2,0)));
    S := Kernel([<p, MinimalPolynomial(Coefficient(f, p))> : p in PrimesUpTo(l)], S);
    if Dimension(S) ne 2 * Genus(C) then
        error "Dimension(S) ne 2 * Genus(C): %o\n", Dimension(S);
    end if;
    f`mod_sym := S;
    return f, S;
end intrinsic;

// Given the big period matrix of an abelian variety A/Q (w.r.t. a Q-basis of H⁰(A, \Omega¹)),
// determine the M-matrix of complex conjugation
intrinsic ComplexConjugationOnHomology(bpm::Mtrx) -> AlgMatElt[RngInt]
{ Given a big period matrix, represent the action of complex conjugation on homology
  by an integral matrix. }
  M, err := quotBPM(bpm, matConj(bpm));
  if err ge 10^(5 - Precision(BaseRing(bpm))) then
    printf "ComplexConjugationOnHomology: err = %o, prec = %o\n",
            ChangePrecision(err, 6), Precision(BaseRing(bpm));
  end if;
//   assert err lt 10^(5 - Precision(BaseRing(bpm)));
  return M;
end intrinsic;


intrinsic KerAndCokerOfPiR(Mpi::AlgMatElt[RngInt], Mtau::AlgMatElt[RngInt]) -> GrpAb, GrpAb, GrpAb, GrpAb
{ Given the matrices M_pi of an isogeny pi : A --> B and M_tau of complex conjugation of B
  acting on the homology, compute the kernel and cokernel of pi on real points and the
  kernel and cokernel of the C/R-quadratic twist of pi on real points. }
  n := Nrows(Mpi);
  assert n eq Ncols(Mpi) and n eq Nrows(Mtau) and n eq Ncols(Mtau) and Mtau^2 eq Parent(Mtau)!1;
  Mpi := Transpose(Mpi);
  Mtau := Transpose(Mtau);
  A := FreeAbelianGroup(n);
  ker, qk := quo<A | [A!Eltseq(Mpi[j]) : j in [1..n]]>;
  im := sub<A | [A!Eltseq(Mpi[j]) : j in [1..n]]>;
  tau_p_id_on_A := hom<A -> A | [A.j + A!Eltseq(Mtau[j]) : j in [1..n]]>;
  tau_m_id_on_A := hom<A -> A | [-A.j + A!Eltseq(Mtau[j]) : j in [1..n]]>;
  tau_p_id_on_ker := hom<ker -> ker | [qk(tau_p_id_on_A(k @@ qk)) : k in OrderedGenerators(ker)]>;
  tau_m_id_on_ker := hom<ker -> ker | [qk(tau_m_id_on_A(k @@ qk)) : k in OrderedGenerators(ker)]>;
  kerR := Kernel(tau_m_id_on_ker);
  kerR_tw := Kernel(tau_p_id_on_ker);
  tau_p_id_on_im := hom<im -> A | [tau_p_id_on_A(g) : g in OrderedGenerators(im)]>;
  tau_m_id_on_im := hom<im -> A | [tau_m_id_on_A(g) : g in OrderedGenerators(im)]>;
  cokerR := quo<Kernel(tau_p_id_on_A) | Image(tau_m_id_on_A) + Kernel(tau_p_id_on_im)>;
  cokerR_tw := quo<Kernel(tau_m_id_on_A) | Image(tau_p_id_on_A) + Kernel(tau_m_id_on_im)>;
  return kerR, cokerR, kerR_tw, cokerR_tw;
end intrinsic;

intrinsic SizeOfRealTwoTorsion(C::CrvHyp) -> RngIntElt
{ Determine #J(R)[2], where J is the Jacobian variety of C. }
  f := HyperellipticPolynomials(SimplifiedModel(C));
  g := Genus(C);
  prec := 20;
  // Compute real roots to sufficient precision to separate them
  repeat
    prec +:= 10;
    rts := Roots(f, RealField(prec));
  until forall{e : e in rts | e[2] eq 1};
  d1 := #rts;                             // degree 1 irreducible factors
  d2 := ExactQuotient(Degree(f) - d1, 2); // degree 2 irreducible factors
  return IsOdd(Degree(f)) or d1 eq 0 select 2^(d1 + d2 - 1) else 2^(d1 + d2 - 2);
end intrinsic;

function tamagawa_number(C, p : n_tries := 10)
  try
    Cp := RegularModel(C, p);
    return TamagawaNumber(Cp), true;
  catch e
    if n_tries gt 0 then
      printf "c_%o(J/Q): trying again ...\n", p;
      return $$(C, p : n_tries := n_tries - 1);
    else
      printf "error %o in c_%o(J), using c_%o = 1 instead.\n", e, p, p;
      return 1, false;
    end if;
  end try;
end function;

function tamagawa_product(C, N)
  tam := 1;
  flag := true;
  for p in PrimeDivisors(N) do
    cp, fl := tamagawa_number(C, p);
    flag and:= fl;
    tam *:= cp;
  end for;
  return tam, flag;
end function;

function RealLatticeCovolume(M)
  // Given a big period matrix M, calculate the covolume of the lattice spanned by
  // the C/R-trace of its columns. We assume that the columns of the complex conjugate
  // matrix are integral linear combinations of the columns of M.
  g := Nrows(M);
  assert Ncols(M) eq 2*g;
  // get matrix of complex conjugation acting on the columns
  I := ComplexConjugationOnHomology(M);
  // multiply trace matrix (I + id) on the right so that last g columns are zero
  H := HermiteForm(Transpose(I) + Parent(I)!1);
  assert forall{j : j in [g+1..2*g] | H[j] eq Parent(H[1])!0};
  MH := Submatrix(M * ChangeRing(Transpose(H), BaseRing(M)), 1, 1, g, g);
  err := 10.0^(5-Precision(BaseRing(M)));
  assert forall{j : j in [1..g], i in[1..g] | Abs(Imaginary(MH[i,j])) lt err};
  MH := Matrix([[Real(MH[i,j]) : j in [1..g]] : i in [1..g]]);
  return Abs(Determinant(MH));
end function;

MyPrec := Precision;

intrinsic LRatio(f::ModFrmElt, bpm::ModMatFldElt) -> FldRatElt
{ Computes the quotient  prod_sigma L(f^sigma, 1) / Omega,  where sigma runs through
  the complex embeddings of the base ring of f and Omega is the real period associated
  to the big period matrix bpm. }
  N := Level(f);
  K := BaseField(f);
  d := Degree(K);

  prec := Precision(BaseRing(bpm));
  // Set up L-series manually:
  //   determine number of coefficients needed
  n2 := LCfRequired(LSeries(2, [0,1], N, 0 : Sign := +1, Precision := prec));
  //   compute the relevant coefficients of f
  cofs := Coefficients(qExpansion(f, n2 + 1));
  // trailing zeros are removed when applying Coefficients :-(
  cofs cat:= [K| 0 : n in [#cofs+1..n2]];

  // Construct the L-series of f^sigma
  Ls := [LSeries(2, [0,1], N,
                 [Conjugate(cofs[n], j : Precision := prec+5) : n in [1..n2]]
                  : Sign := 1, Precision := prec)
          : j in [1..d]];

  vprintf HeegnerPoint, 2: "required coefficients for L-series: %o\n", n2;
  vprintf HeegnerPoint, 2: "Evaluating L(f, 1) to precision %o ...\n", prec;
  Lval := &*[Evaluate(L, 1) : L in Ls];
  // big period matrix of A_f
  period := RealLatticeCovolume(bpm);
  LR := Lval/period;
  pol := MinimalPolynomial(ChangePrecision(LR, prec-5), 1);
  q := -Coefficient(pol, 0)/Coefficient(pol, 1);
//   printf "LR = %o, q = %o\n", LR, q;
  assert Abs(LR - q) lt 10^(5-prec);
  return q;
end intrinsic;

intrinsic LRatioTwisted(f::ModFrmElt, D::RngIntElt, bpm::ModMatFldElt) -> FldRatElt
{ Computes the quotient  prod_sigma L(f_D^sigma, 1) / Omega_D,  where sigma runs through
  the complex embeddings of the base ring of f, f_D is the quadratic twist of f by D, and
  Omega_D is the real period associated to the D-twist of the big period matrix bpm.  }

  N := Level(f);
  K := BaseField(f);
  d := Degree(K);
  // The quadratic character we twist by
  chi_K := BaseChange(KroneckerCharacter(D), Rationals());

  prec := Precision(BaseRing(bpm));
  // Set up L-series manually:
  //   determine number of coefficients needed
  n2 := LCfRequired(LSeries(2, [0,1], N*D^2, 0 : Sign := +1, Precision := prec));
  //   compute the relevant coefficients of f
  cofs := Coefficients(qExpansion(f, n2 + 1));
  // trailing zeros are removed when applying Coefficients :-(
  cofs cat:= [K| 0 : n in [#cofs+1..n2]];

  // Construct the L-series of f^sigma and the twisted version
  Ls := [LSeries(2, [0,1], N*D^2,
                 [chi_K(n)*Conjugate(cofs[n], j : Precision := prec+5) : n in [1..n2]]
                  : Sign := 1, Precision := prec)
          : j in [1..d]];

  vprintf HeegnerPoint, 2: "required coefficients for twisted L-series: %o\n", n2;
  vprintf HeegnerPoint, 2: "Evaluating L(f_D, 1) to precision %o ...\n", prec;
  Lval := &*[Evaluate(L, 1) : L in Ls];
  // big period matrix of twisted A_f
  bpmtw := bpm/Sqrt(BaseRing(bpm)!D);
  period := RealLatticeCovolume(bpmtw);
  LR := Lval/period;
  pol := MinimalPolynomial(ChangePrecision(LR, prec-5), 1);
  q := -Coefficient(pol, 0)/Coefficient(pol, 1);
//   printf "LR = %o, q = %o\n", LR, q;
  assert Abs(LR - q) lt 10^(5-prec);
  return q;
end intrinsic;

intrinsic ShaAnRk0(C::CrvHyp, N::RngIntElt : D := 0, Tamseq := 0) -> FldRatElt
{ Compute the analytic order of Sha(J/Q), where J is the Jacobian variety of the
  genus 2 curve C and there is a newform f of weight 2 and level N such that A_f is
  isogenous to J.
  If D ne 0, compute the analytic order of Sha(J^D/Q). }
  S := ModularSymbolsSpaceFromCurve(C : N := N);
  bpmseq, alphaseq, Mseq := DiagramData(C, N); // TODO: check if we need to compute this for the twist!
//   LR := LRatio(S, 1); // use numerical approach instead
  f := NewformFromCurve(C : N := N);
  LR := D eq 0 select LRatio(f, bpmseq[2]) else LRatioTwisted(f, D, bpmseq[2]);
  // bpmseq = [bpmAfdual, bpmAf, bpmJ]
  // alphaseq = [Id, alpha_pi_Z, alpha_gen, alpha_Z],
  // Mseq = [imat, M_pi, M_gen, M_round]
  flag := true;
  assert D eq 0 or Gcd(2*N, D) eq 1;
  try
    corr := CompensationFactor(C); // same for twist by Lemma 3.1.6 and Cor. 4.5.6 if (D_K,2N) = 1
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
  kerpiR, cokerpiR := KerAndCokerOfPiR(Mpi, Mtau);
  if Tamseq cmpeq 0 then
    tam, fl := tamagawa_product(C, N);
  else
    tam := &*[Integers()| e[2] : e in Tamseq];
    fl := true;
  end if;
  if D ne 0 then
    for p in PrimeDivisors(D) do // Primes dividing D are bad for the twist!
        try
            Cp := BaseChange(C, Bang(Rationals(), GF(p)));
            tam *:= #TwoTorsionSubgroup(Jacobian(Cp));
        catch e
            Ctw := QuadraticTwist(C, D);
            cp, correct := tamagawa_number(Ctw, p);
            tam *:= cp;
            if not correct then
                fl := false;
            end if;
        end try;
    end for;
  end if;
  flag and:= fl;
  if D ne 0 then
    C := QuadraticTwist(C, D);
  end if;
  J := Jacobian(C);
  Jtors := #TorsionSubgroup(J);
  printf "ShaAnRk0:\nLR = %o, C = %o, cfcpi = %o, #ker = %o, #coker = %o, #tors = %o, Tam = %o\n",
         LR, corr, cfcpi, #kerpiR, #cokerpiR, Jtors, tam;
  return LR/cfcpi*#kerpiR/#cokerpiR*Jtors^2/tam, flag;
end intrinsic;

// LRatio on the twisted spaces seems to be infeasible:
// the first example (N = 67, D = -7) exhausts the memory of my laptop

intrinsic ShaAnRk1(C::CrvHyp, N::RngIntElt : Tamseq := 0, D := 0, I := 0, MWtoJ := 0)
  -> FldRatElt, BoolElt, FldRatElt, RngIntElt
{ Compute the analytic order of Sha(J/Q), where J is the Jacobian variety of the
  genus 2 curve C and there is a newform f of weight 2 and level N such that A_f is
  isogenous to J. }
  bpmseq, alphaseq, Mseq, ainO, _, f := DiagramData(C, N);
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
  JR2 := SizeOfRealTwoTorsion(C);
  if Tamseq cmpeq 0 then
    tam, fl := tamagawa_product(C, N);
    flag and:= fl;
  else
    tam := &*[Integers()| e[2] : e in Tamseq];
  end if;
  if D eq 0 or I eq 0 or MWtoJ cmpeq 0 then
    I, D, L_is_zero_at_1, rt, _, MWtoJ := HeegnerIndexJ(C, f);
    assert L_is_zero_at_1;
  else
    discA := Discriminant(BaseRing(f));
    discJ := Discriminant(Parent(ainO));
    flag, rt := IsSquare(discA/discJ); assert flag;
  end if;
  LR := LRatioTwisted(f, D, bpmseq[2]);
  JK := Codomain(MWtoJ);
  K := BaseField(JK);
  PK := PolynomialRing(K);
  autK_pol := hom<PK -> PK | hom<K -> PK | -K.1>, PK.1>;
  MW := Domain(MWtoJ);
  atr_MW := hom<MW -> MW | [(pt - elt<JK | autK_pol(pt[1]), autK_pol(pt[2]), pt[3]>) @@ MWtoJ
                              where pt := MWtoJ(g)
                              : g in OrderedGenerators(MW)]>;
  JK_JQ := Index(MW, Kernel(atr_MW));
  printf "ShaAnRk1:\nLR = %o, C = %o, cfcpi = %o, #ker = %o, #coker = %o, #J(R)[2] = %o, Tam = %o\n",
         LR, corr, cfcpi, #kerpiR, #cokerpiR, JR2, tam;
  printf "sqrt(disc Z[f] / disc O) = %o, I_{K,pi} = %o, (J(K):J(Q)) = %o\n",
         rt, I, JK_JQ;
  // note the fudge factor 16, which is the factor 4^g in Cor. 4.5.1.
  return 16*#cokerpiR/#kerpiR/JR2/tam*(I*rt/JK_JQ)^2/cfcpi/LR, flag, LR, D;
end intrinsic;

intrinsic ShaAnOverK(C::CrvHyp, N::RngIntElt : Tamseq := 0, D := 0, I := 0, MWtoJ := 0) -> FldRatElt
{ Compute the analytic order of Sha(J/Q), where J is the Jacobian variety of the
  genus 2 curve C and there is a newform f of weight 2 and level N such that A_f is
  isogenous to J. }
  bpmseq, alphaseq, Mseq, ainO := DiagramData(C, N);
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
  f := NewformFromCurve(C : N := N);
  discZf := Discriminant(BaseRing(f));
  discO := Discriminant(Parent(ainO));
  JR2 := SizeOfRealTwoTorsion(C);
  if Tamseq cmpeq 0 then
    tam, fl := tamagawa_product(C, N);
    flag and:= fl;
  else
    tam := &*[Integers()| e[2] : e in Tamseq];
  end if;
  if D eq 0 or I eq 0 or MWtoJ cmpeq 0 then
    I, D, _, _, _, MWtoJ := HeegnerIndexJ(C, f);
  end if;
  JK := Codomain(MWtoJ);
  K := BaseField(JK);
  PK := PolynomialRing(K);
  autK_pol := hom<PK -> PK | hom<K -> PK | -K.1>, PK.1>;
  MW := Domain(MWtoJ);
  atr_MW := hom<MW -> MW | [(pt - elt<JK | autK_pol(pt[1]), autK_pol(pt[2]), pt[3]>) @@ MWtoJ
                              where pt := MWtoJ(g)
                              : g in OrderedGenerators(MW)]>;
  JK_JQ := Index(MW, Kernel(atr_MW));
  Sel := TwoSelmerGroup(JK);
  tors2K := TwoTorsionSubgroup(JK);
  printf "ShaAnOverK:\nC = %o, cfcpi = %o, Tam = %o, disc Z[f] = %o, disc O = %o, I_{K,pi} = %o\n",
         corr, cfcpi, tam, discZf, discO, I;
  printf "#Sha(J/K)[2] = %o\n", 2^(#Invariants(Sel) - #Invariants(tors2K) - 2);
  return discZf/discO*(I/tam/cfcpi)^2, flag;
end intrinsic;
