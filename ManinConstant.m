import "RealPeriod.m": RealLatticeArea;

declare verbose ManinConstant, 3;

intrinsic ManinConstant(C::CrvHyp, f::ModFrmElt : prec := 30, max_prec := 100, UseRiemannSurface := false) -> RngIntElt
{ Computes the Manin constant c_pi*c_f of J by identifying the space of newforms with the space of differentials on a hyperelliptic curve. }
    g := Genus(C);

    // big period matrix of J
    if UseRiemannSurface then
        _<x,y> := PolynomialRing(Rationals(), 2);
        Cmin := MinimalWeierstrassModel(C);
        J := RiemannSurface(Evaluate(DefiningPolynomial(Cmin), [x,y,1]) : Precision := prec);
    else
        J := AnalyticJacobian(C : Precision := prec);
    end if;
    bpmJ := BigPeriodMatrix(J);

    // big period matrix of A_f
    S := f`mod_sym;
    bpmAf := BigPeriodMatrix(S, Precision(bpmJ[1,1]));

    // isogeny A_f(C) -> J(C) induced by alpha: C^g -> C^g
    bpmAf := ChangeRing(bpmAf, BaseRing(bpmJ));
    flag, M, alpha := IsIsogenousPeriodMatrices(bpmAf, bpmJ);
    if flag then
      vprintf ManinConstant, 2: "period matrices are isogenous";
      vprintf ManinConstant, 2: " by an isogeny of degree %o\n", Abs(Determinant(M));
    else
      new_prec := Ceiling(prec * 1.5);
      vprintf ManinConstant, 1: "no isogeny found with precision %o, increasing precision to %o ...\n",
                               prec, new_prec;
      return $$(C, f : prec := new_prec, max_prec := max_prec, UseRiemannSurface := UseRiemannSurface);
    end if;

    // compute big period matrix of cusp forms in S_2(f, Z). If f, f^sigma are the newforms, then the basis is (f+f^sigma)/2, (f-f^sigma)/(2sqrt(disc(O))
/*    require g eq 2: "genus must be 2";
    //O := CoefficientRing(f);
    //discO := Discriminant(O);
    bpmAfa := bpmAf;//Matrix(Parent(bpmAf[1,1]), g,2*g, [(bpmAf[1] + bpmAf[2])/2, (bpmAf[1] - bpmAf[2])/(2)]);

    // c_f * c_pi = index of lattice determined by corr * M * Omega_J in that of bpmAfa.
    // the index is the quotient of the real volumes of fundamental domains of the lattices
    pullbackbpmJ := bpmJ * ChangeRing(M, Parent(bpmJ[1,1]));
    pullbackOmegaJ := RealLatticeArea(Matrix([[ 2*Real(pullbackbpmJ[i][j]) : i in [1..g]] : j in [1..2*g]]));*/
    try
        corr := CompensationFactor(C);
        vprintf ManinConstant, 1: "Compensation factor = %o\n", corr;
    catch e
        printf "ERROR in CompensationFactor: %o\n", e;
        printf "using corr = 1 instead.\n";
        corr := 1;
    end try;
    /*pullbackOmegaJ *:= corr;
    OmegaAf := RealLatticeArea(Matrix([[ 2*Real(bpmAfa[i][j]) : i in [1..g]] : j in [1..2*g]]));
    return pullbackOmegaJ / OmegaAf;*/

    return Round(Abs(Determinant(alpha)) * corr);
end intrinsic;
