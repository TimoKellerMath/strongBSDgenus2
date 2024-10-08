freeze;

/******************************************************************************

     Testing regularity of arithmetic surfaces

     Steve Donnelly, July 2009

******************************************************************************/

// TO DO: Intrinsics
// IsRegular(S, P)
// IsRegular(S, pt, P) ... ambiguity when pt is over an extension of O/P ?

debug := true;

import "main.m": pt_coords_from_ideal;

forward is_regular;

/***************************************************************************************
  BASIC STUFF
***************************************************************************************/

function field(O)
  if ISA(Type(O), RngOrd) then
    return NumberField(O);
  else
    return FieldOfFractions(O);
  end if;
end function;
/*
function integers(K)
  if ISA(Type(K), FldFunG) then 
    return MaximalOrderFinite(K);
  else
    return Integers(K);
  end if;
end function;
*/
function generators(I)
  gens := Generators(I);
  if Type(gens) eq SetEnum then
    gens := Setseq(gens);
  end if;
  return gens;
end function;

function pointlift(c, res) // tries to lift in smallest number field possible
  ord := Degree(MinimalPolynomial(c));
  if (ord eq 1) or (ord eq Degree(Parent(c))) then // in this case the current lifting should be alright
    return c@@res;
  end if;
  K := NumberField(Domain(res));
  L, iota := Explode([x : x in Subfields(K) | Degree(x[1]) eq ord][1]); // find smallest number field in which c could be lifted
  OL := MaximalOrder(L);
  P := ideal < OL | #PrimeField(Parent(c)) >;
  F, resL := ResidueClassField(P); // redefine restriction map on new number field
  
  for b in Roots(MinimalPolynomial(c), F) do
    blift := b[1]@@resL; // try all roots of minimal polynomial to see which one is the right one
    if res(iota(blift)) eq c then
      return Domain(res)!iota(blift);
    end if;
  end for;
  
  assert(false); // if none found, assertion error
end function;
  
function lift(c, res)  // returns c@@res ... TO DO: get c@@res to work in all these cases
  O := Domain(res);
  if ISA(Type(O), RngOrd) then return pointlift(c, res);
  elif ISA(Type(O), RngUPol) then return O!c; 
  else return c@@res; end if;
end function;

// Reduction and lifting of polys between Pol over O and kpol over k, via residue map res

function polyres(F, kpol, res) 
  if Type(F) eq SeqEnum then
    return [polyres(f, kpol, res) : f in F];
  elif Type(F) eq FldFunRatMElt then
    Fn := Numerator(F);
    Fd := Denominator(F);
    assert F eq Fn/Fd;
    return polyres(Fn, kpol, res)/polyres(Fd, kpol, res);
  end if;
  coeffs, mons := CoefficientsAndMonomials(F);
  return &+ [kpol| res(coeffs[i]) * kpol!mons[i] : i in [1..#mons]];
end function;

function polylift(f, Pol, res)
  if Type(f) eq RngUPolElt then // univariate 
    if Type(BaseRing(Pol)) in {RngUPol,FldFunRat} then 
      // work around: res has no inverse in RngUPol case
      return Pol!f;
    else 
      return Pol! [c@@res : c in Coefficients(f)];
    end if;
  else // multivariate
    coeffs, mons := CoefficientsAndMonomials(f);
    mons_lifted := [Monomial(Pol, Exponents(m)) : m in mons];
    return &+ [Pol| lift(coeffs[i],res) * mons_lifted[i] : i in [1..#mons]];
  end if;
end function;

// Find an extension by an irreducible polynomial whose residue equals pol.
// If special:=true, insist on special properties

function FindInertExtension(K, d, P : special := false, tries := Infinity())
  if (d eq 1) then
    return K, P, PrimeFactors(Discriminant(K));
  elif IsPrimePower(d) then
    p := PrimeFactors(d)[1];
    if not(Degree(K) eq 1) then
      if not(PrimeFactors(Degree(K)) eq [p]) then
        if Valuation(Degree(K), p) eq 0 then
          L1 := Rationals();
        else
          L1 := Subfields(K, p^Valuation(Degree(K), p))[1][1];
        end if;          
        L2 := Subfields(K, Degree(K) div p^Valuation(Degree(K), p))[1][1];
        M1, PM, ramification := FindInertExtension(L1, d, ideal< Integers(L1) | Generators(P) > : special := true, tries := tries);
        M := CompositeFields(M1, L2)[1];
        M := OptimizedRepresentation(M : Ramification := ramification);
        return M, ideal < Integers(M) | Generators(PM) >, ramification;
      end if;
    end if;
    L, PL, ramification := FindInertExtension(K, d div p, P : special := special, tries := tries);
    l, res := ResidueClassField(PL);
    m := ext<l | p>;
    polk := DefiningPolynomial(m, l);
    Pol := PolynomialRing(L);
    polO := polylift(polk, Pol, res);
    gensP := Generators(PL);
    //print "Making list...";
    bestDisc := Infinity();
    for j in [1..100000] do
      //print "j =", j;
      newpolO := polO + &+[Random({Pol|0,1,-1})*(Random(l)@@res)*Random(gensP) * Pol.1^i : i in [0..Degree(polk)-1]];
      newDisc := Integers() ! Abs(Norm(Discriminant(newpolO)));
      if newDisc le bestDisc then
        bestDisc := newDisc;
        polO := newpolO;
      end if;
    end for;
    //polOprimefactors := [Factorisation(Integers()!Norm(Discriminant(f)) : TrialDivisionLimit := 100000) : f in polOlist];
    //print [Max([i[1] : i in fact]) : fact in polOprimefactors];
    //m, ind := Min([Max([i[1] : i in fact]) : fact in polOprimefactors]);
    //print bestDisc;
    t := 0;


    while t le tries do
      if IsIrreducible(polO) then
        //print "Found", polO, Norm(Discriminant(ext<L | polO>));
        newramification := [fact[1] : fact in Factorisation(Norm(Discriminant(ext<L | polO>)) : Proof := false, ECMLimit := 200)];
        //print "Found ramification", newramification;
        M := OptimizedRepresentation(AbsoluteField(ext<L | polO>) : Ramification := ramification cat newramification);
        //print "Found", M;
        PM := ideal< Integers(M) | gensP >;
        return M, PM, ramification cat newramification;
      end if;
      polO +:= Random({Pol|1,-1})*Random(gensP) * Pol.1^Random(Degree(polk)-1);
    end while;
  else  
    M := K;
    ramification := [];
    for f in Factorisation(d : TrialDivisionLimit := 1000000) do
      L, PL, newramification := FindInertExtension(K, f[1]^f[2], P : special := special, tries := tries);
      ramification := ramification cat newramification;
      M := OptimizedRepresentation(CompositeFields(M, L)[1] : Ramification := ramification);

    end for;
    return M, 0, ramification;
  end if;
end function;

function global_extension(K, pol, P, res : special:=false, tries:=Infinity())
  //print "Trying to find extension of", K, "in which", pol, "factors"; 
  return FindInertExtension(K, Degree(pol), P : special := special, tries := tries); // Use new code to find global extension
end function;

// Given a polynomial F in O[x1,...,xn], return functions Fi (for i=1..n) and F_pi 
// such that F(xj's) = F_pi(yi's)*pi + sum of Fj(yi's)*(xj-yj) + H 
// where H is in the square of the ideal generated by pi and the (xj-yj)'s
/*
function partial_derivs(F, pi)

// case O = k[t], pi = t
assert Type(O) eq RngUPol and pi eq O.1 where O is BaseRing(Parent(F)); 

  Pol := Parent(F);  n := Rank(Pol);  // Pol.i = yi
  Pol2 := PolynomialRing(Pol,n);      // Pol2.j = xj-yj
  FF := Evaluate(F, [Pol2.j + Pol.j : j in [1..n]] ); 
  Fjs := [ MonomialCoefficient(FF, Pol2.j) : j in [1..n] ];
assert Fjs eq [Derivative(F,j) : j in [1..n]];
  Fpi := &+[Pol| Coefficient( MonomialCoefficient(F,mon), 1) * mon : mon in Monomials(F)]; // coeff of t

  if debug then 
    assert &and&cat[[ TotalDegree(mon) ge 2 : mon in Monomials(Fjs[j] - Derivative(F,j)) ] : j in [1..n]];
    // check H lies in the ideal generated by the (xj-yj)'s
    F0 := &+[Pol| ConstantCoefficient( MonomialCoefficient(F,mon) ) * mon : mon in Monomials(F) ];
    H := FF - ( F0 + pi*Fpi + &+[ Pol2.j*Fjs[j] : j in [1..n]] ); 
    for mon in Monomials(H) do 
      power_of_t := Min([ Valuation(c) : c in Coefficients(MonomialCoefficient(H,mon)) ]);
      assert power_of_t + TotalDegree(mon) ge 2; end for;
  end if;

  return Fjs, Fpi; 
end function; 
*/
function partial_derivs(F)
  Pol := Parent(F);  
  derivs := [Derivative(F,j) : j in [1..Rank(Pol)]];
  if Type(BaseRing(Pol)) eq RngUPol then
    dt := &+[Pol| Coefficient( MonomialCoefficient(F,mon), 1) * mon : mon in Monomials(F)]; // coeff of t
    return derivs, dt;
  else 
    return derivs;
  end if;
end function;

/*****************************************************************************************
  REGULARITY TESTS
 (These functions assume the scheme is regular away from the special fibre)
*****************************************************************************************/

// for handling the vararg res:=0 in the functions below
function get_k(O, P, res, kpol)
  if res cmpeq 0 then
    k, res := ResidueClassField(O,P);
  else 
    k := Codomain(res);
  end if;
  if Type(kpol) eq RngIntElt then
    kpol := PolynomialRing(k, kpol);
  end if;
  return k, res, kpol;
end function;

// Check regularity of scheme defined by eqns, of relative dimension d over Spec(O)
// at the given pt (given as a sequence of coords on the special fibre above the 
// prime ideal P of O, or as an ideal inside the special fibre)

function is_regular_at_point(eqns, d, pt, P : res:=0)
  if not ISA(Type(eqns), SeqEnum) then eqns := [eqns]; end if;
         
  if ISA(Type(P), RngElt) then
    pi := P;
    P := ideal< Parent(pi) | pi >;
  else
    pi := generators(P)[1];
  end if;

  Pol := Universe(eqns);  
  n := Rank(Pol);  assert n-d le #eqns;
  O := BaseRing(Pol);  
  k,res := get_k(O, P, res, 0);

  if ISA(Type(pt), RngMPol) then
    pt := pt_coords_from_ideal(pt);
  end if;

  U := Universe(pt);
  if k cmpeq U then
    pt := [lift(c,res) : c in pt]; 
  elif k cmpeq BaseField(U) then
    error if Type(O) eq RngUPol, 
         "Can't test regularity of non-rational points in the function field case"; // TO DO
    L := global_extension(field(O), DefiningPolynomial(U), P, res);
    OL := Integers(L);
    PolL := PolynomialRing(OL, Rank(Pol));
    eqnsL := ChangeUniverse(eqns, PolL);
    PL := ideal<OL| generators(P) >; assert IsPrime(PL);
    kL, resL := ResidueClassField(PL);
    // need an iso between kL and U that extends the correct embedding of k in kL
    // (Embed gives an error if an embedding already exists, so check first)
    if not IsPrimeField(k) and not IsCoercible(kL,k.1) then
      Embed(k, kL, k.1@@res@resL);
    end if;
    Embed(U, kL);  // any embedding that extends k -> kL
    ptL := ChangeUniverse(pt, kL);
    return is_regular_at_point(eqnsL, d, ptL, PL : res:=resL);
  end if;
  assert Universe(pt) cmpeq O; 

  // translate pt to origin
  eqns0 := [Evaluate(F, [Pol.i+pt[i] : i in [1..n]]) : F in eqns];
  jac := [];
  for F in eqns0 do 
    derivs := [MonomialCoefficient(F, Pol.i) : i in [1..n]];
    const := MonomialCoefficient(F, 1);  
    error if const notin P, "point does not satisfy equations mod P";
    Append(~derivs, const div pi);  
    Append(~jac, [dd @res : dd in derivs]);
  end for;
  m := Rank(Matrix(jac));  assert m le n-d;
  return m eq n-d;
end function;

// Determine non-regularities of a surface given by a single equation F in O[x,y].
// Returns bool, fibs, pts, kpol (fibs and pts are the 1- and 0-dimensional reduced irreducible 
// components where the scheme is not regular, given as ideals in kpol = the reduction of O[x,y]

function is_regular_single_eqn(F, P : res:=0) 
  if ISA(Type(P), RngElt) then
    pi := P;
    P := ideal< Parent(pi) | pi >;
  else
    pi := Generator(P);
  end if;

  Pol := Parent(F);  n := Rank(Pol);  
  O := BaseRing(Pol);  
  k,res := get_k(O, P, res, 0);
  kpol := PolynomialRing(k,n);  AssignNames(~kpol,["x"*IntegerToString(i) : i in [1..n]]);

special_comps, special_comps_reduced := PrimaryDecomposition(ideal< kpol | polyres(F,kpol,res) >);
assert special_comps_reduced eq [Radical(fib) : fib in special_comps];
//"Special fibre ="; special_comps; "";

  // Method for general O (for single eqn over O in two variables x,y)
  // + find the singular subscheme of special fibre using the partials Fx and Fy
  // + for each component of this, get an equation h(x,y), possibly on some restricted patch
  //   and write F(x,y) == G(x,y)*H(x,y)^2 + pi*L(x,y), where h is the reduction of H mod P 
  // + The subscheme of this component where F is nonregular is {L(x,y) = 0}

  derivs := partial_derivs(F);  
  derivs_vanish := ideal< kpol | [polyres(G,kpol,res) : G in derivs] >;
  f := polyres(F,kpol,res);
  error if f eq 0, "F reduces to zero mod pi";
  Pi := IdealWithFixedBasis([Pol!pi]);
  nonreg_pts := {};
  nonreg_fibs := [];
  for fib in special_comps_reduced do 
    sing := Radical(fib + derivs_vanish);
    if sing eq fib then
      // write f = g*h^m and lift g,h to G,H in O[x,y]
      bool, h := IsPrincipal(fib);  assert bool;
      m := 0; g := f; while g in ideal<kpol|h> do m +:= 1; g := g div h; end while;
      assert f eq g*h^m and m ge 2;
      G := polylift(g,Pol,res);
      H := polylift(h,Pol,res);
      Fpi := (F - G*H^m) div pi; 
      nonreg_on_fib := Radical(fib + ideal< kpol | polyres(Fpi,kpol,res) >);
      if nonreg_on_fib eq fib then 
        Append(~nonreg_fibs, fib);  
      else 
        assert Dimension(nonreg_on_fib) le 0;
        nonreg_pts join:= Seqset(pts) where _,pts := PrimaryDecomposition(nonreg_on_fib);
      end if;
    else 
      _,sing_pts := PrimaryDecomposition(sing);
      for pt in sing_pts do 
        // check regularity at pt
        Pt := ideal< Pol | [pi] cat [polylift(gen,Pol,res) : gen in Basis(pt)] >;
        if F in Pt^2 then Include(~nonreg_pts,pt); end if;
      end for;
    end if;
  end for;
  // get rid of points lying on nonreg_fibs
  nonreg_pts := {pt : pt in nonreg_pts | not &or [fib subset pt : fib in nonreg_fibs]}; 

  // Check using partials derivs when O = k[t], pi = t 
  if Type(O) eq RngUPol and pi eq O.1 then
    Fis, Fpi := partial_derivs(F);
    nonreg := ideal< kpol | [polyres(G,kpol,res) : G in [F,Fpi] cat Fis] >;
    nonreg_comps := Seqset(&cat[ RadicalDecomposition(fib + nonreg) : fib in special_comps_reduced ]);
    assert #Seqset(nonreg_fibs) eq #nonreg_fibs;
    assert Seqset(nonreg_fibs) eq {fib : fib in nonreg_comps | Dimension(fib) eq 1};
    assert nonreg_pts eq {pt : pt in nonreg_comps | Dimension(pt) eq 0 and not &or [fib subset pt : fib in nonreg_fibs]};
  end if;
 
  return IsEmpty(nonreg_fibs) and IsEmpty(nonreg_pts), 
         nonreg_fibs, Setseq(nonreg_pts), kpol;
end function;


// Determines whether scheme defined by { F=0, pi=U } where F,U are in Pol = O[X,Y,Z],
// is regular generically along Ires, a reduced irreducible 1-dimensional component of 
// the special fibre given as an ideal of kpol = k[x,y,z].
// Ires *must* be contained in singular subscheme of special fibre.
// When true (ie regular except at finitely many points of fib), also returns the 
// non-regular points, as a sequence of (maximal) ideals of kpol.

// Method: let I be the pullback of Ires to Pol (so I contains P).
// If F and U are both in I^2 + P, then scheme is non-regular along I.
// Otherwise, find A, B in Pol but not in I, such that F1 = A*F + B*(pi-U) is in I^2 + P.  
// Write F1 = pi*H + I^2.  The scheme is non_regular along I iff F1 in I^2 (iff H in I). 
// More generally, for a point M (maximal ideal of Pol) containing I but not containing {A,B}
// the scheme is non-regular at M iff H is in M.

// Temporary version translating ideals over O to ideals over Z 

function is_regular_fibre_FU_hack(F, U, Ires, P, pi : res:=0, kpol:=3)
  Pol := Parent(F); assert Pol eq Parent(U) and Rank(Pol) eq 3;
  O := BaseRing(Pol); assert O eq Parent(pi);
  k, res, kpol := get_k(O, P, res, kpol);
  P := ideal< Parent(pi) | pi >;
  gensP := generators(P);
  eqns := [F, pi-U];

  // Set up the conversion Pol <--> PolZ
  K := NumberField(O);
  assert ISA(Type(K), FldAlg);
  error if not IsAbsoluteField(K) or NumberOfGenerators(K) ne 1 or 
           not IsIntegral(K.1) or Order([K.1]) ne O, 
           "\nRegularModel: Not yet implemented for this number field."
           *"\n(K.1 does not generate the maximal order.)";
  r := Rank(Pol);
  PolZ := PolynomialRing(Integers(), r+1); 
  a := PolZ.(r+1); // this variable will correspond to K.1
  function toPolZ(pol)
    if pol in O then
      e := ChangeUniverse(Eltseq(K!pol), Integers());
      return &+[e[i]*a^(i-1) : i in [1..#e]];
    else
      c,m := CoefficientsAndMonomials(pol);
      return &+[ c[i]@toPolZ * Monomial(PolZ, Exponents(m[i]) cat [0]) : i in [1..#m] ];
    end if;
  end function;
  function fromPolZ(pol)
    return Evaluate(pol, [Pol.i : i in [1..r]] cat [Pol!K.1]);
  end function;
  idealZ0 := ideal< PolZ | Evaluate(ChangeRing(DefiningPolynomial(K), Integers()), a) >;
  function idealZ(gens)
    return idealZ0 + ideal< PolZ | [g@toPolZ : g in gens] >;
  end function;

  I := idealZ(gensP cat [polylift(b,Pol,res) : b in Basis(Ires)]);
  I2 := I^2 + idealZ0;
  I2P := idealZ(gensP) + I2;

  f := polyres(F,kpol,res);
  u := polyres(U,kpol,res);
  I2res := Ires^2;
  if u in I2res and f in I2res then 
    return false, _;
  else
    // In kpol, find a*f+b*u in Ires^2
    fu := IdealWithFixedBasis([f,-u]);  
    J := fu meet Ires^2;
    coords := [Coordinates(fu, b) : b in Basis(J)];
    assert exists(ab) {ab : ab in coords | not ab subset Ires}; 
    A, B := Explode([ polylift(x,Pol,res) : x in ab ]);
    F1 := A*F + B*(pi-U);
    if debug then 
      assert F1@toPolZ in I2P;
      f1 := polyres(F1,kpol,res);
      F1derivs := [Derivative(f1,i) : i in [1..3]];
      assert &and [d in Ires : d in F1derivs];
    end if;
    if F1@toPolZ in I2 then
      return false, _;
    else
      // Write F1 = pi*H mod I^2
      I2bas := [b@fromPolZ : b in Basis(I2)];
      I2res := IdealWithFixedBasis([polyres(b,kpol,res) : b in I2bas]);
      F1coords_res := Coordinates(I2res, polyres(F1,kpol,res));
      F1coords := [polylift(c,Pol,res) : c in F1coords_res];
      H := (F1 - &+[F1coords[i]*I2bas[i] : i in [1..#I2bas]]) div pi;
      // also must check points where both equations have zero derivs
      FF := (ab[2] in Ires) select U else F;
      FFk := polyres(FF,kpol,res);
      nonreg_pts := RadicalDecomposition(Ires + ideal< kpol | polyres(H,kpol,res) >) cat
                    RadicalDecomposition(Ires + ideal< kpol | [Derivative(FFk,i) : i in [1..3]] >);
      nonreg_pts := [pt : pt in nonreg_pts | not is_regular_at_point(eqns, 1, pt, P : res:=res)];
      if debug then 
        assert (F1-pi*H)@toPolZ in I2 and H@toPolZ notin I;  
        assert forall{pt: pt in nonreg_pts | Dimension(pt) eq 0}; 
      end if;
      return true, nonreg_pts;
    end if;
  end if;
end function;

function is_regular_fibre_FU(F, U, Ires, P, pi : res:=0, kpol:=3)

  Pol := Parent(F); assert Pol eq Parent(U) and Rank(Pol) eq 3;
  O := BaseRing(Pol); assert O eq Parent(pi);

  if ISA(Type(O), RngOrd) then
    return is_regular_fibre_FU_hack(F, U, Ires, P, pi : res:=res, kpol:=kpol);
  end if;

  k, res, kpol := get_k(O, P, res, kpol);
  P := ideal< Parent(pi) | pi >;
  gensP := generators(P);
  eqns := [F, pi-U];

  // branch according to whether to work with ideals over O or over residue rings
  // Here it suffices to work mod P^2.
  use_Pol := not ISA(Type(O), RngOrd);
  if use_Pol then
    I := ideal< Pol | gensP cat [polylift(b,Pol,res) : b in Basis(Ires)] >;
    I2 := I^2;
    I2P := ideal< Pol | gensP > + I2;
  else
    R, res2 := quo< O | P*P >;
    Rpol := PolynomialRing(R, Rank(Pol));
    I := ideal< Rpol | [g@res2 : g in gensP] cat [polyres(polylift(b,Pol,res),Rpol,res2) : b in Basis(Ires)] >;
    I2 := I^2;
    I2P := ideal< Rpol | [g@res2 : g in gensP] > + I2;
  end if;

  f := polyres(F,kpol,res);
  u := polyres(U,kpol,res);
  I2res := Ires^2;
  if u in I2res and f in I2res then 
    return false, _;
  else
    // In kpol, find a*f+b*u in Ires^2
    fu := IdealWithFixedBasis([f,-u]);  
    J := fu meet Ires^2;
    coords := [Coordinates(fu, b) : b in Basis(J)];
    assert exists(ab) {ab : ab in coords | not ab subset Ires}; 
    A, B := Explode([ polylift(x,Pol,res) : x in ab ]);
    F1 := A*F + B*(pi-U);
    if debug then 
      assert use_Pol select F1 in I2P  
                      else  polyres(F1,Rpol,res2) in I2P;
      f1 := polyres(F1,kpol,res);
      F1derivs := [Derivative(f1,i) : i in [1..3]];
      assert &and [d in Ires : d in F1derivs];
    end if;
    if use_Pol select F1 in I2  
                else  polyres(F1,Rpol,res2) in I2 then
      return false, _;
    else
      // Write F1 = pi*H mod I^2
      I2bas := use_Pol select Basis(I2)
                        else [polylift(b,Pol,res2) : b in Basis(I2)];
      I2res := IdealWithFixedBasis([polyres(b,kpol,res) : b in I2bas]);
      F1coords_res := Coordinates(I2res, polyres(F1,kpol,res));
      F1coords := [polylift(c,Pol,res) : c in F1coords_res];
      H := (F1 - &+[F1coords[i]*I2bas[i] : i in [1..#I2bas]]) div pi;
      // also must check points where both equations have zero derivs
      FF := (ab[2] in Ires) select U else F;
      FFk := polyres(FF,kpol,res);
      nonreg_pts := RadicalDecomposition(Ires + ideal< kpol | polyres(H,kpol,res) >) cat
                    RadicalDecomposition(Ires + ideal< kpol | [Derivative(FFk,i) : i in [1..3]] >);
      nonreg_pts := [pt : pt in nonreg_pts | not is_regular_at_point(eqns, 1, pt, P : res:=res)];
// TO DO: smarter way, but not quite correct yet 
//        (because the ab thing assumes F1 is the unique combination in whatever ideal):
//    nonreg_pts := [pt : pt in nonreg_pts
//                      | not ab subset pt  // under this condition, pt is nonreg iff H(pt) = 0
//                        or not is_regular_at_point(eqns, 1, pt, P : res:=res)];  
      if debug then 
        assert use_Pol select F1-pi*H in I2 and H notin I  
                        else  polyres(F1-pi*H,Rpol,res2) in I2 and polyres(H,Rpol,res2) notin I;
        assert forall{pt: pt in nonreg_pts | Dimension(pt) eq 0}; 
      end if;
      return true, nonreg_pts;
    end if;
  end if;
end function;


// Determines regularity of scheme defined by { F=0, pi=U } where F,U are in Pol = O[X,Y,Z].
// Scheme is assumed to have 1-dimensional special fibre.
// Returns bool, fibs, pts, kpol (fibs and pts are the 1- and 0-dimensional reduced irreducible 
// components where the scheme is not regular, given as ideals in kpol = the reduction of Pol).

function is_regular_FU(F, U, P, pi : res:=0, kpol:=3)
  Pol := Parent(F); assert Pol eq Parent(U) and Rank(Pol) eq 3;
  O := BaseRing(Pol); assert O eq Parent(pi);
  P := ideal< Parent(pi) | pi >;
  eqns := [F, pi-U];

  // Find the components where the special fibre is singular 
  k, res, kpol := get_k(O, P, res, kpol);
  FUres := ideal< kpol | polyres(F,kpol,res), polyres(U,kpol,res) >; 
assert Dimension(FUres) eq 1;
  FUres_scheme := Scheme(AffineSpace(kpol), FUres);
  FUres_sing := DefiningIdeal(SingularSubscheme(FUres_scheme));
  sing_comps := RadicalDecomposition(FUres_sing);
  sing_fibs := [I : I in sing_comps | Dimension(I) eq 1];
  sing_pts := {I : I in sing_comps | Dimension(I) eq 0};
  nonreg_fibs := [];
  nonreg_pts := {};

  for Ires in sing_fibs do
    reg, pts := is_regular_fibre_FU(F, U, Ires, P, pi : res:=res, kpol:=kpol);
    if reg then 
      nonreg_pts join:= Seqset(pts);
    else
      nonreg_fibs cat:= [Ires];
    end if;
  end for;
 
  for pt in sing_pts do 
    if not is_regular_at_point(eqns, 1, pt, P : res:=res) then
      Include(~nonreg_pts, pt);
    end if;
  end for;

  if debug and ISA(Type(O), RngUPol) 
and pi eq O.1 
  then // Check: compare with general routine
    bool1, fibs1, pts1 := is_regular(eqns, P : res:=res);
    assert nonreg_pts eq {ideal<kpol| [kpol!b : b in Basis(I)]> : I in pts1}; 
    assert Seqset(nonreg_fibs) eq {ideal<kpol| [kpol!b : b in Basis(I)]> : I in fibs1};
  end if;

  return IsEmpty(nonreg_fibs) and IsEmpty(nonreg_pts), nonreg_fibs, Setseq(nonreg_pts);
end function;


// Determines regularity of scheme defined by eqns = arbitrary sequence of polys in Pol = O[X1,X2,...]
// Scheme is assumed to have 1-dimensional special fibre.
// Returns bool, fibs, pts, kpol (fibs and pts are the 1- and 0-dimensional reduced irreducible 
// components where the scheme is not regular, given as ideals in kpol = the reduction of Pol.

function is_regular(eqns, P : res:=0)
  if not ISA(Type(eqns), SeqEnum) then eqns := [eqns]; end if;

  if ISA(Type(P), RngElt) then
    pi := P;
    P := ideal< Parent(pi) | pi >;
  else
    pi := Generator(P);
  end if;
  k,res := get_k(O, P, res, 0);

  if #eqns eq 1 then 
    bool, fibs1, pts1, kpol := is_regular_single_eqn(eqns[1], P : res:=res);
  end if;

  // Case O = k[t] : compute singularities of the surface intersected with the special fibre
  // TO DO: apparently this is just the special case P = (t) ?
  O := BaseRing(Universe(eqns));
  if Type(O) eq RngUPol then
    k := BaseRing(O); t := O.1;
    n := Rank(Universe(eqns)); // # of variables, excluding t
    A := AffineSpace(k, n+1); 
    P := ideal<O|pi>; 
    _,res := ResidueClassField(O,P); assert Codomain(res) eq k;
    kpol := PolynomialRing(k,n);
    eqns1 := [ &+[ Evaluate(coeffs[k], A.(n+1)) * 
                   &* [A.i ^ Degree(mons[k],i) : i in [1..n]] 
                 : k in [1..#mons] ]
               where coeffs := Coefficients(f) where mons := Monomials(f)
             : f in eqns ];
    pi1 := Evaluate(pi, A.(n+1));
    S := Scheme(A, eqns1);
    N := SingularSubscheme(S);
    I := ideal< CoordinateRing(A) | DefiningIdeal(N), pi1 >;
    vars := [kpol.i : i in [1..n]] cat [0]; 
    fibs := []; 
    pts := [];
    for J in RadicalDecomposition(I) do 
      J0 := ideal<kpol| [Evaluate(b,vars) : b in Basis(J)] >;  // TO DO: need to take radical again?
      if Dimension(J0) eq 0 then 
        Append(~pts, J0); 
      else 
        Append(~fibs, J0);
      end if;
    end for;
    if #eqns eq 1 then assert fibs cat pts eq [kpol!!I : I in fibs1 cat pts1]; end if;
  end if;

  return IsEmpty(fibs) and IsEmpty(pts), fibs, pts, kpol;
end function;

