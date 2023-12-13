//freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// Thank you!

////////////////////////////////////////////////////////////////////////
//
//  Computations with the analytic jacobian of a hyperelliptic curve.
//  This file is for the mappings between the analytic and algebraic
//  jacobians.
//
//  P. van Wamelen (started Nov 2002)
//
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//   ToAnalyticJacobian, FromAnalyticJacobian, RosenhainInvariants
//
////////////////////////////////////////////////////////////////////////
//
//  to debug the following is useful:
//   import "/home/magma/package/Geometry/CrvAnJac/jacmaps.m" : Bset, Uset,
//     eta1, eta, taured, taured0Q, MyCompInverse;
//
////////////////////////////////////////////////////////////////////////

forward eta1;

intrinsic ToAnalyticJacobian
(x::FldComElt, y::FldComElt, z::FldComElt, AJ::AnHcJac) -> Mtrx
{This maps the point (x:y:z) on the curve to its analytic Jacobian.
 The analytic Jacobian is understood to be C^g/Lambda. }
  C := BaseRing(AJ);
 require Parent(x) eq C: "Argument 1 must be in the base ring of the Jacobian";
 require Parent(y) eq C: "Argument 2 must be in the base ring of the Jacobian";
 require Parent(z) eq C: "Argument 3 must be in the base ring of the Jacobian";
  pres := Precision(C);
  g := Genus(AJ);
  fC := HyperellipticPolynomial(AJ);
  ev := (&+[Coefficient(fC, j)*x^j*z^(2*g+2-j) : j in [0..Degree(fC)]] - y^2);
//   ev:=Evaluate(AJ`HyperellipticPolynomial,x/z)-(y/z)^2;
  require Abs(ev) lt 10^(-pres/2-5)*(Norm(x)+Norm(z))^(g+1): "Point not on hyperelliptic curve?";
  if Abs(Imaginary(x)) lt 10^(5-pres) then x:=x+10^(5-pres)*C.1; end if;
  rts := AJ`Roots;
  g := (#rts-1) div 2;
  if z ne 0 then
    x := x/z;
    y := y/z^(g+1);
    // Apply map to get point on the odd degree model
    if AJ`OddDegree then
      y := y/Sqrt(AJ`OddLeadingCoefficient);
    else
      if Abs(x-AJ`InfiniteRoot) lt 10^(-pres+5) then
        return Matrix(C,g,1,[]);
      end if;
      x := 1/(x-AJ`InfiniteRoot);
      y := y*x^(g+1)/(Sqrt(AJ`EvenLeadingCoefficient)*
        Sqrt(AJ`OddLeadingCoefficient));
    end if;
  elif  AJ`OddDegree then
    x := 0;
    y := y/Sqrt(AJ`OddLeadingCoefficient);
  else
    x := 0;
    y := y/(Sqrt(AJ`EvenLeadingCoefficient)*
        Sqrt(AJ`OddLeadingCoefficient));
  end if;
  // this product needs to be done the *exact* way it is done in anal.c
  // otherwise numerical instability can cause a mess...
  // see Analytic_Jacobian_Addition example
  pc:=Precision(C); x+:=10^(-pc+1)*(C.1); // MW Mar11 avoid branchcut
  fa := x-rts[1]; // hmm
  for i in [2..#rts] do
    fa *:= x-rts[i];
  end for;
  ty := Sqrt(fa); //  ty := Sqrt(&*[x - r : r in rts]);
  if Abs(ty) lt 10^(-(pres div 2)+5) then
    rsgn := C!1;
  else
    rsgn := y/ty;
  end if;
  sgn := Round(Re(rsgn)); // need above x-fiddle *before* this is computed ?!
  assert Abs(sgn-rsgn) le 10^(-pres/2+5);
  // Check that we aren't at a Weierstrass point and if we
  // are don't try to integrate (it will take forever) but just return
  // the correct eta interpolated...
  // NOTE: in case you are within 10^-16 or so, but not at, a Weierstrass point
  // HyperellipticIntegrals below will fail because in findc we work at low
  // precision and we get divide by zero. To fix this do integrals that get
  // close to a Weierstrass point, a, by a change of variable z^2 = (x-a) as
  // was done for the integral to infinity. Wait for new reals...
  min, nrti := Min([Abs(x-rt) : rt in rts]);
  nrt := rts[nrti];
  if min lt 10^(-pres+10) then
    char := eta1(g,nrti);
    char:=Matrix(C,char); // MW Nov 2017, this seems a/the correct way around?
    /*  char := Matrix(C,VerticalJoin(Submatrix(char,g+1,1,g,1), // wrong?
	                              Submatrix(char,1,1,g,1))); */
    return AJ`BigPeriodMatrix*char;
  end if;
  // Find closest point from which integral is known
  // but exclude paths that take you closer to the nearest root
  elst := [p : p in AJ`EndPoints | Re((p-x)/(nrt-x)) lt 0];
  if elst eq [] then
    elst := AJ`EndPoints;
  end if;
  _, ind := Minimum([Abs(x-p) : p in elst]);

  intlst, sgnlst := HyperellipticIntegral([[x,AJ`EndPoints[ind]]],rts);
  ans := sgn*AJ`DifferentialChangeMatrix*Matrix(g,1,intlst[1]);
  sgn := sgn*sgnlst[1];
  pathtobase := Geodesic(AJ`PathGraph!ind,AJ`PathGraph!AJ`BasePoint);
  pathtobase := [Index(v) : v in pathtobase];
  for i := 1 to #pathtobase-1 do
    e := [pathtobase[i],pathtobase[i+1]];
    ind := Index(AJ`DirectedEdges,e);
    if ind gt 0 then
      ans +:= sgn*AJ`PathIntegrals[ind];
      sgn *:= AJ`PathSigns[ind];
    else
      ind := Index(AJ`DirectedEdges,Reverse(e));
      sgn *:= AJ`PathSigns[ind];
      ans +:= -sgn*AJ`PathIntegrals[ind];
    end if;
  end for;
  ans +:= sgn*AJ`InfiniteIntegrals;
  return ans;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ToAnalyticJacobian(x::FldComElt, y::FldComElt, AJ::AnHcJac) -> Mtrx
{This maps the point \{x,y\} on the curve to its analytic Jacobian.
 The analytic Jacobian is understood to be C^g/Lambda. }
  if Log(10,Abs(x)+1) gt 0.7*Precision(x) then
    // point is very likely at infinity
//     printf "ToAnalyticJacobian: point with large coordinates replaced by point at infinity\n";
    yx := y/x^(Genus(AJ)+1);
    y_inf := Sqrt(Coefficient(HyperellipticPolynomial(AJ), 2*Genus(AJ)+2));
    yx := Abs(yx - y_inf) lt Abs(yx + y_inf) select y_inf else -y_inf;
    return ToAnalyticJacobian(Parent(x)!1, yx, Parent(x)!0, AJ);
  else
    return ToAnalyticJacobian(x,y,Parent(x)!1,AJ);
  end if;
end intrinsic;

intrinsic ToAnalyticJacobian(P::PtHyp, sigma::PlcNumElt, AJ::AnHcJac) -> Mtrx
{This maps the point P on a hyperelliptic curve to the analytic Jacobian
 associated to  the same curve over the complex numbers. The  analytic
 Jacobian is understood to be C^g/Lambda. }

  require IsInfinite(sigma): "Argument 2 must be an archimedean place.";
  require BaseRing(Parent(P)) eq NumberField(sigma):
  "Argument 2 must be an  archimedean place of the base ring of argument 1";

  require AnalyticJacobian(Curve(P), sigma :
			   Precision := Precision(BaseRing(AJ))) cmpeq AJ:
  "Argument 3 must be analytic Jacobian"*
  "associated to the curve of argument 1 embedded using argument 2.";

  Cc := BaseRing(AJ);
  x, y, z := Explode(ChangeUniverse([P[1],P[2],P[3]],Cc));
  return ToAnalyticJacobian(x, y, z, AJ);
end intrinsic;

intrinsic ToAnalyticJacobian(P::PtHyp, AJ::AnHcJac) -> Mtrx
{This maps the point P on a curve defined over a number field to the
  analytic Jacobian associated to the archimedean place sigma. The
 analytic Jacobian is understood to be C^g/Lambda. }

  require AnalyticJacobian(Curve(P) :
			   Precision := Precision(BaseRing(AJ))) cmpeq AJ:
  "Argument 2 must analytic Jacobian associated to curve of argument 1.";

  Cc := BaseRing(AJ);
  x, y, z := Explode(ChangeUniverse([P[1],P[2],P[3]],Cc));
  return ToAnalyticJacobian(x, y, z, AJ);
end intrinsic;

// New

intrinsic ToAnalyticJacobianMumford(pt::JacHypPt, AJ::AnHcJac) -> Mtrx
{Map the point on the Jacobian over Q to the analytic Jacobian.}
  J := Parent(pt);
  g := Dimension(J);
  // some checks
  f, h := HyperellipticPolynomials(Curve(J));
  CC := BaseField(AJ);
  require h eq 0 and ChangeRing(f, CC) eq HyperellipticPolynomial(AJ):
          "Argument 2 must be the analytic Jacobian associated to the parent of argument 1.";
  apol := pt[1];
  bpol := pt[2];
  d := pt[3];
  // if the divisor representing pt contains points at infinity,
  // move to a linearly equivalent divisor that does not
  if Degree(apol) lt d then
    bd := 1;
    repeat
      bpol1 := bpol + apol*Parent(apol)![Random(-bd, bd) : j in [0..g+1-d]];
      apolnew := ExactQuotient(f - bpol1^2, apol);
      bd *:= 2;
    until Degree(apolnew) eq Degree(f) - d;
    apol := apolnew;
    bpol := -bpol1 mod apol;
  end if;
  // now map the points in the support to AJ and add them up
  afact := Factorization(apol);
  result := Matrix(CC, [[0] : j in [1..g]]);
  for e in afact do
    for r in Roots(e[1], CC) do
      result +:= e[2]*ToAnalyticJacobian(r[1], Evaluate(bpol, r[1]), AJ);
    end for;
  end for;
  return result;
end intrinsic;

intrinsic ToAnalyticJacobianMumford(pt::JacHypPt, AJ::AnHcJac, conj::RngIntElt) -> Mtrx
{Map the point on the Jacobian over a number field K to the analytic Jacobian
 using the conj'th embedding of K into the complex numbers.}
  J := Parent(pt);
  g := Dimension(J);
  // some checks
  f, h := HyperellipticPolynomials(Curve(J));
  CC := BaseField(AJ);
  prec := Precision(CC);
  pol_to_CC := func<pol | Polynomial(CC, [Conjugate(c, conj : Precision := prec) : c in Coefficients(pol)])>;
  dev := Sqrt(&+[RealField()| Norm(c) : c in Coefficients(pol_to_CC(f) - HyperellipticPolynomial(AJ))]);
  require h eq 0 and dev lt 0.1^(0.9*prec):
          "Argument 2 must be the analytic Jacobian associated to the parent of argument 1.";
  apol := pt[1];
  bpol := pt[2];
  d := pt[3];
  // if the divisor representing pt contains points at infinity,
  // move to a linearly equivalent divisor that does not
  if Degree(apol) lt d then
    bd := 1;
    repeat
      bpol1 := bpol + apol*Parent(apol)![Random(-bd, bd) : j in [0..g+1-d]];
      apolnew := ExactQuotient(f - bpol1^2, apol);
      bd *:= 2;
    until Degree(apolnew) eq Degree(f) - d;
    apol := apolnew;
    bpol := -bpol1 mod apol;
  end if;
  // now map the points in the support to AJ and add them up
  afact := Factorization(apol);
  result := Matrix(CC, [[0] : j in [1..g]]);
  bpolCC := pol_to_CC(bpol);
  for e in afact do
    for r in Roots(pol_to_CC(e[1])) do
      result +:= e[2]*ToAnalyticJacobian(r[1], Evaluate(bpolCC, r[1]), AJ);
    end for;
  end for;
  return result;
end intrinsic;

////////////////////////////////////////////////////////////////////////

// -1 will stand for infinity
// The next 4 functions from Mumford, ThetaII, Lemma 3.5.6 p86
function Bset(g)
  return {1..(2*g+1)} join {-1};
end function;

function Uset(g)
  return {2*i+1 : i in [0..g]};
end function;

function eta1(g,j)
  ans := Matrix(RationalField(),2*g,1,[]);
  if j eq -1 then
    return ans;
  end if;
  if j mod 2 eq 1 then
    i := (j+1) div 2;
    ans[i,1] := 1/2;
    for k := g+1 to g+i-1 do
      ans[k,1] := 1/2;
    end for;
    return ans;
  else
    i := j div 2;
    ans[i,1] := 1/2;
    for k := g+1 to g+i do
      ans[k,1] := 1/2;
    end for;
    return ans;
  end if;
end function;

function eta(g,S)
  if S eq {} then
    return eta1(g,-1);
  else
    return &+[eta1(g,j) : j in S];
  end if;
end function;

function taured(nz,tau);
  g := NumberOfRows(tau);
  C := BaseRing(tau);
  Itau := Matrix(g,g,[Im(a) : a in ElementToSequence(tau)]);
  dum := Itau^-1*Matrix(g,1,[Im(zi) : zi in ElementToSequence(nz)]);
  v1 := Matrix(C,g,1,[Round(di) : di in ElementToSequence(dum)]);
  nz := nz - tau*v1;
  return nz - Matrix(C,g,1,[Round(Re(di)) : di in ElementToSequence(nz)]);
end function;

function taured0Q(nz,tau);
  dum := taured(nz,tau);
  return Max([Abs(d) : d in ElementToSequence(dum)]);
end function;

/* This is realy dumb, but I don't have time to fix magma right now... */
/*function MyCompInverse(mat);
  C := BaseRing(mat);
  dim := NumberOfRows(mat);
  fullmat := HorizontalJoin(mat,ScalarMatrix(dim,C!1));
  for i in [1..dim] do
    _,ind := Max([Abs(fullmat[j,i]) : j in [i..dim]]);
    ind := ind+i-1;
    SwapRows(~fullmat,i,ind);
    for j in [i+1..dim] do
      AddRow(~fullmat,-fullmat[j,i]/fullmat[i,i],i,j);
    end for;
    MultiplyRow(~fullmat,1/fullmat[i,i],i);
  end for;
  for i:=dim to 2 by -1 do
    for j in [1..i-1] do
      AddRow(~fullmat,-fullmat[j,i],i,j);
    end for;
  end for;
  return Submatrix(fullmat,1,dim+1,dim,dim);
end function;*/

// Random real number between s and b to precision of R
function RandomReal(s,b,R)
  pres := Precision(R);
  dum := Random(0,10^pres)/(R!10.0)^pres;
  return s + dum*(b-s);
end function;

function RandomPoint(f)
  rts := [r[1] : r in Roots(f)];
  C := Universe(rts);
  pres := Precision(C);
  I := Name(C,1);
  R := Parent(Re(I));
  a := Max([Re(r) : r in rts]);
  b := Min([Re(r) : r in rts]);
  c := Max([Im(r) : r in rts]);
  d := Min([Im(r) : r in rts]);
  if c-d lt 10^-10 then
    c := c + (b-a)/6;
    d := d - (b-a)/6;
  end if;
  if a-b lt 10^-10 then
    a := a + (c-d)/6;
    b := b - (c-d)/6;
  end if;
  dum := (a+b)/2;
  a := 2*(a-dum)+dum;
  b := 2*(b-dum)+dum;
  dum := (c+d)/2;
  c := 2*(c-dum)+dum;
  d := 2*(d-dum)+dum;
  thex := RandomReal(a,b,R) + I*RandomReal(c,d,R);
  they := Random([-1,1])*Sqrt(Evaluate(f,thex));
  return thex,they;
end function;

function AffinePointToProjectivePoint(pt, g, oddDegree, y_inf)
  x, y := Explode(pt);
  C := Parent(x);
  prec := Precision(C);
  // check if (x,y) is likely to be a point at infinity
  if Abs(x) gt 10^(prec/3 - 2) then
    y_ := y/x^(g+1);
    if oddDegree then
//       assert Abs(y_) lt 10^(-0.7 * prec);
      return <C!1, C!0, C!0>;
    else
      min, pos := Min([Abs(y_ - y_inf), Abs(y_ - -y_inf)]); // determine sign of point at infinity
//       assert min lt 10^(-0.7 * prec);
      return <C!1, [y_inf, -y_inf][pos], C!0>; // approximately point at infinity: 1/x \approx 0
    end if;
  else
    return <x, y, C!1>;
  end if;
end function;

function AffinePointsToProjectivePoints(ptseq, g, oddDegree, y_inf)
  seq := [AffinePointToProjectivePoint(pt, g, oddDegree, y_inf) : pt in ptseq];
  return oddDegree select [pt : pt in seq | pt[3] ne 0] else seq;
end function;

// See [Mumford, Tata Lectures on Theta II], p. 3.80 f., Theorem 5.3
intrinsic FromAnalyticJacobianXYZ(z::Mtrx[FldCom], A::AnHcJac) -> SeqEnum
{This returns a divisor corresponding to z}
  rts := A`Roots;
  g := (#rts-1) div 2;
  C := Universe(rts);
  require C eq BaseRing(z) : "The first argument must have entries"*
  " in the base ring of the analytic Jacobian";
  require NumberOfRows(z) eq g :
    "The first argument does not have the correct number of rows";
  require NumberOfColumns(z) eq 1 :
    "The first argument must have one column";
  pres := Precision(C);
  om1 := Submatrix(BigPeriodMatrix(A),1,g+1,g,g)^-1;
  nz := om1*z;
  V := {1..g+1};
  U := Uset(g);
  etaU  := eta(g,U);
  etaUV := eta(g,U sdiff V);
  etaUp := Submatrix(etaU,1,1,g,1);
  etaUVpp := Submatrix(etaUV,g+1,1,g,1);
  tau := SmallPeriodMatrix(A);
  thnullden := InternalTheta(Matrix(C,etaUV),Matrix(C,g,1,[]),tau);
  thetaden  := InternalTheta(Matrix(C,etaU ),nz,tau);
  //printf "thnullden = %o\nthetaden = %o\n", thnullden, thetaden;
  if Abs(thetaden) lt 10^(-pres/2+5) then
  // We are close to the theta divisor. Add a random point and subtract again
    //print "We are on the theta divisor. Add a random point and subtract again";
    Seeds, Seedc := GetSeed();
    success := false;
    dum := Abs(thetaden);
    SetSeed(Round(dum*10^(-Round(Log(dum)/Log(10))+3)));
    repeat
      try
        thex, they := RandomPoint(HyperellipticPolynomial(A));
        rpt := ToAnalyticJacobian(thex,they,A);
        z2 := z + rpt; // add a random point
        Plst := FromAnalyticJacobian(z2,A);
        success := true;
      catch e
        success := false;
      end try;
    until success;
    SetSeed(Seeds, Seedc);
    if IsEmpty(Plst) then
      Plst := [<thex, -they>];
    else
      dum := [Max(Abs(P[1]-thex),Abs(P[2]-they)) : P in Plst]; // find the point added in the divisor
      min, ind := Min(dum);
      assert min lt 10^(-Round(pres*0.8));
      Remove(~Plst,ind); // subtract again
    end if;
    // MS, 2023-11-28: replace by base point if degree is even!
    if not A`OddDegree and IsOdd(#Plst) then Append(~Plst, <A`InfiniteRoot, C!0>); end if;
    //return Plst;
    return AffinePointsToProjectivePoints(Plst, g, A`OddDegree,
                                          A`OddDegree select 0 else C!Sqrt(A`EvenLeadingCoefficient));
  end if;
  cvec := [];
  M := Matrix(C,g,g,[]);
  for k in [1..g] do
    etak  := eta1(g,k);
    etakp := Submatrix(etak,1,1,g,1);
    etakpp := Submatrix(etak,g+1,1,g,1);
    thnullnum := InternalTheta(Matrix(C,etaUV+etak),Matrix(C,g,1,[]),tau);
    thetanum  := InternalTheta(Matrix(C,etaU +etak),nz,tau);
    ck := &*[rts[k]-rts[i] : i in V | not i eq k];
    ck := ck*(-1)^IntegerRing()!
          (4*(Transpose(etaUp)*etakpp + Transpose(etaUVpp)*etakp)[1,1]);
    ck := ck*(thnullnum*thetanum/(thnullden*thetaden))^2;
    Append(~cvec,ck-rts[k]^g);
    for j in [1..g] do
      M[k,j] := rts[k]^(g-j);
      if rts[k] eq 0 then
        M[k,g] := 1;
      end if;
    end for;
  end for;
  cvec := Matrix(g,1,cvec);
  sx := Transpose(cvec)*Transpose(M)^-1; //MyCompInverse(Transpose(M));
  P := PolynomialRing(C); x := P.1;
  F := P!Reverse(ElementToSequence(sx)) + x^g;
  xlst := Roots(F);  // This causes trouble if there are multiple roots...
  assert forall{x[2] : x in xlst | x[2] eq 1};
  xlst := [x[1] : x in xlst]; // find the x-coordinates of the points of the divisor
  if not A`OddDegree then // if even degree model ...
    xlst := [1/x+A`InfiniteRoot : x in xlst]; // Apply map to get point back on original model
  end if;
  f := HyperellipticPolynomial(A);
  ylst := [Sqrt(Evaluate(f,thex)) : thex in xlst]; // find y-coodinates of the points of the divisor up to sign
  zlst := [om1*ToAnalyticJacobian(xlst[i],ylst[i],A) : i in [1..g]]; // find z-coodinates of the points of the divisor up to sign
  sgnlst := [sgns : sgns in CartesianPower({-1,1}, g)];
  dlst :=
    [taured0Q(nz-&+[sgn[i]*zlst[i] : i in [1..g]],tau) : sgn in sgnlst];
  min,ind := Min(dlst);
  assert Abs(min) le 10^-10;
  sgns := sgnlst[ind];
  //return [<xlst[i], sgns[i]*ylst[i], C!1> : i in [1..g]]; // TODO: use zlst
  ptseq := [<xlst[i], sgns[i]*ylst[i]> : i in [1..g]];
  return AffinePointsToProjectivePoints(ptseq, g, A`OddDegree,
                                        A`OddDegree select 0 else C!Sqrt(A`EvenLeadingCoefficient));
end intrinsic;

// See [Mumford, Tata Lectures on Theta II], p. 3.80 f., Theorem 5.3
intrinsic FromAnalyticJacobianXYZ(z::Mtrx[FldCom], A::RieSrf) -> SeqEnum
{This returns a divisor corresponding to z}
  require IsSuperelliptic(A) and Degree(A) eq 2: "The Riemann surface must be hyperelliptic.";
  g := Genus(A); //(#rts-1) div 2;
  C<i> := BaseRing(A); //Universe(rts);
  require C eq BaseRing(z) : "The first argument must have entries"*
  " in the base ring of the analytic Jacobian";
  require NumberOfRows(z) eq g :
    "The first argument does not have the correct number of rows";
  require NumberOfColumns(z) eq 1 :
    "The first argument must have one column";
  f := A`DefiningPolynomial;
  rts := Roots(f);  //A`Roots;
  assert (#rts - 1) div 2 eq g;
  rts := [r[1] : r in rts];
  //rts := AnalyticJacobian(f)`Roots;
  oddDegree := IsOdd(Degree(f));
  assert oddDegree; // TODO: treat even degree
  first_point_at_infinity := A![1];
  y_inf := Coordinates(first_point_at_infinity)[2];
  pres := Precision(C);
  bpmA := BigPeriodMatrix(A);
  om1 := Submatrix(bpmA, 1,g+1, g,g)^-1;
  nz := om1*z;
  V := {1..g+1};
  U := Uset(g);
  etaU  := eta(g,U);
  etaUV := eta(g,U sdiff V);
  etaUp := Submatrix(etaU,1,1,g,1);
  etaUVpp := Submatrix(etaUV,g+1,1,g,1);
  tau := SmallPeriodMatrix(A);
  thnullden := InternalTheta(Matrix(C,etaUV),Matrix(C,g,1,[]),tau);
  thetaden  := InternalTheta(Matrix(C,etaU ),nz,tau);
  /*for s in [[1,1/2,1/2,1/2], [1/2,1,1/2,1/2], [1/2,1/2,1,1/2], [1/2,1/2,1/2,1]] do //sigma in SymmetricGroup(2*g) do
    printf "char = %o: %o\n", s, InternalTheta(Matrix(C,2*g,1,s),nz,tau);
  end for;*/
  //printf "thnullden = %o\nthetaden = %o\n", thnullden, thetaden;
  if Abs(thetaden) lt 10^(-pres+10) then
  // We are on the theta divisor. Add a random point and subtract again
    //print "We are on the theta divisor. Add a random point and subtract again";
    Seeds, Seedc := GetSeed(); // save seed
    dum := Abs(thetaden);
    SetSeed(Round(dum*10^(-Round(Log(dum)/Log(10))+3))); // use deterministic seed
    //thex, they := RandomPoint(HyperellipticPolynomial(A));
    thept := RandomPoint(A); //thex, they := Explode(RandomPoint(A));
    SetSeed(Seeds, Seedc); // restore seed
    z2 := z+AbelJacobi(thept); // add a random point
    Plst := FromAnalyticJacobianXYZ(z2,A);
    assert forall{xyz[3] : xyz in Plst | Abs(xyz[3] - C!1) lt 10^(-pres+10)}; // not points at infinity
    dum := [Max(Abs(P[1]-thept[1]),Abs(P[2]-thept[2])) : P in Plst]; // find the point added in the divisor
    min, ind := Min(dum);
    assert min lt 10^(-Round(pres*0.8));
    Remove(~Plst,ind); // subtract again
    //return Plst;
    return [AffinePointToProjectivePoint(pt, g, oddDegree, y_inf) : pt in Plst];
  end if;
  cvec := [];
  M := Matrix(C,g,g,[]);
  for k in [1..g] do
    etak  := eta1(g,k);
    etakp := Submatrix(etak,1,1,g,1);
    etakpp := Submatrix(etak,g+1,1,g,1);
    thnullnum := InternalTheta(Matrix(C,etaUV+etak),Matrix(C,g,1,[]),tau);
    thetanum  := InternalTheta(Matrix(C,etaU +etak),nz,tau);
    ck := &*[rts[k]-rts[i] : i in V | not i eq k];
    ck := ck*(-1)^IntegerRing()!
          (4*(Transpose(etaUp)*etakpp + Transpose(etaUVpp)*etakp)[1,1]);
    ck := ck*(thnullnum*thetanum/(thnullden*thetaden))^2;
    Append(~cvec,ck-rts[k]^g);
    for j in [1..g] do
      M[k,j] := rts[k]^(g-j); // checkme: do we require a special ordering of rts? #rts = 2g + {1,2}, so we only take the first g roots!
      if rts[k] eq 0 then
        M[k,g] := 1;
      end if;
    end for;
  end for;
  cvec := Matrix(g,1,cvec);
  sx := Transpose(cvec)*Transpose(M)^-1; //MyCompInverse(Transpose(M));
  P<x> := PolynomialRing(C);
  F := P!Reverse(ElementToSequence(sx)) + x^g;
  xlst := Roots(F);  // This causes trouble if there are multiple roots...
  assert forall{x[2] : x in xlst | x[2] eq 1};
  xlst := [x[1] : x in xlst]; // find the x-coordinates of the points of the divisor
  //printf "xlst = %o\n", xlst;
  if not oddDegree then // if even degree model ... [TODO: do we need this for RieSrf?]
    xlst := [1/x+A`InfiniteRoot : x in xlst]; // Apply map to get point back on original model
  end if;
  ylst := [Sqrt(Evaluate(f,thex)) : thex in xlst]; // find y-coodinates of the points of the divisor up to sign
  zlst := [om1*AbelJacobi(A![xlst[i],ylst[i]]) : i in [1..g]]; // find z-coodinates of the points of the divisor up to sign
  sgnlst := [sgns : sgns in CartesianPower({-1,1}, g)];
  dlst :=
    [taured0Q(nz-&+[sgn[i]*zlst[i] : i in [1..g]],tau) : sgn in sgnlst];
  min,ind := Min(dlst);
  assert Abs(min) le 10^-10;
  sgns := sgnlst[ind];
  //return [<xlst[i], sgns[i]*ylst[i], C!1> : i in [1..g]]; // TODO: use zlst
  return [AffinePointToProjectivePoint(<xlst[i], sgns[i]*ylst[i]>, g, oddDegree, y_inf) : i in [1..g]];
end intrinsic;

/*
This uses formula 20 in "Equations for the Jacobian of a hyperelliptic curve"
*/

function etamod1(g,S)
  ans := ElementToSequence(eta(g,S));
  return Matrix(RationalField(),2*g,1,
    [((IntegerRing()!(2*e)) mod 2)/2 : e in ans]);
end function;

intrinsic RosenhainInvariants(tau::Mtrx) -> Set
{Given a small period matrix cooresponding to an analytic Jacobian, A,
of genus g this returns a set of 2g-1 complex numbers such that the
hyperelliptic curve y^2 = x(x-1) prod (x-s) for s in S has Jacobian
isomorphic to A.}
  C := BaseRing(tau);
  g := NumberOfRows(tau);
  V0 := {2..g+2};
  set := {};
  U := Uset(g);
  // Compute all characteristics that will be needed
  charlst := {};
  for j in [3..2*g+1] do
    if j in V0 then
      V := V0;
    else
      V := V0 sdiff {g+2,j};
    end if;
    UV := U sdiff V;
    Include(~charlst,etamod1(g,UV sdiff {j,-1}));
    Include(~charlst,etamod1(g,UV sdiff {2,1}));
    Include(~charlst,etamod1(g,UV sdiff {2,-1}));
    Include(~charlst,etamod1(g,UV sdiff {j,1}));
  end for;
  charlst := SetToSequence(charlst);
  // Compute theta nulls
  z := Matrix(C,g,1,[]);
  thetalst := [Theta(char,z,tau) : char in charlst];
  // Compute aj, j := 3..2g+1
  for j in [3..2*g+1] do
    if j in V0 then
      V := V0;
    else
      V := V0 sdiff {g+2,j};
    end if;
    UV := U sdiff V;
    ind1 := Index(charlst,etamod1(g,UV sdiff {j,-1}));
    ind2 := Index(charlst,etamod1(g,UV sdiff {2,1}));
    ind3 := Index(charlst,etamod1(g,UV sdiff {2,-1}));
    ind4 := Index(charlst,etamod1(g,UV sdiff {j,1}));
    aj := (thetalst[ind1]*thetalst[ind2]/(thetalst[ind3]*thetalst[ind4]))^2;
    Include(~set,aj);
  end for;
  return set;
end intrinsic;
