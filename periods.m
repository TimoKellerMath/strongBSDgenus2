
/*import "/opt/magma/magma-2.28-2/package/Geometry/ModSym/multichar.m" :
  AssociatedNewformSpace,
  HasAssociatedNewformSpace,
  MC_ConvToModularSymbol;

import "/opt/magma/magma-2.28-2/package/Geometry/ModSym/analytic.m" :
  PeriodGenerators;

import "/opt/magma/magma-2.28-2/package/Geometry/ModSym/core.m" :
  ConvFromModularSymbol;

import "/opt/magma/magma-2.28-2/package/Geometry/ModSym/period.m" :
  RationalPeriodMapping;

import "/opt/magma/magma-2.28-2/package/Geometry/ModSym/linalg.m" :
  MakeLattice;

import "/opt/magma/magma-2.28-2/package/Geometry/ModSym/operators.m" :
  AtkinLehnerSign;
*/

/*
import "/opt/magma/current/package/Geometry/ModSym/multichar.m" :
  AssociatedNewformSpace,
  HasAssociatedNewformSpace,
  MC_ConvToModularSymbol;

import "/opt/magma/current/package/Geometry/ModSym/analytic.m" :
  PeriodGenerators;

import "/opt/magma/current/package/Geometry/ModSym/core.m" :
  ConvFromModularSymbol;

import "/opt/magma/current/package/Geometry/ModSym/period.m" :
  RationalPeriodMapping;

import "/opt/magma/current/package/Geometry/ModSym/linalg.m" :
  MakeLattice;

import "/opt/magma/current/package/Geometry/ModSym/operators.m" :
  AtkinLehnerSign;
*/


import "/usr/local/magma/package/Geometry/ModSym/multichar.m" :
  AssociatedNewformSpace,
  HasAssociatedNewformSpace,
  MC_ConvToModularSymbol;

import "/usr/local/magma/package/Geometry/ModSym/analytic.m" :
  PeriodGenerators;

import "/usr/local/magma/package/Geometry/ModSym/core.m" :
  ConvFromModularSymbol;

import "/usr/local/magma/package/Geometry/ModSym/period.m" :
  RationalPeriodMapping;

import "/usr/local/magma/package/Geometry/ModSym/linalg.m" :
  MakeLattice;

import "/usr/local/magma/package/Geometry/ModSym/operators.m" :
  AtkinLehnerSign;


function Int1(alp, m, n, C)
   c := 2*Pi(C)*C.1*n;
   return
      Exp(c*alp)
      * &+[(-1)^s *(alp^(m-s)) / c^(s+1) * (&*[Integers()|i : i in [m-s+1..m]])
          : s in [0..m]];
end function;


/////////////////////////////////////////////////////////////
// Compute Int_{alp}^{oo} P(z)*f(q) dz, using              //
// an explicit formula derived via integration by parts.   //
/////////////////////////////////////////////////////////////
function Int2(f, alp, m : prec := 30)
   C := ComplexField(prec);
   return &+[Int1(alp,m,n,C)*(C!Coefficient(f,n)) : n in [1..Degree(f)]];
end function;


function PeriodIntegral(f, P, alpha : prec := 30)
   // {Computes <f, P\{alpha,oo\}> = -2*pi*I*Int_{alp}^{oo} P(z) f(q) dz
   // for alpha any point
   // in the upper half plane.}
   C := ComplexField(prec); i := C.1;
   return -2*Pi(C)*i* &+[Int2(f,alpha,m : prec := prec)* (C!Coefficient(P,m))
               : m in [0..Degree(P)] | Coefficient(P,m) ne 0];
end function;

////////////////////////////////////////////////////////////////
// In the following, "fast" refers to using the Fricke        //
// involution trick to speed convergence.  This only works    //
// in some cases, so we have also implemented a standard      //
// slow method which should work in all cases.                //
////////////////////////////////////////////////////////////////

function FastPeriodIntegral(A, f, Pg : prec := 30)
// Compute <f, Pg[1]*\{oo, Pg[2](oo)\}>.
   //assert IsNew(A);

   P, g := Explode(Pg);
   if g[3] eq 0 then // g(oo)=oo.
      return 0;
   end if;
   if g[4] lt 0 then
      g[1] *:= -1; g[2] *:= -1; g[3] *:= -1; g[4] *:= -1;
   end if;

   R    := Parent(P);
   phi  := hom <R -> R  |  g[1]*R.1+g[2]*R.2, g[3]*R.1+g[4]*R.2>;
   giP  := phi(P) / (g[1]*g[4]-g[2]*g[3]);
   assert giP eq P;


   C := ComplexField(prec); i := C.1;

   N    := Level(A);
   k    := Weight(A);
   e    := AtkinLehnerSign(A);
   rootN:= Sqrt(C!Level(A));
   PI   := Pi(C);
   a    := g[1];
   b    := g[2];
   c    := g[3] div N;
   d    := g[4];
   if k eq 2 then     // the formula takes a simpler form when k=2.
      vprint ModularSymbols : "Computing period integrals (fast): loop over a_n(f).";
      /*cn := [
         (e-1)*Exp(-2*PI*n/rootN)
              + Exp(-2*PI*n/(d*rootN))*(Exp(2*PI*i*n*b/d)-e*Exp(2*PI*i*n*c/d))
                  : n in [1..Degree(f)]
            ];
      return &+[(Coefficient(f,n)/n) * cn[n] : n in [1..Degree(f)]];*/
      result := C!0;
      for n in [1..Degree(f)] do
         result +:= Coefficient(f,n)/n * ((e-1)*Exp(-2*PI*n/rootN)
         + Exp(-2*PI*n/(d*rootN))*(Exp(2*PI*i*n*b/d)-e*Exp(2*PI*i*n*c/d)));
      end for;
      return result;

   else
      /* The following formula is in my (William Stein)
         Ph.D. thesis.  It generalizes Cremona's Prop 2.10.3
         to the case of higher weight modular symbols. */
      W  := hom <R -> R  |  R.2, -N*R.1>;
      WP := W(P)/N^(Integers()!(k/2-1));

      S := PolynomialRing(Rationals()); z := S.1;
      ev   := hom <R -> S | z, 1>;
      P    := ev(P);
      WP   := ev(WP);
      ans  :=  PeriodIntegral(f,  P-e*WP, i/rootN : prec := prec)
              +PeriodIntegral(f,    e*WP, c/d+i/(d*rootN) : prec := prec)
              +PeriodIntegral(f, -P     , b/d+i/(d*rootN) : prec := prec);
      return ans;
   end if;
end function;

function SlowPeriodIntegral(A, f, Pg : prec := 30)
/* A::ModSym,  f::RngSerPowElt, Pg::Tup) -> FldComElt
 Given a homogeneous polynomial P(X,Y) of degree k-2,
 a 2x2 matrix g=[a,b,c,d], and a q-expansion f of a weight k
 modular form, this function returns the period
 <f, P {oo,g(oo)}> = -2*pi*I*Int_{oo,g(oo)} P(z,1) f(z) dz.
   Resort to VERY SLOWLY CONVERGING METHOD.
   We have, for any alp in the upper half plane,
      <f, P{oo,g(oo)}>
       = <f, P{oo,alp} + P{alp, g(alp)} +         P{g(alp),g(oo)}>
       = <f, P{oo,alp} + P{alp, g(alp)} + (eps(g)g^(-1)P){alp,oo}>
       = <f, ((eps(g)g^(-1)P)-P){alp, oo} + P{alp, oo} - P{g(alp),oo}>
       = <f, (eps(g)g^(-1)P){alp, oo} - P{g(alp),oo}>.
      The integrals converge best when Im(alp) and Im(g(alp))
      are both large.  We choose alp=i/c.
      ************/

   P, g := Explode(Pg);
   if g[3] eq 0 then // g(oo)=oo.
      return 0;
   end if;

   R    := Parent(P);
   phi  := hom <R -> R  |  g[1]*R.1+g[2]*R.2, g[3]*R.1+g[4]*R.2>;
   giP  := phi(P) / (g[1]*g[4]-g[2]*g[3]);

   C := ComplexField(prec); i := C.1;

   if g[3] lt 0 then   // g(oo) = (-g)(oo), since g acts through PSL.
      g[1] *:= -1; g[2] *:= -1; g[3] *:= -1; g[4] *:= -1;
   end if;

   alp  := (-g[4]+i)/g[3];
   galp := (g[1]*alp + g[2])/(g[3]*alp+g[4]);
   S := PolynomialRing(Rationals()); z := S.1;
   ev   := hom <R -> S | z, 1>;
   P    := ev(P);
   giP  := ev(giP);
   eps_g:= C!Evaluate(DirichletCharacter(A),g[1]);
   return eps_g*PeriodIntegral(f,giP,alp : prec := prec) - PeriodIntegral(f,P,galp : prec := prec);
end function;

intrinsic PeriodMappingModSym(A::ModSym, prec::RngIntElt, n::RngIntElt) -> Map
{The complex period mapping to precision prec, computed using n terms of q-expansion.
 The period map is a homomorphism M --> C^d, where d is the
 dimension of A.}
   require Sign(A) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(A) : "Argument 1 must be cuspidal.";

   if IsMultiChar(A) then
      require HasAssociatedNewformSpace(A) : "Argument 1 must be created using NewformDecomposition.";
      M := AssociatedNewformSpace(A);
      phi := PeriodMappingModSym(M,prec,n);
      A`PeriodMapPrecision := n;
      return hom< AmbientSpace(A) -> Codomain(phi) |
                   x :-> phi(M!MC_ConvToModularSymbol(AmbientSpace(A),x)) > ;
   end if;

   if not assigned A`PeriodMap or A`PeriodMapPrecision lt n then
      vprint ModularSymbols : "Computing period mapping.";
      k  := Weight(A);

      /****************************************************************
      * If fast = true then we can use tricks arising from the       *
      * Atkin-Lehner involution to greatly speed of the convergence  *
      * of the series.  If fast = false we rely on a simplistic      *
      * method which gives series that do not converge as quickly.   *
      ****************************************************************/
      fast := (Level(A) gt 1) and (k mod 2 eq 0)
               and IsTrivial(DirichletCharacter(A))
               and IsScalar(AtkinLehner(A,Level(A)));

      vprint ModularSymbols : "Computing period generators.";
      G, fast  := PeriodGenerators(A, fast);

      vprint ModularSymbols : "Computing an integral basis.";
      Q  := qIntegralBasis(A, n);
      // A is cuspidal with sign 0, so dimension is twice as large
      dim := Dimension(A) * AbsoluteDegree(BaseRing(A)) / 2;
      if #Q ne dim then
         require #Q le dim : "Too many q-expansions!";
         require #Q eq dim : "The precision ( =", prec, ") is too low";
      end if;
      vprint ModularSymbols : "Found integral basis, now creating C^d.";
      C := ComplexField(prec); i := C.1;
      Cd := VectorSpace(C,DimensionComplexTorus(A)*Degree(BaseField(A)));

      if fast then
         vprintf ModularSymbols : "\t\t(Using WN trick.)\n";
      end if;

      if fast then
         vprint ModularSymbols : "Computing period integrals (fast).";
         P  := [Cd![FastPeriodIntegral(A,Q[i],x : prec := prec) : i in [1..#Q]] : x in G];
      else
         vprint ModularSymbols : "Computing period integrals (slow).";
         P  := [Cd![SlowPeriodIntegral(A,Q[i],x : prec := prec) : i in [1..#Q]] : x in G];
      end if;

      vprint ModularSymbols : "Constructing period mapping from integrals.";
      M    := AmbientSpace(A);
      star := StarInvolution(M);
      gens := &cat[[v + v*star, v - v*star] where v is
                   ConvFromModularSymbol(M,
                [ <x[1],[[1,0],[x[2][1],x[2][3]]]>] )
                         : x in G];
      vprintf ModularSymbols : "Computed %o generators.\n", #gens;
      // images of the gens
      periods := &cat[[2*Cd![Real(z):z in Eltseq(x)],
                       2*i*Cd![Imaginary(z):z in Eltseq(x)]] : x in P];

      vprint ModularSymbols : "Computing RationalPeriodMapping.";
      pi := RationalPeriodMapping(A);
      vprint ModularSymbols : "Computing Representation.";
      PG := [ pi(Representation(g)) : g in gens];
      V  := VectorSpaceWithBasis(PG);

      vprint ModularSymbols : "Computing DualRepresentation.";
      IMAGES :=
        [ &+[periods[i]*coord[i] : i in [1..#coord]] where
                       coord is Coordinates(V, pi(b))
            :        b in Basis(DualRepresentation(M))  ];
      A`PeriodMapPrecision := n;
      W := VectorSpace(ComplexField(prec),Degree(IMAGES[1]));

      vprint ModularSymbols : "Computing PeriodMap.";
      A`PeriodMap := hom<AmbientSpace(A)->W | x :-> &+[y[i]*IMAGES[i] : i in [1..#y]] where
                                 y := Eltseq(x)>;
      vprint ModularSymbols : "done.";
   end if;
   return A`PeriodMap;
end intrinsic;


intrinsic PeriodsModSym(M::ModSym, prec::RngIntElt, n::RngIntElt) -> SeqEnum
{The complex period lattice associated to A using n terms of the q-expansions.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Type(BaseField(M)) eq FldRat : "The base ring of M must be the rational field.";

   if not assigned M`period_lattice  or M`PeriodMapPrecision lt n then
      phi := PeriodMappingModSym(M,prec,n);  // compute to precision n.
      vprint ModularSymbols : "Computed PeriodMappingModSym.";
      pi := RationalMapping(M);
      vprint ModularSymbols : "Computed RationalMapping.";
      L,psi := Lattice(CuspidalSubspace(AmbientSpace(M))); // this takes a huge amount of memory!
      vprint ModularSymbols : "Computed Lattice.";
      piL := [pi(psi(x)) : x in Basis(L)];
      P := MakeLattice(piL);
      B := Basis(P);
      vprint ModularSymbols : "Computing LatticeWithBasis.";
      V := LatticeWithBasis(RMatrixSpace(RationalField(),#B,#B)!&cat[Eltseq(b) : b in B]);
      vprint ModularSymbols : "done.";

      // Now find a set B of elements of L that map onto a basis for W.
      A := RMatrixSpace(IntegerRing(), Rank(L), #B)!
                            &cat[Coordinates(V,V!x) : x in piL];
      Z := RSpace(IntegerRing(),#B);

      C := [];
      for i in [1..#B] do
         x := Solution(A,Z.i);
         t := x[1]*psi(Basis(L)[1]);
         for j in [2..Rank(L)] do
            if x[j] ne 0 then
               t +:= x[j]*psi(Basis(L))[j];
            end if;
         end for;
         Append(~C, t);
      end for;
      M`period_lattice := [phi(z) : z in C];
   end if;
   return M`period_lattice;
end intrinsic;
