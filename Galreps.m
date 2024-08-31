// Implement the algorithms in Section 2 of the paper

function get_coeffs(f, num : D := 0)
  // f: a newform
  // returns the Fourier coefficients of f for all primes <= num
  // if D ne 0, then take the quadratic twist of f by Q(sqrt(D))
  qexp := qExpansion(f, num);
  prs := PrimesUpTo(num);
  OK := Integers(CoefficientField(f));
  return [OK| Coefficient(qexp, p) * (D eq 0 select 1 else KroneckerCharacter(D)(p)) : p in prs], prs;
end function;

function check_frp(f, prs, cofs, frp)
  // f: a newform
  // prs: the primes up to some bound
  // cofs: the corresponding coefficients of f
  // frp: a prime ideal in the maximal order of Z[f]
  // Implements Algorithm 2.5.4
  N := Level(f);
  assert IsPrime(frp);
  p := MinimalInteger(frp);
  d := Degree(frp);
  S := {"R", "L", "Ns", "Nns", "S4", "A5"};
  if d eq 1 then
    S diff:= {"L", "A5"};
    if p eq 2 or p eq 3 then S diff:= {"Ns", "S4"}; end if;
  elif d eq 2 then
    if p eq 2 then
      S diff:= {"Ns", "S4", "A5"};
    elif p eq 3 then
      S diff:= {"Ns", "Nns", "S4"};
    elif p ge 5 and Valuation(N, p) le 1 then
      Exclude(~S, "Nns");
    end if;
    if p mod 10 notin {3, 7} then Exclude(~S, "A5"); end if;
  else
    error "degree of prime ideal is not 1 or 2";
  end if;
  if p mod 8 notin {3, 5} then Exclude(~S, "S4"); end if;
  F, toFp := ResidueClassField(frp);
  for i -> l in prs do
    if l ne p and not IsDivisibleBy(N, l) then
      u := toFp(cofs[i])^2/toFp(l);
      if p ne 2 then
        D := toFp(cofs[i])^2 - toFp(4*l);
        D := D eq 0 select 0 else IsSquare(D) select 1 else -1;
      end if;
      if u notin {F| 0, 1, 2, 4} then
        Exclude(~S, "S4");
      end if;
      if u notin {F| 0, 1, 4} and u^2 - 3*u + 1 ne 0 then
        Exclude(~S, "A5");
      end if;
      if d eq 2 and u^p ne u then
        Exclude(~S, "L");
        if p eq 2 then Exclude(~S, "R"); end if;
      end if;
      if p eq 2 and u eq 1 then
        Exclude(~S, d eq 1 select "R" else "Nns");
      elif p ne 2 and D eq -1 then
        S diff:= {"R", "L"};
        if u ne 0 then Exclude(~S, "Ns"); end if;
      elif p ne 2 and D eq 1 and u ne 0 then
        Exclude(~S, "Nns");
      end if;
      if IsEmpty(S) then return S; end if;
    end if;
  end for;
  return S;
end function;

function poss_red_type(f, prs, cofs, frp)
  // f: a newform
  // prs: the primes up to some bound
  // cofs: the corresponding coefficients of f
  // Assuming the representation is reducible, determine possible pairs
  // (ch, n) with a Dirichlet character ch of conductor|d_max and 0 <= n < (p-2)
  // such that the semi-simplification is (ch chi_p^n) + (ch^{-1} chi_p^{1-n})
  N := Level(f);
  dmax := &*[Integers()| e[1]^(e[2] div 2) : e in Factorization(N)];
  OK := Universe(cofs);
  F, toF := ResidueClassField(frp);
  p := MinimalInteger(frp);
  if IsDivisibleBy(dmax, p) and Valuation(N, p) le 3 then
    // the p-parts of the Dirichlet characters are powers of chi_p --> redundant
    dmax := ExactQuotient(dmax, p);
  end if;
  DG := DirichletGroup(dmax, F);
  cands := {<ch, n> : ch in Elements(DG), n in [0] cat [2..(p-1) div 2]};
  for i -> l in prs do
    if l ne p and not IsDivisibleBy(N, l) then
      // compare a_l with all possible values of ch(l)*l^n + l/(ch(l)*l^n)
      cands := {chn : chn in cands | toF(cofs[i]) eq a + l/a where a := chn[1](l)*l^chn[2]};
    end if;
  end for;
  return cands;
end function;

function poss_non_irr(f, prs, cofs)
  // f: a newform
  // prs: the primes up to some bound
  // cofs: the corresponding coefficients of f
  // Implements Algorithm 2.8.4
  N := Level(f);
  Nf := Factorization(N);
  dmax := &*[e[1]^(e[2] div 2) : e in Nf];
  R := Universe(cofs);
  I := ideal<R | 0>;
  if dmax le 2 then
    // order = 1, no resultant necessary
    for i -> l in prs do
      if not IsDivisibleBy(N, l) then
        I +:= ideal<R | l*(l + 1 - cofs[i])>;
      end if;
    end for;
  else
    RT<T> := PolynomialRing(R : Global := false);
    for i -> l in prs do
      if not IsDivisibleBy(N, l) then
        m := Order(l, dmax);
        I +:= ideal<R | l*Resultant(T^2 - cofs[i]*T + l, T^m - 1)>;
      end if;
    end for;
  end if;
  If := Factorization(I);
  return Sort(Setseq(Set(&cat[[e[1] : e in Decomposition(R, p[1])] : p in Nf | p[2] ge 2]) // 2.8.4 excludes p^2 | N
                      join Set({e[1] : e in If})));
end function;

function poss_tors(f, prs, cofs)
  // f: a newform
  // prs: the primes up to some bound
  // cofs: the corresponding coefficients of f
  // Implements Algorithm 2.8.4
  N := Level(f);
  Nf := Factorization(N);
  R := Universe(cofs);
  I := ideal<R | 0>;
  for i -> l in prs do
    if l gt 2 and not IsDivisibleBy(N, l) then
      I +:= ideal<R | (l + 1 - cofs[i])>;
    end if;
  end for;
  If := Factorization(I);
  return [e[1] : e in If];
end function;

function poss_subline(f, prs, cofs)
  // f: a newform
  // prs: the primes up to some bound
  // cofs: the corresponding coefficients of f
  // Implements Algorithm 2.9.1
  N := Level(f);
  OK := Universe(cofs);
  disc := Discriminant(CoefficientRing(f));
  flag, sd := IsSquare(OK!disc);
  assert flag;
  R := 0;
  for i -> l in prs do
    if not IsDivisibleBy(N, l) then
      t := Trace(cofs[i]);
      R := GCD(R, l*Integers()!ExactQuotient(t*(2*cofs[i]-t), sd));
      if R eq 1 then break; end if;
    end if;
  end for;
  result := [Parent(Decomposition(OK, 2)[1,1])| ];
  for p in PrimeDivisors(R) do
    if p ne 2 then
      dec := Decomposition(OK, p);
      if #dec eq 1 and Degree(dec[1,1]) eq 2 then
        Append(~result, dec[1,1]);
      end if;
    end if;
  end for;
  return result;
end function;

function characters(d)
  // Returns a sequence containing all nontrivial quadratic characters mod d
  DG := DirichletGroup(d);
  return [ch : ch in Elements(DG) | not IsTrivial(ch)];
end function;

//intrinsic galrep_info(f::ModFrmElt, num::RngIntElt : D := 0) -> SeqEnum
function galrep_info(f, num : D := 0)
/*{ This implements Algorithm 2.11.3: for a given newform f, it determines the
  possible types of non-maximal Galois representations. num is a bound for the
  test primes. D, if given, must be coprime to the level of f, and has the effect
  of twisting f by the quadratic character associated to D. }*/
  cofs, prs := get_coeffs(f, num : D := D);
  N := Level(f) * (D eq 0 select 1 else D^2);
  OK := Universe(cofs);
  HT := AssociativeArray();
  Sred := Set(poss_non_irr(f, prs, cofs));
  Ssl := Set(poss_subline(f, prs, cofs));
  Nf := Factorization(N);
  //bad_p := (LegendreSymbol(Discriminant(OK), 3) eq -1 select [3, 5] else [5])
  bad_p := [2, 3, 5]
             cat [e[2] : e in Nf | e[1] ge 7 and e[2] ge 2];
  Sexc := Set(&cat[[e[1] : e in Decomposition(OK, p)] : p in bad_p]);
  d := &*[Integers()| e[1] : e in Nf | e[1] ne 2 and e[2] ge 2];
  if IsDivisibleBy(N, 4) then d *:= 8; end if;
  if d ne 1 then
    chars := characters(d);
    Is := [ideal<OK | 0> : ch in chars];
    for i -> l in prs do
      if not IsDivisibleBy(N, l) then
        for j -> ch in chars do
          if ch(l) eq -1 then
            Is[j] +:= ideal<OK | l*cofs[i]>;
          end if;
        end for;
      end if;
    end for;
    SNC := {Parent(ideal<OK | 0>)| };
    for I in Is do
      SNC join:= {e[1] : e in Factorization(I)};
    end for;
  else
    SNC := {};
  end if;
  for frp in Sred join Ssl join Sexc join SNC do
    S := {"R", "L", "Ns", "Nns", "S4", "A5"};
    if frp notin Sred then Exclude(~S, "R"); end if;
    if frp notin Ssl then Exclude(~S, "L"); end if;
    if frp notin Sexc then S diff:= {"S4", "A5"}; end if;
    if frp notin SNC and MinimalInteger(frp) ne 2 then
      S diff:= {"Ns", "Nns"};
    end if;
    HT[frp] := S;
  end for;
  keys := Keys(HT);
  for frp in keys do
    HT[frp] meet:= check_frp(f, prs, cofs, frp);
  end for;
  result := [Parent(<Rep(Sexc), {"R"}>)| ];
  for frp in keys do
    S := HT[frp];
    if not IsEmpty(S) then
      Append(~result, <frp, S>);
    end if;
  end for;
  return Sort(result, func<x, y | MinimalInteger(x[1]) - MinimalInteger(y[1])>);
end function;

procedure print_info(gi)
  last_p := 1;
  count := 0;
  if IsEmpty(gi) then
    printf "\n";
    return;
  end if;
  for i -> pair in gi do
    frp, S := Explode(pair);
    p := MinimalInteger(frp);
    d := Degree(frp);
    e := RamificationIndex(frp);
    if p eq last_p then
      count +:= 1;
    else
      count := 1;
    end if;
    printf "%o%o:", p, d eq 1 select (e eq 2 select "_r" else "_"*IntegerToString(count)) else "";
    for s in S do printf " %o", s; end for;
    printf i eq #gi select "\n" else ", ";
    last_p := p;
  end for;
end procedure;

function newforms_dim2(N)
  // N: level
  nf := Newforms(CuspForms(N));
  return [*e[1] : e in nf | #e eq 2*];
end function;

function galreps_level(N : num := 100)
  nf := newforms_dim2(N);
  result := [**];
  for i -> f in nf do
    gi := galrep_info(f, num);
    printf "N = %o, form %o: ", N, i;
    print_info(gi);
    Append(~result, gi);
  end for;
  return result;
end function;

function serialize_prid(pr)
  // pr: prime ideal of an order
  gens := Generators(pr);
  R := Universe(gens);
  assert Degree(R) eq 2 and MinimalPolynomial(R.1) eq Polynomial([-1,1]);
  return <MinimalInteger(pr), Eltseq(MinimalPolynomial(R.2)), [Eltseq(g) : g in gens]>;
end function;

procedure print_gi(gi)
  printf "[";
  for i -> e in gi do
    prs := serialize_prid(e[1]);
    printf i eq 1 select " " else "  ";
    printf "<%o, %o, [", prs[1], prs[2];
    for j -> s in prs[3] do
      printf "%o", s;
      printf j eq #prs[3] select "], {" else ", ";
    end for;
    for j -> t in Setseq(e[2]) do
      printf "\"%o\"", t;
      printf j eq #e[2] select "}> " else ", ";
    end for;
    printf i eq #gi select "" else ",\n";
  end for;
  printf "]";
end procedure;

trans := AssociativeArray();
trans["R"] := "Borel";
trans["L"] := "sub-line";
trans["Ns"] := "$N(C_{s})$";
trans["Nns"] := "$N(C_{ns})$";
trans["S4"] := "$S_4$";
trans["A5"] := "$A_5$";

procedure print_ch_pow(p, n)
  if n eq 0 then
    printf "\\mathbf{1}";
  elif n eq 1 then
    printf "\\chi_{%o}", p;
  else
    printf "\\chi_{%o}^{%o}", p, n;
  end if;
end procedure;

// function move_ideal(frp, O)
//   // transfer the ideal frp to an isomorphic order
//   mipo := MinimalPolynomial(Order(frp).2);
//
// end function;

// uses DB from database.magma
//intrinsic print_table_line(entry::.)
procedure print_table_line(entry)
//{ entry is an entry in the database. This prints LaTeX code to produce a line
//  in the table of Galois representations. }
  printf "  %3o&%o & ", entry`N, Split(entry`label, ".")[2];
  bad := [e[1] : e in Factorization(entry`N) | e[2] ge 2];
  if IsEmpty(bad) then
    printf "& ";
  else
    printf "%o & ", bad;
  end if;
  // output discriminant of endomorphism ring
  printf "$\\sqrt{%o}$ & ", entry`discO_J;
  // for each possibly non-max. rep., give some info
  f := entry`f;
  cofs, prs := get_coeffs(f, 100);
  gi := entry`galreps;
  last_p := 1;
  // print the reducible frp
  for i -> info in gi do
    if not "R" in info [2] then
      continue;
    end if;
    frp := info[1];
    p := MinimalInteger(frp);
    if Degree(frp) eq 1 then
      if RamificationIndex(frp) eq 1 then
        printf "$\\frp_{%o}%o$: ", p, p eq last_p select "''" else "'";
      else
        printf "$\\frp_{%o}$: ", p;
      end if;
    elif Degree(frp) eq 2 then
      printf "$%o$: ", p;
    else
      error "prime ideal has too large degree";
    end if;
    invs := [i : i in entry`JQ_invs | i ne 0];
    texp := IsEmpty(invs) select 1 else invs[#invs]; // exponent of rational torsion subgroup
    if "R" in info[2] and #[e : e in gi | MinimalInteger(e[1]) eq p and "R" in e[2]] eq 1
                      and IsDivisibleBy(texp, p) then
      printf "$\\mathbf{1} \\oplus \\chi_{%o}$", p;
    else
      for j -> t in Setseq(info[2]) do
        if t eq "R" then
          cands := poss_red_type(f, prs, cofs, frp);
          if #cands eq 1 then
            chn := Rep(cands);
            if IsTrivial(chn[1]) then
              printf "%o ($", trans[t];
              print_ch_pow(p, chn[2]);
              printf " \\oplus ";
              print_ch_pow(p, (1 - chn[2]) mod (p-1));
              printf "$)";
            else
              printf trans[t];
            end if;
          else
            printf trans[t];
          end if;
        else
          printf trans[t];
        end if;
        printf j eq #info[2] select "" else ", ";
      end for;
    end if;
    last_p := p;
    printf i eq #gi select "" else ";\\quad ";
  end for;
  // print the remaining non-maximal frp
  printf " & ";
  for i -> info in gi do
    if "R" in info [2] then
      continue;
    end if;
    frp := info[1];
    p := MinimalInteger(frp);
    if Degree(frp) eq 1 then
      if RamificationIndex(frp) eq 1 then
        printf "$\\frp_{%o}%o$: ", p, p eq last_p select "''" else "'";
      else
        printf "$\\frp_{%o}$: ", p;
      end if;
    elif Degree(frp) eq 2 then
      printf "$%o$: ", p;
    else
      error "prime ideal has too large degree";
    end if;
    invs := [i : i in entry`JQ_invs | i ne 0];
    texp := IsEmpty(invs) select 1 else invs[#invs]; // exponent of rational torsion subgroup
    if "R" in info[2] and #[e : e in gi | MinimalInteger(e[1]) eq p and "R" in e[2]] eq 1
                      and IsDivisibleBy(texp, p) then
      printf "$\\mathbf{1} \\oplus \\chi_{%o}$", p;
    else
      for j -> t in Setseq(info[2]) do
        if t eq "R" then
          cands := poss_red_type(f, prs, cofs, frp);
          if #cands eq 1 then
            chn := Rep(cands);
            if IsTrivial(chn[1]) then
              printf "%o ($", trans[t];
              print_ch_pow(p, chn[2]);
              printf " \\oplus ";
              print_ch_pow(p, (1 - chn[2]) mod (p-1));
              printf "$)";
            else
              printf trans[t];
            end if;
          else
            printf trans[t];
          end if;
        else
          printf trans[t];
        end if;
        printf j eq #info[2] select "" else ", ";
      end for;
    end if;
    last_p := p;
    printf i eq #gi select "" else ";\\quad ";
  end for;
  printf " \\\\\n";
end procedure;
