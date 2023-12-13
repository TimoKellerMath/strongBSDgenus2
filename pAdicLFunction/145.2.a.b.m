
// Make newform 145.2.a.b in Magma, downloaded from the LMFDB on 30 November 2023.
// To make the character of type GrpDrchElt, type "MakeCharacter_145_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_145_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_145_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [-2, 0, 1];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rfbasis := [Kf.1^i : i in [0..Degree(Kf)-1]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_145_a();"
function MakeCharacter_145_a()
    N := 145;
    order := 1;
    char_gens := [117, 31];
    v := [1, 1];
    // chi(gens[i]) = zeta^v[i]
    assert UnitGenerators(DirichletGroup(N)) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_145_a_Hecke(Kf)
    return MakeCharacter_145_a();
end function;


function ExtendMultiplicatively(weight, aps, character)
    prec := NextPrime(NthPrime(#aps)) - 1; // we will able to figure out a_0 ... a_prec
    primes := PrimesUpTo(prec);
    prime_powers := primes;
    assert #primes eq #aps;
    log_prec := Floor(Log(prec)/Log(2)); // prec < 2^(log_prec+1)
    F := Universe(aps);
    FXY<X, Y> := PolynomialRing(F, 2);
    // 1/(1 - a_p T + p^(weight - 1) * char(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
    R<T> := PowerSeriesRing(FXY : Precision := log_prec + 1);
    recursion := Coefficients(1/(1 - X*T + Y*T^2));
    coeffs := [F!0: i in [1..(prec+1)]];
    coeffs[1] := 1; //a_1
    for i := 1 to #primes do
        p := primes[i];
        coeffs[p] := aps[i];
        b := p^(weight - 1) * F!character(p);
        r := 2;
        p_power := p * p;
        //deals with powers of p
        while p_power le prec do
            Append(~prime_powers, p_power);
            coeffs[p_power] := Evaluate(recursion[r + 1], [aps[i], b]);
            p_power *:= p;
            r +:= 1;
        end while;    
    end for;
    Sort(~prime_powers);
    for pp in prime_powers do
        for k := 1 to Floor(prec/pp) do
            if GCD(k, pp) eq 1 then
                coeffs[pp*k] := coeffs[pp]*coeffs[k];
            end if;
        end for;
    end for;
    return coeffs;
end function;


function qexpCoeffs()
    // To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
    weight := 2;
    raw_aps := [[-1, 1], [-2, 0], [1, 0], [-2, -2], [-2, 2], [-2, 0], [0, 2], [-2, -2], [-6, 2], [1, 0], [-2, 6], [0, -6], [-6, 0], [-6, 0], [-6, -4], [2, -4], [0, 0], [2, -4], [-2, 6], [-4, -8], [0, 6], [6, -6], [10, -2], [-2, -4], [-4, -6], [10, 4], [2, 10], [6, 10], [2, 0], [0, -2], [6, 0], [2, -10], [-8, 2], [16, 4], [-2, 8], [-12, 0], [-8, 6], [-14, 4], [6, -6], [6, 8], [-12, -8], [-6, 0], [-18, -2], [-4, 6], [-14, -4], [12, 0], [2, -2], [2, -14], [6, 10], [-2, 0], [18, 0], [-12, 8], [10, 0], [6, 2], [18, -8], [-14, -4], [-10, -8], [10, -14], [2, -4], [-18, -8], [2, 2], [0, 6], [-6, -12], [6, 6], [-6, 0], [0, 2], [2, 14], [-4, 2], [6, -10], [-2, 16], [-10, 4], [-18, 10], [18, 0], [10, -12], [14, 6], [-6, 6], [-18, -8], [-14, -4], [-18, 8], [14, -12], [12, 12], [2, 12], [-8, 8], [-32, 2], [-16, 4], [-2, -4], [6, 4], [14, 4], [-30, -4], [2, 14], [-6, 12], [10, -2], [-10, 14], [18, -18], [36, 0], [-30, 0], [-22, 16], [-10, -8], [-6, 6], [-22, 12], [6, -6], [6, -24], [2, 4], [22, 4], [28, 0], [4, 14], [-10, -14], [-2, -4], [-18, -14], [2, 0], [26, -12], [-2, 0], [-12, 2], [10, -14], [20, 12], [-22, 16], [-6, 18], [-10, -22], [-20, 2], [-18, 14], [26, 0], [6, 12], [0, -26], [26, -10], [-28, -12], [18, -8], [-22, 0], [-12, -16], [10, -24], [-20, -2], [6, 6], [-30, -16], [2, 10], [28, -6], [-14, 16], [-10, -4], [0, -6], [-2, 14], [-20, 10], [14, 20], [32, 4], [-34, 8], [-14, -12], [6, 8], [-2, 16], [-6, 6], [20, 22], [26, -16], [-14, -30], [-22, -10], [10, 20], [18, 8], [-6, -6], [-18, 8], [-10, 0], [18, 10], [-36, 0], [18, -16], [14, 4], [6, -24], [-6, 36], [18, 8], [-2, 12], [14, 10], [-14, 8], [2, -8], [52, 0], [4, 2]];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_145_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_145_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_145_2_a_b(:prec:=2)
    chi := MakeCharacter_145_a();
    f_vec := qexpCoeffs();
    Kf := Universe(f_vec);
    // SetVerbose("ModularForms", true);
    // SetVerbose("ModularSymbols", true);
    S := CuspidalSubspace(ModularForms(chi, 2));
    S := BaseChange(S, Kf);
    maxprec := NextPrime(997) - 1;
    while true do
        trunc_vec := Vector(Kf, [0] cat [f_vec[i]: i in [1..prec]]);
        B := Basis(S, prec + 1);
        S_basismat := Matrix([AbsEltseq(g): g in B]);
        if Rank(S_basismat) eq Min(NumberOfRows(S_basismat), NumberOfColumns(S_basismat)) then
            S_basismat := ChangeRing(S_basismat,Kf);
            f_lincom := Solution(S_basismat,trunc_vec);
            f := &+[f_lincom[i]*Basis(S)[i] : i in [1..#Basis(S)]];
            return f;
        end if;
        error if prec eq maxprec, "Unable to distinguish newform within newspace";
        prec := Min(Ceiling(1.25 * prec), maxprec);
    end while;
end function;


// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_145_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function MakeNewformModSym_145_2_a_b( : sign := -1)
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_145_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,sign)));
    Vf := Kernel([<2,R![-1, 2, 1]>],Snew);
    return Vf;
end function;