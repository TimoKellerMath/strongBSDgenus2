
// Make newform 169.2.a.b in Magma, downloaded from the LMFDB on 20 January 2023.
// To make the character of type GrpDrchElt, type "MakeCharacter_169_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_169_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_169_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [*1, -2, -1, 1*];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rf_num := [*\
[*1, 0, 0*],
[*0, 1, 0*],
[*-2, 0, 1*]*];
    Rf_basisdens := [*\
1,
1,
1*];
    Rf_basisnums := ChangeUniverse([[z : z in elt] : elt in Rf_num], Kf);
    Rfbasis := [Rf_basisnums[i]/Rf_basisdens[i] : i in [1..Degree(Kf)]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_169_a();"
function MakeCharacter_169_a()
    N := 169;
    order := 1;
    char_gens := [*2*];
    v := [*\
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_169_a_Hecke(Kf)
    return MakeCharacter_169_a();
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
    raw_aps := [*\
[*-1, 0, -1*],
        [*0, -1, 1*],
        [*-2, 1, -1*],
        [*-1, 1, 1*],
        [*-2, -1, 1*],
        [*0, 0, 0*],
        [*-1, -1, -2*],
        [*-1, -2, -1*],
        [*-3, 2, -2*],
        [*-3, 5, -3*],
        [*1, -5, 3*],
        [*3, 2, -1*],
        [*1, -4, 6*],
        [*6, -2, 3*],
        [*-6, 1, 1*],
        [*4, -4, 7*],
        [*-5, -4, 0*],
        [*-1, 6, -1*],
        [*-4, 6, -5*],
        [*-10, 3, 0*],
        [*4, -6, -3*],
        [*-4, -1, -8*],
        [*-6, 9, -2*],
        [*-6, 7, 0*],
        [*5, -1, 7*],
        [*6, -3, 10*],
        [*-4, 8, -1*],
        [*1, -3, -2*],
        [*4, 2, -6*],
        [*8, 1, -2*],
        [*-4, -9, 1*],
        [*-7, 5, 1*],
        [*8, -4, 0*],
        [*1, -11, 6*],
        [*3, 3, 0*],
        [*-5, 12, -2*],
        [*-5, 1, -5*],
        [*13, -1, -2*],
        [*-10, 2, -14*],
        [*0, -16, 8*],
        [*2, 5, -4*],
        [*7, -1, -8*],
        [*0, 4, 9*],
        [*8, -8, 10*],
        [*3, -8, 0*],
        [*-11, 6, -11*],
        [*2, -5, -5*],
        [*-9, 3, -3*],
        [*2, -8, 3*],
        [*-8, -8, 7*],
        [*-8, 3, -2*],
        [*-13, -3, 6*],
        [*0, -1, 11*],
        [*6, -2, 16*],
        [*11, -13, -5*],
        [*9, -6, 13*],
        [*-6, 3, 1*],
        [*-16, 14, -9*],
        [*0, 10, -5*],
        [*-8, 5, -6*],
        [*-12, 20, -14*],
        [*-17, 7, -16*],
        [*2, -2, -10*],
        [*1, -15, -3*],
        [*-9, -4, 7*],
        [*22, -8, 18*],
        [*-2, 0, -11*],
        [*-4, -5, 12*],
        [*-12, 2, -7*],
        [*-7, -4, 3*],
        [*5, 1, 7*],
        [*-17, 10, -18*],
        [*7, 11, 6*],
        [*10, -16, 5*],
        [*25, -13, 12*],
        [*2, -8, 16*],
        [*12, 2, 16*],
        [*-6, 11, -10*],
        [*10, 1, -9*],
        [*-16, 15, -21*],
        [*-22, -9, 2*],
        [*-18, -6, -5*],
        [*-11, -6, -10*],
        [*-4, 5, 7*],
        [*9, -9, 14*],
        [*18, -6, 4*],
        [*-10, 6, -11*],
        [*-16, 17, -8*],
        [*-12, -6, -7*],
        [*-3, 8, 5*],
        [*-29, 19, -30*],
        [*-27, -3, -2*],
        [*23, -11, 31*],
        [*12, 11, -8*],
        [*4, 15, -6*],
        [*-15, 21, -24*],
        [*0, -2, 9*],
        [*-19, -10, -2*],
        [*-24, 8, -5*],
        [*27, 0, 6*],
        [*9, 12, 5*],
        [*15, -9, 2*],
        [*-18, 7, -3*],
        [*-20, 10, -3*],
        [*-10, 7, 4*],
        [*27, 8, 3*],
        [*10, -9, -21*],
        [*-6, 14, 14*],
        [*9, -14, 5*],
        [*9, -6, 0*],
        [*0, -9, 22*],
        [*-8, -12, 7*],
        [*1, 20, -20*],
        [*4, -6, -3*],
        [*14, -3, -18*],
        [*29, 4, -1*],
        [*9, 17, -5*],
        [*4, -12, 16*],
        [*5, 15, -14*],
        [*25, -7, -1*],
        [*10, -25, 17*],
        [*23, -24, 11*],
        [*-26, 4, 6*],
        [*11, -10, 17*],
        [*29, -8, 13*],
        [*-11, -4, 20*],
        [*2, -31, 5*],
        [*-6, 9, -13*],
        [*-5, -3, -11*],
        [*6, -2, 27*],
        [*12, 10, -2*],
        [*-21, 1, 7*],
        [*6, 10, -16*],
        [*-7, 0, 22*],
        [*5, -24, 9*],
        [*-32, 23, -38*],
        [*-32, 8, 1*],
        [*-23, 19, -24*],
        [*-9, 15, 9*],
        [*-28, 16, -6*],
        [*-23, 17, -3*],
        [*9, 6, 21*],
        [*-17, 18, -6*],
        [*32, -23, 30*],
        [*25, -2, 5*],
        [*-14, 14, 14*],
        [*-36, -4, 0*],
        [*22, 8, -1*],
        [*-2, 8, 12*],
        [*-17, -8, -8*],
        [*21, -33, 11*],
        [*-34, 12, -13*],
        [*30, -21, 14*],
        [*15, -5, 8*],
        [*-5, -7, -9*],
        [*34, -12, 21*],
        [*14, 2, -7*],
        [*13, 9, -4*],
        [*26, -9, 6*],
        [*11, -12, 12*],
        [*1, -20, -8*],
        [*3, -9, -27*],
        [*7, -17, 24*],
        [*-3, -16, -8*],
        [*25, 0, -1*],
        [*-38, 13, -33*],
        [*-26, 12, -25*],
        [*3, 11, -13*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_169_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_169_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_169_2_a_b(:prec:=3)
    chi := MakeCharacter_169_a();
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
// containing the newform, type "MakeNewformModSym_169_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function MakeNewformModSym_169_2_a_b( : sign := +1)
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_169_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,sign)));
    Vf := Kernel([<2,R![-1, -1, 2, 1]>],Snew);
    return Vf;
end function;