
// Make newform 23.2.a.a in Magma, downloaded from the LMFDB on 14 June 2023.
// To make the character of type GrpDrchElt, type "MakeCharacter_23_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_23_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_23_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [*-1, -1, 1*];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rfbasis := [Kf.1^i : i in [0..Degree(Kf)-1]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_23_a();"
function MakeCharacter_23_a()
    N := 23;
    order := 1;
    char_gens := [*5*];
    v := [*
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_23_a_Hecke(Kf)
    return MakeCharacter_23_a();
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
    raw_aps := [*
[*0, -1*],
        [*-1, 2*],
        [*0, -2*],
        [*2, -2*],
        [*-4, 2*],
        [*3, 0*],
        [*2, 2*],
        [*-2, 0*],
        [*1, 0*],
        [*-3, 0*],
        [*3, -6*],
        [*0, 2*],
        [*-1, 4*],
        [*0, 0*],
        [*-1, 2*],
        [*-2, -4*],
        [*4, -4*],
        [*-2, 8*],
        [*-4, -2*],
        [*11, -2*],
        [*9, 4*],
        [*-6, 8*],
        [*-10, -2*],
        [*-8, 4*],
        [*14, -6*],
        [*2, -4*],
        [*2, 10*],
        [*6, -12*],
        [*0, 0*],
        [*10, 2*],
        [*-11, -6*],
        [*15, -6*],
        [*-12, 16*],
        [*-7, 6*],
        [*14, -16*],
        [*3, -2*],
        [*-4, 12*],
        [*-7, -2*],
        [*4, 4*],
        [*18, -8*],
        [*-3, -6*],
        [*8, -14*],
        [*-20, 10*],
        [*5, -8*],
        [*1, 4*],
        [*-16, -6*],
        [*-16, 12*],
        [*4, 0*],
        [*-6, 10*],
        [*-12, 0*],
        [*-9, -4*],
        [*15, 2*],
        [*-12, 18*],
        [*6, 6*],
        [*-5, 4*],
        [*-2, -8*],
        [*-3, 8*],
        [*8, 0*],
        [*13, -4*],
        [*-10, -2*],
        [*24, -6*],
        [*-4, -4*],
        [*12, 4*],
        [*7, -10*],
        [*12, -20*],
        [*18, -12*],
        [*-11, 14*],
        [*16, -12*],
        [*0, 16*],
        [*17, -12*],
        [*-3, -20*],
        [*-10, 16*],
        [*2, 10*],
        [*4, -6*],
        [*12, -20*],
        [*12, 8*],
        [*28, 4*],
        [*-17, 12*],
        [*-8, 10*],
        [*9, -20*],
        [*-12, -12*],
        [*-14, -6*],
        [*-20, -4*],
        [*24, 10*],
        [*-15, 6*],
        [*27, -18*],
        [*-10, 8*],
        [*6, 18*],
        [*1, 4*],
        [*-20, 0*],
        [*-18, -8*],
        [*18, -22*],
        [*-11, 6*],
        [*17, 14*],
        [*23, 6*],
        [*-22, 8*],
        [*-11, 28*],
        [*24, -12*],
        [*30, -18*],
        [*-27, 12*],
        [*-11, 30*],
        [*0, 12*],
        [*-28, 8*],
        [*-16, 10*],
        [*-18, -6*],
        [*13, -16*],
        [*-21, 6*],
        [*2, 8*],
        [*24, -16*],
        [*37, -16*],
        [*24, -4*],
        [*2, -6*],
        [*-10, -4*],
        [*12, -12*],
        [*0, -20*],
        [*0, 28*],
        [*-16, 22*],
        [*3, -6*],
        [*-21, 28*],
        [*-2, 14*],
        [*-18, 8*],
        [*3, 0*],
        [*18, 0*],
        [*13, -22*],
        [*12, 8*],
        [*-10, -10*],
        [*-26, 26*],
        [*-8, -8*],
        [*-24, 6*],
        [*-30, 2*],
        [*33, 10*],
        [*30, -18*],
        [*-12, -20*],
        [*-12, -22*],
        [*29, -28*],
        [*-12, 18*],
        [*-8, -4*],
        [*32, 12*],
        [*-22, 20*],
        [*22, 16*],
        [*-33, -14*],
        [*-34, 8*],
        [*-21, 30*],
        [*4, 4*],
        [*18, -36*],
        [*-30, 18*],
        [*-18, -12*],
        [*-1, -4*],
        [*-13, 6*],
        [*-3, 30*],
        [*-34, 4*],
        [*38, -10*],
        [*4, 0*],
        [*7, -26*],
        [*-18, 36*],
        [*14, -28*],
        [*30, -18*],
        [*-29, -8*],
        [*28, -10*],
        [*-2, -14*],
        [*-17, -10*],
        [*18, -4*],
        [*9, -30*],
        [*14, -4*],
        [*-32, -14*],
        [*-38, 4*],
        [*24, 0*],
        [*2, -24*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_23_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_23_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_23_2_a_a(:prec:=2)
    chi := MakeCharacter_23_a();
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
// containing the newform, type "MakeNewformModSym_23_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function MakeNewformModSym_23_2_a_a( : sign := -1)
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_23_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,sign)));
    Vf := Kernel([],Snew);
    return Vf;
end function;