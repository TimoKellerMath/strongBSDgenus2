
// Make newform 321.2.a.a in Magma, downloaded from the LMFDB on 14 November 2022.
// To make the character of type GrpDrchElt, type "MakeCharacter_321_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_321_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_321_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
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


// To make the character of type GrpDrchElt, type "MakeCharacter_321_a();"
function MakeCharacter_321_a()
    N := 321;
    order := 1;
    char_gens := [*215, 109*];
    v := [*\
1,
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_321_a_Hecke(Kf)
    return MakeCharacter_321_a();
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
[*0, -1*],
        [*-1, 0*],
        [*1, 0*],
        [*-2, 0*],
        [*-4, 2*],
        [*-1, 0*],
        [*-1, 4*],
        [*-3, -2*],
        [*0, -4*],
        [*0, -2*],
        [*-6, 0*],
        [*1, 0*],
        [*4, -8*],
        [*-4, 2*],
        [*4, -2*],
        [*8, -2*],
        [*0, 8*],
        [*7, -12*],
        [*6, -2*],
        [*-3, -2*],
        [*-4, 10*],
        [*-8, 12*],
        [*-4, -4*],
        [*-6, 2*],
        [*-4, 6*],
        [*-8, 6*],
        [*-8, -2*],
        [*-1, 0*],
        [*-10, 8*],
        [*3, -4*],
        [*4, -6*],
        [*11, -2*],
        [*2, 10*],
        [*-6, 4*],
        [*10, -4*],
        [*1, -10*],
        [*-12, 6*],
        [*-8, 8*],
        [*11, -6*],
        [*5, 0*],
        [*-23, -2*],
        [*-8, 6*],
        [*-13, 2*],
        [*-2, -8*],
        [*14, 0*],
        [*-5, 14*],
        [*14, 8*],
        [*1, -10*],
        [*16, 6*],
        [*16, -10*],
        [*-8, 12*],
        [*-8, 18*],
        [*17, -12*],
        [*-8, 2*],
        [*6, 12*],
        [*-4, 0*],
        [*9, -12*],
        [*-11, 14*],
        [*-8, 6*],
        [*6, -4*],
        [*19, -2*],
        [*26, -6*],
        [*6, -16*],
        [*5, 10*],
        [*1, -16*],
        [*-18, 20*],
        [*19, -22*],
        [*3, -12*],
        [*-3, 6*],
        [*-16, 26*],
        [*14, -20*],
        [*-17, -10*],
        [*0, -18*],
        [*-15, -12*],
        [*10, -10*],
        [*4, -24*],
        [*6, -8*],
        [*10, -24*],
        [*-18, 0*],
        [*22, 2*],
        [*17, -14*],
        [*-29, 0*],
        [*-6, 6*],
        [*-10, 18*],
        [*-28, -4*],
        [*-12, 24*],
        [*-21, 24*],
        [*-23, 28*],
        [*14, 6*],
        [*-24, 16*],
        [*-14, 14*],
        [*-9, 18*],
        [*10, 16*],
        [*-17, 2*],
        [*-8, -10*],
        [*14, -26*],
        [*-6, 8*],
        [*-1, -12*],
        [*26, -14*],
        [*-16, -4*],
        [*29, -2*],
        [*35, -16*],
        [*29, 2*],
        [*-32, -6*],
        [*-1, 10*],
        [*-33, -8*],
        [*20, -14*],
        [*-29, 8*],
        [*10, 0*],
        [*-32, 10*],
        [*12, 2*],
        [*12, -36*],
        [*23, -24*],
        [*10, 14*],
        [*22, -10*],
        [*-13, -8*],
        [*-19, 26*],
        [*8, -24*],
        [*-18, -2*],
        [*-36, 16*],
        [*-2, 8*],
        [*26, -2*],
        [*22, 4*],
        [*10, -8*],
        [*21, 10*],
        [*-9, 28*],
        [*24, -28*],
        [*-15, 18*],
        [*-13, -18*],
        [*-18, 26*],
        [*16, 6*],
        [*-34, -8*],
        [*12, -22*],
        [*-4, -6*],
        [*4, 12*],
        [*34, -24*],
        [*-14, 40*],
        [*-12, -12*],
        [*4, 14*],
        [*17, -36*],
        [*36, 0*],
        [*-25, -8*],
        [*-20, -8*],
        [*-5, -18*],
        [*-32, 2*],
        [*-22, 14*],
        [*20, 18*],
        [*-26, 6*],
        [*39, -6*],
        [*-25, 2*],
        [*6, -34*],
        [*20, -36*],
        [*47, -6*],
        [*-13, 2*],
        [*-12, 20*],
        [*-32, -8*],
        [*6, -4*],
        [*-13, 24*],
        [*-1, -4*],
        [*-34, -6*],
        [*28, -16*],
        [*22, -32*],
        [*-11, 18*],
        [*-37, -6*],
        [*-2, -32*],
        [*37, -6*],
        [*8, -26*],
        [*-53, -4*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_321_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_321_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_321_2_a_a(:prec:=2)
    chi := MakeCharacter_321_a();
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
// containing the newform, type "MakeNewformModSym_321_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function MakeNewformModSym_321_2_a_a( : sign := 0)
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_321_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,sign)));
    Vf := Kernel([<2,R![-1, 1, 1]>,<5,R![-1, 1]>],Snew);
    return Vf;
end function;