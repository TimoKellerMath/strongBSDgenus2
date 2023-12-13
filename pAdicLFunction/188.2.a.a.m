
// Make newform 188.2.a.a in Magma, downloaded from the LMFDB on 11 June 2023.
// To make the character of type GrpDrchElt, type "MakeCharacter_188_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_188_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_188_2_a_a();".
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


// To make the character of type GrpDrchElt, type "MakeCharacter_188_a();"
function MakeCharacter_188_a()
    N := 188;
    order := 1;
    char_gens := [*95, 5*];
    v := [*
1,
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_188_a_Hecke(Kf)
    return MakeCharacter_188_a();
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
[*0, 0*],
        [*-1, -1*],
        [*-2, 2*],
        [*-4, 1*],
        [*0, -4*],
        [*0, -4*],
        [*3, -3*],
        [*-4, 6*],
        [*-2, 4*],
        [*0, 0*],
        [*0, 0*],
        [*-7, 3*],
        [*10, -2*],
        [*-10, 0*],
        [*1, 0*],
        [*-8, 5*],
        [*0, 1*],
        [*4, -3*],
        [*-6, -2*],
        [*5, 5*],
        [*0, 6*],
        [*-3, -3*],
        [*-4, 8*],
        [*0, -3*],
        [*-12, 3*],
        [*-9, 1*],
        [*3, -9*],
        [*0, -10*],
        [*-4, -2*],
        [*10, 2*],
        [*-6, -4*],
        [*0, 3*],
        [*-12, 2*],
        [*14, -8*],
        [*-5, -11*],
        [*-12, 0*],
        [*-8, 5*],
        [*2, 6*],
        [*0, -14*],
        [*12, 1*],
        [*10, 4*],
        [*6, -12*],
        [*8, -8*],
        [*6, -10*],
        [*2, 4*],
        [*8, 12*],
        [*8, -14*],
        [*0, 4*],
        [*2, 10*],
        [*-6, 2*],
        [*-14, 16*],
        [*-17, 7*],
        [*-15, 11*],
        [*-19, 17*],
        [*22, -4*],
        [*-4, -11*],
        [*-10, 4*],
        [*3, -17*],
        [*-9, 1*],
        [*24, -12*],
        [*4, 9*],
        [*-4, -4*],
        [*-17, 11*],
        [*-14, 4*],
        [*6, 2*],
        [*-8, -2*],
        [*-8, -3*],
        [*20, -11*],
        [*-3, 9*],
        [*-12, 24*],
        [*-8, -7*],
        [*0, -14*],
        [*24, -12*],
        [*10, 6*],
        [*4, -19*],
        [*11, -25*],
        [*10, -2*],
        [*13, 15*],
        [*-27, 15*],
        [*8, -12*],
        [*-14, 14*],
        [*30, -4*],
        [*-24, 17*],
        [*2, -2*],
        [*24, -12*],
        [*-6, 22*],
        [*-6, -6*],
        [*-15, 31*],
        [*-28, 16*],
        [*-4, -2*],
        [*26, -16*],
        [*12, -7*],
        [*-20, -4*],
        [*-12, 19*],
        [*-4, 16*],
        [*14, -4*],
        [*10, 16*],
        [*-36, 1*],
        [*-24, 20*],
        [*-24, -13*],
        [*-28, 4*],
        [*-2, -2*],
        [*4, -10*],
        [*-32, -8*],
        [*-7, 13*],
        [*4, 18*],
        [*8, 4*],
        [*10, -8*],
        [*22, 4*],
        [*-24, -9*],
        [*-20, 8*],
        [*-16, 3*],
        [*-5, 13*],
        [*0, 0*],
        [*0, 4*],
        [*2, 2*],
        [*12, -7*],
        [*-12, -13*],
        [*33, -1*],
        [*41, 1*],
        [*11, -3*],
        [*-4, 18*],
        [*-24, 2*],
        [*24, -27*],
        [*-18, -10*],
        [*16, -2*],
        [*20, -21*],
        [*20, -19*],
        [*-14, -4*],
        [*-45, 9*],
        [*-20, -9*],
        [*34, 2*],
        [*-30, 6*],
        [*-6, 12*],
        [*26, -16*],
        [*-7, 19*],
        [*-3, -21*],
        [*-6, -6*],
        [*-18, -8*],
        [*32, 2*],
        [*23, -29*],
        [*-14, 16*],
        [*32, -8*],
        [*-20, 11*],
        [*-20, 6*],
        [*22, -40*],
        [*-3, -9*],
        [*-18, 22*],
        [*-2, 26*],
        [*-13, 31*],
        [*-18, 0*],
        [*8, 2*],
        [*-24, 29*],
        [*14, -28*],
        [*40, -24*],
        [*-16, -19*],
        [*26, -44*],
        [*-31, -1*],
        [*-22, 6*],
        [*28, -35*],
        [*32, -20*],
        [*0, 30*],
        [*0, -9*],
        [*26, 2*],
        [*6, -28*],
        [*-34, 8*],
        [*-20, 45*],
        [*0, -18*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_188_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_188_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_188_2_a_a(:prec:=2)
    chi := MakeCharacter_188_a();
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
// containing the newform, type "MakeNewformModSym_188_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function MakeNewformModSym_188_2_a_a( : sign := -1)
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_188_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,sign)));
    Vf := Kernel([<3,R![1, 3, 1]>],Snew);
    return Vf;
end function;