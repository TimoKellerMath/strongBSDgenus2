
// Make newform 3200.2.a.bn in Magma, downloaded from the LMFDB on 13 June 2023.
// To make the character of type GrpDrchElt, type "MakeCharacter_3200_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_3200_2_a_bn();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_3200_2_a_bn();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [*-2, 0, 1*];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rfbasis := [Kf.1^i : i in [0..Degree(Kf)-1]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_3200_a();"
function MakeCharacter_3200_a()
    N := 3200;
    order := 1;
    char_gens := [*1151, 901, 2177*];
    v := [*
1,
1,
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_3200_a_Hecke(Kf)
    return MakeCharacter_3200_a();
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
        [*1, 1*],
        [*0, 0*],
        [*2, -2*],
        [*1, 3*],
        [*0, -4*],
        [*-3, 2*],
        [*3, -1*],
        [*2, 2*],
        [*8, 0*],
        [*-2, 2*],
        [*-2, -4*],
        [*5, 4*],
        [*10, 0*],
        [*4, 4*],
        [*2, 4*],
        [*2, -4*],
        [*6, 0*],
        [*-7, 3*],
        [*4, 4*],
        [*3, 2*],
        [*-10, -2*],
        [*-3, 3*],
        [*9, -2*],
        [*-6, -8*],
        [*-2, -12*],
        [*4, -4*],
        [*-9, 5*],
        [*6, 4*],
        [*9, -4*],
        [*-6, -10*],
        [*-6, 8*],
        [*-5, 0*],
        [*1, 7*],
        [*8, -8*],
        [*2, -6*],
        [*14, 4*],
        [*-7, -9*],
        [*8, -4*],
        [*4, 4*],
        [*23, -1*],
        [*10, 4*],
        [*-10, 6*],
        [*-11, 2*],
        [*2, 4*],
        [*-20, -4*],
        [*-1, -7*],
        [*-8, -4*],
        [*-10, -8*],
        [*12, -8*],
        [*-2, -8*],
        [*4, -16*],
        [*7, 2*],
        [*13, -3*],
        [*-6, 8*],
        [*-2, -6*],
        [*-12, 4*],
        [*-22, 2*],
        [*4, 4*],
        [*2, -16*],
        [*3, -9*],
        [*6, 8*],
        [*1, -3*],
        [*14, 6*],
        [*-10, 0*],
        [*8, -4*],
        [*13, 7*],
        [*13, -4*],
        [*-9, -7*],
        [*18, 8*],
        [*10, -16*],
        [*-6, -2*],
        [*-16, 12*],
        [*-22, -8*],
        [*-7, -7*],
        [*2, 18*],
        [*-6, 8*],
        [*-20, 8*],
        [*-5, 18*],
        [*-11, 12*],
        [*-9, 11*],
        [*-4, 0*],
        [*2, -10*],
        [*-19, -2*],
        [*-12, 8*],
        [*7, 11*],
        [*-9, -18*],
        [*23, -4*],
        [*0, 4*],
        [*-4, 12*],
        [*-2, 8*],
        [*38, -2*],
        [*-6, 22*],
        [*6, -16*],
        [*-14, 0*],
        [*0, 12*],
        [*14, 0*],
        [*5, 8*],
        [*-21, 1*],
        [*-12, -4*],
        [*1, -11*],
        [*-32, 4*],
        [*10, -12*],
        [*-15, -8*],
        [*-2, 24*],
        [*13, 20*],
        [*7, -5*],
        [*-7, 0*],
        [*10, -26*],
        [*21, 10*],
        [*-36, 0*],
        [*-18, 8*],
        [*-18, 0*],
        [*-2, -8*],
        [*-30, 10*],
        [*-34, -8*],
        [*-26, 8*],
        [*0, 4*],
        [*6, 0*],
        [*-13, -27*],
        [*12, -4*],
        [*-14, -8*],
        [*40, -8*],
        [*-13, 21*],
        [*15, 15*],
        [*-36, -8*],
        [*12, -24*],
        [*-2, 18*],
        [*-32, 0*],
        [*-32, 4*],
        [*-6, -16*],
        [*-6, -14*],
        [*12, 16*],
        [*20, 4*],
        [*-11, -20*],
        [*3, 22*],
        [*8, 8*],
        [*6, -16*],
        [*42, 0*],
        [*18, 16*],
        [*-2, -24*],
        [*-18, -16*],
        [*-4, 12*],
        [*-41, -5*],
        [*20, 0*],
        [*-4, 0*],
        [*-6, 16*],
        [*11, 0*],
        [*33, 15*],
        [*4, 0*],
        [*-32, 4*],
        [*-26, 8*],
        [*-39, -3*],
        [*-28, 4*],
        [*34, 8*],
        [*-8, -20*],
        [*42, -2*],
        [*-22, 16*],
        [*11, -22*],
        [*24, 12*],
        [*-6, 28*],
        [*-1, -8*],
        [*-20, -16*],
        [*33, 7*],
        [*-7, 22*],
        [*-14, -14*],
        [*-14, -34*],
        [*0, 12*],
        [*-5, -22*],
        [*8, 24*],
        [*-7, 29*],
        [*6, 32*],
        [*6, 14*],
        [*3, -26*],
        [*-24, 0*],
        [*-7, 2*],
        [*-3, 5*],
        [*-6, 8*],
        [*-32, -8*],
        [*-14, -12*],
        [*-20, -4*],
        [*-9, 23*],
        [*-14, -4*],
        [*15, 26*],
        [*0, 12*],
        [*-16, -4*],
        [*18, -24*],
        [*-3, 5*],
        [*25, 12*],
        [*36, 0*],
        [*-15, -24*],
        [*-21, -5*],
        [*15, -3*],
        [*-10, 4*],
        [*29, 5*],
        [*-14, 0*],
        [*3, -24*],
        [*26, -24*],
        [*-27, -8*],
        [*-34, -14*],
        [*-6, -20*],
        [*-8, 12*],
        [*12, -12*],
        [*-21, -4*],
        [*14, -8*],
        [*-14, 0*],
        [*-50, -6*],
        [*14, -16*],
        [*-22, 24*],
        [*18, 28*],
        [*-30, 16*],
        [*-34, -8*],
        [*-12, 16*],
        [*11, 1*],
        [*30, -6*],
        [*41, 0*],
        [*6, -2*],
        [*11, -22*],
        [*10, 34*],
        [*30, 20*],
        [*-2, 4*],
        [*-32, -12*],
        [*39, -14*],
        [*34, 26*],
        [*25, -27*],
        [*10, -24*],
        [*15, 10*],
        [*-12, -8*],
        [*32, -4*],
        [*-39, 9*],
        [*10, -32*],
        [*-21, 9*],
        [*-22, 26*],
        [*-7, 10*],
        [*-34, -12*],
        [*22, -22*],
        [*27, -2*],
        [*-8, 0*],
        [*-3, -15*],
        [*12, 12*],
        [*41, -15*],
        [*17, -43*],
        [*2, 38*],
        [*20, 8*],
        [*53, 12*],
        [*-8, -8*],
        [*10, 10*],
        [*-30, 8*],
        [*33, 25*],
        [*36, 16*],
        [*-4, 12*],
        [*27, 16*],
        [*-22, 34*],
        [*13, -38*],
        [*12, -4*],
        [*35, -3*],
        [*44, 4*],
        [*31, 15*],
        [*-10, 44*],
        [*67, 4*],
        [*-30, -14*],
        [*41, 15*],
        [*32, -8*],
        [*4, -16*],
        [*-3, 10*],
        [*7, -29*],
        [*14, 36*],
        [*-22, 8*],
        [*-45, -3*],
        [*38, -12*],
        [*36, -24*],
        [*-19, 31*],
        [*63, 10*],
        [*-60, 8*],
        [*14, 32*],
        [*32, -28*],
        [*-5, 9*],
        [*-12, 36*],
        [*34, -32*],
        [*-9, -29*],
        [*-12, -4*],
        [*-14, -18*],
        [*-20, -16*],
        [*52, -24*],
        [*27, 11*],
        [*12, -40*],
        [*-10, -16*],
        [*-4, 28*],
        [*-28, 8*],
        [*-14, 0*],
        [*-6, 20*],
        [*-2, 40*],
        [*11, -10*],
        [*-3, 25*],
        [*-40, 28*],
        [*34, -16*],
        [*-34, -6*],
        [*-44, -20*],
        [*14, 16*],
        [*-11, -1*],
        [*15, 16*],
        [*-42, 8*],
        [*28, 32*],
        [*45, 13*],
        [*5, -15*],
        [*17, 30*],
        [*-38, 16*],
        [*-38, 8*],
        [*-22, -30*],
        [*2, 4*],
        [*18, 2*],
        [*14, -40*],
        [*-1, -34*],
        [*26, -4*],
        [*-40, -20*],
        [*18, -8*],
        [*67, 3*],
        [*-60, -8*],
        [*-39, 16*],
        [*-13, 16*],
        [*26, -32*],
        [*19, 28*],
        [*0, -4*],
        [*-22, -10*],
        [*14, 40*],
        [*14, 0*],
        [*-1, 25*],
        [*26, 0*],
        [*2, 30*],
        [*52, 24*],
        [*-36, 0*],
        [*10, -32*],
        [*42, 14*],
        [*-51, 9*],
        [*-35, 35*],
        [*-66, -12*],
        [*24, -8*],
        [*-2, -16*],
        [*-15, -2*],
        [*-54, -10*],
        [*20, -44*],
        [*-9, 20*],
        [*-2, 12*],
        [*20, -28*],
        [*-62, 12*],
        [*26, 8*],
        [*-8, 36*],
        [*-5, -17*],
        [*-8, 16*],
        [*2, -28*],
        [*35, -19*],
        [*62, 16*],
        [*14, 20*],
        [*12, -36*],
        [*-38, 28*],
        [*-5, -34*],
        [*24, -20*],
        [*-27, -37*],
        [*-42, 32*],
        [*68, -12*],
        [*34, -16*],
        [*37, -22*],
        [*70, 18*],
        [*-58, -16*],
        [*-59, 3*],
        [*-53, -2*],
        [*20, 20*],
        [*-12, -32*],
        [*21, 24*],
        [*-54, -8*],
        [*-39, 27*],
        [*-4, -20*],
        [*-8, 44*],
        [*-32, -32*],
        [*30, 24*],
        [*-21, -29*],
        [*-86, 2*],
        [*69, -4*],
        [*71, -22*],
        [*-26, 24*],
        [*-6, 4*],
        [*-1, 4*],
        [*-16, 8*],
        [*49, 28*],
        [*-42, -36*],
        [*-34, 14*],
        [*-36, -8*],
        [*24, 0*],
        [*30, -4*],
        [*-18, 6*],
        [*-21, -12*],
        [*-12, 48*],
        [*-35, 25*],
        [*5, 51*],
        [*50, -38*],
        [*27, -44*],
        [*-32, -12*],
        [*-7, -16*],
        [*17, -17*],
        [*-62, 12*],
        [*-28, -20*],
        [*21, 46*],
        [*-16, 20*],
        [*39, -16*],
        [*-28, -20*],
        [*-16, 56*],
        [*-30, 8*],
        [*-18, -24*],
        [*-18, -24*],
        [*-41, -3*],
        [*-15, 24*],
        [*8, -16*],
        [*-33, -1*],
        [*-6, 0*],
        [*39, -2*],
        [*66, 8*],
        [*22, -10*],
        [*18, -10*],
        [*-47, -22*],
        [*58, 10*],
        [*-88, 0*],
        [*-6, -52*],
        [*-34, 22*],
        [*-79, 1*],
        [*27, 4*],
        [*68, 12*],
        [*10, -4*],
        [*21, 22*],
        [*-27, -33*],
        [*54, -10*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_3200_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_3200_2_a_bn();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_3200_2_a_bn(:prec:=2)
    chi := MakeCharacter_3200_a();
    f_vec := qexpCoeffs();
    Kf := Universe(f_vec);
    // SetVerbose("ModularForms", true);
    // SetVerbose("ModularSymbols", true);
    S := CuspidalSubspace(ModularForms(chi, 2));
    S := BaseChange(S, Kf);
    maxprec := NextPrime(2999) - 1;
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
// containing the newform, type "MakeNewformModSym_3200_2_a_bn();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
// The default sign is -1.  You can change this with the optional parameter "sign".
function MakeNewformModSym_3200_2_a_bn( : sign := -1)
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_3200_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,sign)));
    Vf := Kernel([<3,R![-1, -2, 1]>,<7,R![-4, -4, 1]>,<11,R![-17, -2, 1]>,<13,R![-32, 0, 1]>],Snew);
    return Vf;
end function;