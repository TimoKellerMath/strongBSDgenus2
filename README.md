# Complete verification of strong BSD for many absolutely simple modular abelian surfaces over __Q__

This is the Magma code for the algorithms and the examples in "Complete verification of strong BSD for many absolutely simple modular abelian surfaces over __Q__" by Timo Keller and Michael Stoll.

__.m__ files contain intrinsics and should be __Attach__'ed. __.magma__ files should be __load__'ed.

## External code used
* Raymond van Bommel's code (slightly modified) for the real period and Tamagawa numbers (see the ancillary files at https://arxiv.org/abs/2002.04667):
* __RealPeriod.m__ (written by Raymond van Bommel): computation of the real period of hyperelliptic Jacobians
* __Tamagawa_pkg2.m__ (written by Raymond van Bommel): computation of Tamagawa numbers

## Section 1 (examples)
* __database_extract.magma:__ produce LaTeX code to print the table with information about the Galois representations
* __database_y_K_JK.magma:__ output of LMFDBexamples.m for the database
* __database.magma:__ data about our genus 2 curves relevant for BSD
* __findDuplicates.magma:__ count the number of isomorphism (curve) and isogeny (Jacobian) classes of Hasegawa and Wang curves and LMFDB examples
* __curves.magma:__ genus 2 curves with absolutely simple GL_2-type Jacobian from the LMFDB
* __LMFDB-curves.magma:__ a variant of __curves.magma__

## Section 2 (residual Galois representations)
* __Galreps.m:__ compute the images of the residual Galois representations of weight 2 newforms with real quadratic coefficients
* __endomorphisms.m:__ compute endomorphism rings of genus 2 Jacobians and their action on points, in particular torsion points, compute Galois representations rho_frp for fixed frp, characters constituting it if reducible, etc.
* __computeGalreps.magma:__ print information about the Galois representations
* __p-adic-Galois.magma:__ code for images of p-adic Galois representations
* __printGalrepsTable.magma:__ code to produce a LaTeX table with information about the residual Galois representations
* __characters.magma:__ code for producing the information on the characters involved in odd reducible residual Galois representations
* __logs/characters.log:__ the result of running __characters.magma__
* __irreducible_non_maximal.magma:__ code for determining the projective image of the odd irreducible, but not maximal Galois representations
* __logs/irreducible_non_maximal.log:__ the result of running __irreducible_non_maximal.magma__

## Section 3 (Heegner point and index)
* __jacmaps.m:__ compute the Abel--Jacobi map and its inverse also for projective hyperelliptic curves (only needed for older versions of Magma)
* __HeegnerPoint.m:__ code to compute Heegner points and indices
* __PeterssonNorm.m:__ code to compute the Petersson norm of newforms of weight 2
* __MWgroup.m:__ saturate finite index subgroup of Mordell–Weil group, compute Mordell–Weil group over quadratic fields
* __periods.m:__ adapted Magma code to compute periods of modular symbols to given precision
* __outputHeegnerindices.magma:__ compute a few Heegner indices

## Section 4 (analytic order of Sha)
* __ShaAn.m:__ computation of #Sha(J/Q)_an
* __ManinConstant.m:__ compute c_f * c_pi as in the section on the analytic order of Sha

## Section 5 (bound on support of Sha)
* partially contained in the files for Section 1 and 8

## Section 6 (descent)
* partially contained in the files for Section 1 and 8

## Section 7 (p-adic L-functions)
* __EvaluateModularSymbols.m:__ evaluate modular symbols of general weight 2 newforms with the canonical periods as in [Balakrishnan--Müller--Stein]
* __directory pAdicLFunction/:__ code to compute p-adic L-functions of newforms of weight 2, trivial nebentypus and with real quadratic coefficient ring where p is ordinary for f

## Section 8 (examples)
* __verifyBSD.magma:__ compute what is left to do to verify strong BSD
* __HasegawaWangCurves.magma:__ compute what is left to do to verify strong BSD for the Hasegawa and Wang curves
* __logs/HasegawaWangCurves.log:__ log file of he previous computation
* __LMFDBexamples.magma:__ compute what is left to do to verify strong BSD for the LMFDB examples
* __logs/LMFDBexamples.log:__ log file of he previous computation
* __logs/remains_to_be_done.txt:__ what remains to be done for the LMFDB examples after running LMFDBexamples.magma, also includes information on further examples

## Appendix A (example with #Sha = 7^2)
* __congruence.magma:__ (written by Sam Frengley) check claims in appendix A
* __N3200.magma:__ code for I_K and #Sha(J/Q)_an of the N = 3200 example in the Appendix
* __logs/3200.log:__ log file of the previous computation
* __Sha7-curve.magma:__ verify c_2(J/Q) = 1 for Sam Frengley's curve in the Appendix
* __torsionInSha.magma:__ compute what is left to do to verify strong BSD for twists J^K/Q in the examples with p = 3, 5, 7 dividing #Sha
* __logs/torsionInSha.log:__ the result of running __torsionInSha.magma__

## General functions
* __Sha.spec:__ spec file to attach the Magma files needed
* __CrvHypConversion.m:__ convert between curves, modular symbols, and newforms
* __parse_group.magma:__ functions for creating database_y_K_JK.magma
