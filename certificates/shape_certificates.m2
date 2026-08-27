-- Certificate extraction for Proposition 2.4 (iii)  [proof of Proposition 2.4]
-- Reproduces the paper's Macaulay2 computation in the (r,s)-coordinates directly and
-- extracts ideal-membership certificates that Lean can verify with linear_combination.
--
-- Equations (B^k-coefficients of the normalized trinomial 1 - t1 - t2 in J0):
--   g0 = l1 + l2 - 1
--   g1..g4 = the k=1..4 equations of the paper (proof of Proposition 2.4)
--
-- Output: certificates as Macaulay2 matrices, printed to stdout.

R = QQ[l1,l2,r1,s1,r2,s2];
g0 = l1 + l2 - 1;
g1 = l1*r1 + l2*r2;
g2 = l1*(r1^2 - s1) + l2*(r2^2 - s2);
g3 = l1*r1*(r1^2 - 3*s1 + 2) + l2*r2*(r2^2 - 3*s2 + 2);
g4 = l1*(r1^4 - 6*r1^2*s1 + 8*r1^2 + 3*s1^2 - 6*s1) + l2*(r2^4 - 6*r2^2*s2 + 8*r2^2 + 3*s2^2 - 6*s2);
G = matrix{{g0,g1,g2,g3,g4}};
I = ideal G;

J = saturate(I, l1*l2);
DecJ = decompose J;
<< "number of components: " << #DecJ << endl;
scan(DecJ, p -> (<< "component: " << toString p << endl));

Pinf = first select(DecJ, p -> isSubset(ideal(r1,s1,r2,s2), p));
Paff = first select(DecJ, p -> not isSubset(ideal(r1,s1,r2,s2), p));
<< "Pinf = " << toString Pinf << endl;
<< "Paff = " << toString Paff << endl;

E = eliminate(Paff, {l1,l2});
<< "elimination ideal gens:" << endl;
scan(flatten entries gens E, v -> << "  " << toString v << endl);

-- also the paper's second SOS element as combination of E-gens
sosR = r1^2 - r1*r2 + r2^2 - 3;
<< "sosR in E: " << (sosR % E == 0) << endl;
cofSOS = sosR // (gens E);
<< "sosR cofactors over E-gens: " << toString cofSOS << endl;

-- Certificates: for u in {r1,s1,r2,s2} and each generator v of E, find the least m with
-- u*v*(l1*l2)^m in I, and cofactors over g0..g4.
sat = l1*l2;
findCert = (f0) -> (
    -- find least k with f0^k in radical-membership range, then least m with
    -- f0^k*(l1*l2)^m in I; return (k, m, cofactors over g0..g4)
    k := 1;
    f := f0;
    while (f % J != 0 and k < 8) do (f = f*f0; k = k+1);
    if f % J != 0 then error "not in saturation";
    m := 0;
    while (f % I != 0 and m < 20) do (f = f*sat; m = m+1);
    if f % I != 0 then error "no certificate found";
    (k, m, f // (gens I))
    );

us = {r1, s1, r2, s2};
vs = flatten entries gens E;
<< "BEGIN CERTIFICATES" << endl;
scan(#us, i -> scan(#vs, j -> (
    (k, m, cof) := findCert(us#i * vs#j);
    << "CERT u=" << toString(us#i) << " v=" << toString(vs#j)
       << " k=" << k << " m=" << m << endl
       << " cofactors=" << toString transpose cof << endl;
    )));
<< "END CERTIFICATES" << endl;
