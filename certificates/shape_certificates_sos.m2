-- Variant of shape_certificates.m2: single case witness u* = r1^2+s1^2+r2^2+s2^2.
-- "Case 2" of the Prop-shape proof is u* != 0, so 6 certificates (one per
-- elimination-ideal generator) suffice.

R = QQ[l1,l2,r1,s1,r2,s2];
g0 = l1 + l2 - 1;
g1 = l1*r1 + l2*r2;
g2 = l1*(r1^2 - s1) + l2*(r2^2 - s2);
g3 = l1*r1*(r1^2 - 3*s1 + 2) + l2*r2*(r2^2 - 3*s2 + 2);
g4 = l1*(r1^4 - 6*r1^2*s1 + 8*r1^2 + 3*s1^2 - 6*s1) + l2*(r2^4 - 6*r2^2*s2 + 8*r2^2 + 3*s2^2 - 6*s2);
G = matrix{{g0,g1,g2,g3,g4}};
I = ideal G;
J = saturate(I, l1*l2);
Paff = first select(decompose J, p -> not isSubset(ideal(r1,s1,r2,s2), p));
E = eliminate(Paff, {l1,l2});

sat = l1*l2;
findCert = (f0) -> (
    k := 1;
    f := f0;
    while (f % J != 0 and k < 10) do (f = f*f0; k = k+1);
    if f % J != 0 then error "not in saturation";
    m := 0;
    while (f % I != 0 and m < 24) do (f = f*sat; m = m+1);
    if f % I != 0 then error "no certificate found";
    (k, m, f // (gens I))
    );

ustar = r1^2 + s1^2 + r2^2 + s2^2;
vs = flatten entries gens E;
<< "BEGIN CERTIFICATES" << endl;
scan(#vs, j -> (
    (k, m, cof) := findCert(ustar * vs#j);
    << "CERT u=ustar v=" << toString(vs#j) << " k=" << k << " m=" << m << endl
       << " cofactors=" << toString transpose cof << endl;
    ));
<< "END CERTIFICATES" << endl;
