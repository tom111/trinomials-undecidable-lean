-- Third variant: certificates of the shape (u*)^k * v * (l1*l2)^m in I,
-- with (k, m) chosen to minimize the printed cofactor size.
-- Conclusion in Lean is the same (u* != 0 and l1*l2 != 0 give v = 0), but v is not
-- raised to a power, and small (k, m) keep the linear_combination light.

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

ustar = r1^2 + s1^2 + r2^2 + s2^2;
sat = l1*l2;

-- search the (k, m) grid for the smallest certificate
bestCert = (v) -> (
    best := null;
    for k from 1 to 5 do (
        for m from 0 to 4 do (
            f := ustar^k * v * sat^m;
            if f % I == 0 then (
                cof := f // (gens I);
                sz := #(toString cof);
                if best === null or sz < best#0 then best = (sz, k, m, cof);
                );
            );
        );
    best
    );

vs = flatten entries gens E;
<< "BEGIN CERTIFICATES" << endl;
scan(#vs, j -> (
    b := bestCert(vs#j);
    if b === null then error "no certificate in grid";
    (sz, k, m, cof) := b;
    << "CERT v=" << toString(vs#j) << " k=" << k << " m=" << m
       << " size=" << sz << endl
       << " cofactors=" << toString transpose cof << endl;
    ));
<< "END CERTIFICATES" << endl;
