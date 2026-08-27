-- Self-contained check of the generator algorithm of Theorem 4.5, for the smallest instance
-- (no equations, only the two guards; N = 6, M = 2), independent of Lean.
R = QQ[S,T,D_1..D_6];
-- A_0 = QQ[B,C_1..C_6]/(B^5, B C_i, C_i C_j),  S -> (1+B)/2, T -> (1-B)/2, D_i -> 1+C_i
A0amb = QQ[B, C_1..C_6];
A0 = A0amb / (ideal(B^5) + ideal apply(toList(1..6), i -> B*C_i)
      + ideal flatten apply(toList(1..6), i -> apply(toList(i..6), j -> C_i*C_j)));
psi0 = map(A0, R, {(1+B)/2, (1-B)/2} | toList apply(1..6, i -> 1 + C_i));
J0 = ker psi0;
-- A_Q for a quadratic form with symmetric matrix b on V = Q^6 x Q v_0 (order X_1..X_6, X_0)
AQ = (b) -> (
    amb := QQ[X_1..X_6, X_0, Z];
    idx := {X_1,X_2,X_3,X_4,X_5,X_6,X_0};
    rel := ideal flatten apply(0..6, i -> apply(i..6, j -> idx#i * idx#j - b_(i,j)*Z));
    rel = rel + ideal apply(idx, x -> x*Z) + ideal(Z^2);
    amb / rel);
Exp = (x) -> 1 + x + (1/2)*x^2;
phiI = (b) -> (
    A := AQ b;
    x0 := A_6; xs := apply(0..5, i -> A_i);
    ker map(A, R, {(1/2)*Exp(x0), (1/2)*Exp(-x0)} | toList apply(0..5, i -> Exp(xs#i))));
-- guard g_{m+1} = h^2 - 3k^2 - t^2:  matrix on (D_1..D_6,t) with D_1=h,D_2=k
bP = matrix table(7,7,(i,j)-> if i==j then (if i==0 then 1 else if i==1 then -3 else if i==6 then -1 else 0) else 0);
-- guard g_{m+2} = u_1^2+..+u_4^2 - h t:  D_3..D_6 = u_1..u_4, cross term (h,t)
bS = matrix table(7,7,(i,j)-> if i==j and i>=2 and i<=5 then 1 else if (i==0 and j==6) or (i==6 and j==0) then -1/2 else 0);
IP = intersect(J0, phiI bP, phiI bS);
m = ideal(2*S-1, 2*T-1, D_1-1,D_2-1,D_3-1,D_4-1,D_5-1,D_6-1);
<< "I_P: numgens=" << numgens IP << " dim=" << dim IP << " degree=" << degree IP << endl;
<< "colength dim_QQ(R/I_P) = " << degree IP << " (compare C=(N+5)+M(N+3)=" << (11+2*9) << ", C(N+6,4)=" << binomial(12,4) << ")" << endl;
<< "m^5 subset I_P : " << isSubset(m^5, IP) << endl;
<< "m^4 subset I_P : " << isSubset(m^4, IP) << "  (expected false)" << endl;
gens5 = ideal select(flatten entries mingens IP, g -> first degree g <= 5);
<< "I_P generated in degree <= 5 : " << (gens5 == IP) << endl;
<< "max degree of a minimal generator: " << max apply(flatten entries mingens IP, g -> first degree g) << endl;
-- tau~_d for d=(1,0,1,0,0,0): h=1,k=0,u_1=1 satisfies guards; tau~ = D^|d| - S D^{|d|+d} - T D^{|d|-d}
tau = D_1*D_3 - S*D_1^2*D_3^2 - T;
<< "a cleared affine trinomial tau~_d lies in I_P : " << (tau % IP == 0) << endl;
<< "I_P contains no monomial (I_P : (prod vars)^inf = I_P) : " << (saturate(IP, S*T*D_1*D_2*D_3*D_4*D_5*D_6) == IP) << endl;
