load "~/Repository/aip_Hg/m2/aip.m2"

-----------------------------
-- Theta example from paper
-----------------------------

A = matrix {{5,3,4},{5,4,3},{2,8,5}}
u = colVec {1,1,1}
Abar = collapse(A,u)

s = colVec {1/17,0,3/17}
solveIP theta(A, u, s, 11)

QQ[p,t]

S1 = {(A,u)}
M1 = ft(A,u)*p - uDeficit(A,u,11)

B = collapse(A,u)

S2 = uShort(A,u,11)
numeric apply(S2,v->ft(B,v)) -- second one wins

u2 = S2_1
M2 = ft(B,u2)*p-uDeficit(B,u2,11)
S2 = {(B,u2)}

S3 = uShort(B,u2,11)
numeric apply(S3,v->ft(B,v)) -- first one wins

u3 = S3_0
M3 = ft(B,u3)*p-uDeficit(B,u3,11)
S3 = {(B,u3)}

S4 = uShort(B,u3,11)
numeric apply(S4,v->ft(B,v)) -- first and second are not very small; S5 is empty
 
gf = (M1*t + M2*t^2 + M3*t^3)/(1-p*t) + (p-1)*t^4/((1-p*t)*(1-t)) 
toString gf

ft(B,colVec{5,5})
ft(B,colVec{4,8})
ft(B,colVec{1,17})
ft(B,colVec{2,14})

-- why don't these work?
us := v -> uShort(collapse(B,v),v,11) 
collapse(B,colVec{1,7})
us colVec{1,7}
-- something is getting messed up when the matrix has a single row


-- {-(10/17) + (4*p)/17, -(8/17) + (4*p^2)/17, -(20/17) + (4*p^3)/17, -1 - (3*p)/17 + (4*p^4)/17, -1 - (3*p^2)/17 + (4*p^5)/17, -1 - (3*p^3)/17 + (4*p^6)/17, -1 - (3*p^4)/17 + (4*p^7)/17, -1 - (3*p^5)/17 + (4*p^8)/17, -1 - (3*p^6)/17 + (4*p^9)/17, -1 - (3*p^7)/17 + (4*p^10)/17}

-- {2, 28, 312, 3442, 37872, 416602, 4582632, 50408962, 554498592, 6099484522}

ZZ/11[x,y,z]
I = monomialIdeal(x^5*y^5*z^2,x^3*y^4*z^8,x^4*y^3*z^5)
    
frobeniusNu(5,I,Verbose=>true,ContainmentTest=>FrobeniusPower)
-- Beauty! 
   
---------------------------------------------
-- diagonal
------------------------------------------------------
A = matrix {{5,0,0},{0,6,0},{0,0,9}}
u = colVec {1,1,1}
QQ[p,t]

toString mPrimaryMu(A,u,7,p,t)

-- {2, 20, 146, 1028, 7202, 50420, 352946, 2470628, 17294402, 121060820}

ZZ/7[x,y,z];
I = monomialIdeal(x^5,y^6,z^9);

frobeniusNu(7,I,Verbose=>true,ContainmentTest=>FrobeniusPower)
-- Beauty!

---------------------------------------------
-- power of m
------------------------------------------------------
QQ[p,t]
ZZ/7[x,y,z];
I = (monomialIdeal(x,y,z))^4
A = transpose matrix apply(I_*,v-> first exponents v)
u = colVec{1,1,1}

time toString mPrimaryMu(A,u,7,p,t)
time toString mPrimaryMu(A,u,7,p,t)

-- {4, 34, 244, 1714, 12004, 84034, 588244, 4117714, 28824004, 201768034}

pp = 7;
apply(1..10, e-> pp^e*adicTruncation(pp,e,3/4-1/(4*pp))) 
--Beauty!

frobeniusNu(3,I,Verbose=>true,ContainmentTest=>FrobeniusPower) 

QQ[x,y,z];
I = (monomialIdeal(x,y,z))^5
A = transpose matrix apply(I_*,v-> first exponents v)
u = colVec{1,1,1}

QQ[p,t]
time toString mPrimaryMu(A,u,2,p,t)
-- takes a little while, but finishes it (~13-14 min)