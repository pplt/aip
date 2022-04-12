--- RANDOM 

comp := (u,v) -> all(u,v,(i,j) -> i<=j ) or all(u,v,(i,j) -> i>=j )
    
search := (r) -> (
count := 1;
found := false;
local notCool;
local A;
local B;
local u;
local eps;
local S2;
local L;
local a;
local deficit;
local ramif;
while not found and count <= 100 do (
    print count;
notCool = true;
u = colVec toList apply(4,i-> 1+ random(10)); -- 4-vec
while notCool do (
   a = toList apply(3, i -> toList apply(4, j -> 1 + random(15))); -- 3x4
   A = transpose matrix a;
   B = collapse(A,u);
   notCool = ( rank target B ) < 2 or ft(A,u) >= 1 or comp(a_0,a_1) or comp(a_0,a_2) or comp(a_1,a_2) --or comp(a_0,a_3) or comp(a_1,a_3) or comp(a_2,a_3)
);
S2 = uShort(A,u,r); 
L = apply(S2, v -> ft(B,v));
eps = max L;
print(deficit = uDeficit(A,u,r), eps, ramif = #(select(L,x->x==eps)) );
found = (deficit != eps)  and ramif > 1;
count = count + 1;
);
(A,u)
)

randomVec := (n,M) -> colVec toList apply(n,i-> 1+ random(M))

randomMat := (m,n,M) -> 
(
    found := false;
    local mat;
    while not found do 
    (
        mat = toList apply(n, i -> toList apply(m, j -> random(M)));
        found = all(n-1, i -> all((i+1)..(n-1), j-> not comp(mat_i,mat_j) ) )
    );
    transpose matrix mat
)

maximalBy := (L,f) ->
(
    vals := apply(L,f);
    maximum := max vals;
    ( maximum, L_(positions(vals, x -> x == maximum )) )
)

minimalBy := (L,f) ->
(
    vals := apply(L,f);
    minimum := min vals;
    (minimum, L_(positions(vals, x -> x == minimum )) )
)

init := () ->
(
num = {(ft(A,u),uDeficit(A,u,r))};
graph = {{(A,u)}}
)

iterate := () -> (
S = last graph;
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )); 
( eps, S ) = maximalBy( S, pair -> ft pair); 
( delta, S ) = minimalBy( S, pair -> uDeficit(pair_0,pair_1,r));
graph = append(graph, S);
print S;
num = append(num,(eps,delta))
)

search2 := (r,m,n,M,maxTries) -> 
(
    count := 1;
    found := false;
    local i;
    local A;
    local u;
    local cool;
    local num;
    local graph;
    local S;
    local eps;
    local delta;
    local diffs;
    local ramif;
    while count <= maxTries and not found do
    (
        print count;
        (A,u) = ( randomMat(m,n,M), randomVec(m,M) );
        while gcd(univDenom A,r) != 1 do (A,u) = ( randomMat(m,n,M), randomVec(m,M) );
        num = {(ft(A,u),uDeficit(A,u,r))};
        graph = {{(A,u)}};
        i = 0;
        cool = num_0_0 <= 1;
        while cool and i <= 8 do
        -- looking at 8 levels
        (
            S = last graph;
            S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )); 
            ( eps, S ) = maximalBy( S, pair -> ft pair); 
            if eps > 1 then cool = false
            else
            ( 
                ( delta, S ) = minimalBy( S, pair -> uDeficit(pair_0,pair_1,r));
                graph = append(graph, S);
                num = append(num,(eps,delta));
                i = i + 1
            )
        );
        if cool then 
        (
            diffs = #select(0..7, i -> num_i_1 != num_(i+1)_0);
            -- ramif = #(unique apply(graph, x -> #x) );
            ramif = max apply(graph, x -> #x);
            found = diffs > 2 and ramif > 2
        );
        count = count + 1
     );
     if found then 
     (
         print graph;
         print num;
         print (diffs,ramif);
         (A,u)
     )
) 

search2(5,4,3,50,10000)

toString oo

-- NEW EXAMPLES
--* = skip; c = collapse

(r,A,u) = (11,matrix {{16, 16, 13}, {4, 12, 19}, {2, 4, 18}, {18, 2, 18}},matrix {{7}, {8}, {19}, {7}})
init()

iterate()

--collapses to 3 right away
-- 1 1*c 1c 1 2* 1c 1 1 1 1 1 1 1 1 1 1 1
-- ends in 12-loop

----------------------------------------------------------------------------------------------------------
(r,A,u) = (11, matrix {{7, 15, 13}, {17, 13, 14}, {4, 19, 14}, {15, 2, 0}},matrix {{18}, {10}, {14}, {3}})
init()

iterate()

--collapse to 2 right away
-- 1c 1 1* 1 1 2* 1c 1 1 1 1 1 1 1 1 1 1 1
-- ends in 12-cycle

----------------------------------------------------------------------------------------------------------
-- sprouting_graph_4.tex
(r,A,u) = (11,matrix {{36, 10, 31}, {38, 14, 23}, {19, 46, 31}, {47, 25, 36}},matrix {{29}, {24}, {24}, {30}})

-- may collapse right away
(r,A,u) = (11,matrix {{36, 10, 31}, {19, 46, 31}, {47, 25, 36}},matrix {{29}, {24}, {30}})
init()

iterate() 

toString oo

-- 1 1*c(2) 1 4* 1c 1 1 1 1
-- 5-loop at the end

univDenom2 A

QQ[p,t]

mu(A,u,11,p,t)

toString oo

ft(A,u)

----------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------


-------OLD EXAMPLE
(r,A,u) = (5, matrix {{6, 12, 9}, {14, 5, 11}, {14, 6, 9}, {4, 6, 1}},matrix {{5}, {6}, {6}, {10}})
-- my favorite so far
-- Currently in paper; UNFORTUNATELY r = 5 divides the universal denominator!

univDenom A

univDenom2 A

(r,A,u) = (5, matrix {{9, 6, 12}, {6, 9, 0}, {0, 6, 2}, {8, 11, 3}},matrix {{10}, {2}, {14}, {4}})

QQ[p,t]
toString mu(A,u,r,p,t)

------------------------------------------------------------------------------

(r,A,u) = (5,matrix {{1, 3, 7}, {7, 8, 3}},matrix {{1}, {3}})
init()

iterate()


-----------------------------
-- Theta example from paper
-----------------------------

A = matrix {{5,3,4},{5,4,3},{2,8,5}}
u = colVec {1,1,1}
r = 11

QQ[p,t]
mu(A,u,11,p,t)

S1 = {(A,u)}
M1 = ft(A,u)*p - uDeficit(A,u,11)

B = collapse(A,u)

S2 = uShort(A,u,11)
numeric apply(S2,v->ft(B,v)) -- last one wins

u2 = S2_2
M2 = ft(B,u2)*p-uDeficit(B,u2,11)
S2 = {(B,u2)}

S3 = uShort(B,u2,11)
numeric apply(S3,v->ft(B,v)) -- first one wins

u3 = S3_0
M3 = ft(B,u3)*p-uDeficit(B,u3,11)
S3 = {(B,u3)}

S4 = uShort(B,u3,11)
numeric apply(S4,v->ft(B,v)) -- last two are not very small; S5 is empty
 
gf = (M1*t + M2*t^2 + M3*t^3)/(1-p*t) + (p-1)*t^4/((1-p*t)*(1-t)) 
toString gf

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

-----------------------------
-- Theta example from paper (another class)
-----------------------------

A = matrix {{5,3,4},{5,4,3},{2,8,5}}
u = colVec {1,1,1}
Abar = collapse(A,u)

QQ[p,t]

S1 = {u}
M1 = ft(A,u)*p - uDeficit(A,u,12)

B = collapse(A,u)

S2 = uShort(A,u,12)
numeric apply(S2,v->ft(B,v)) -- second and 4th
S2 = {S2_1,S2_3}
numeric apply(S2,v->uDeficit(B,v,12)) -- tie

M2 = ft(B,S2_0)*p-uDeficit(B,S2_0,12)

uShort(B,S2_0,12)
uShort(B,S2_1,12)
S3 = uShort(B,S2_0,12)
numeric apply(S3,v->ft(B,v)) -- second and third
S3 = {S3_1,S3_2}
numeric apply(S3,v->uDeficit(B,v,12)) -- tie

M3 = ft(B,S3_1)*p-uDeficit(B,S3_1,12)

uShort(B,S3_0,12)
uShort(B,S3_1,12)
S4 = uShort(B,S3_0,12)
numeric apply(S4,v->ft(B,v)) -- second and third
S4 = {S4_1}
-- numeric apply(S3,v->uDeficit(B,v,12)) -- tie

M4 = ft(B,S4_0)*p-uDeficit(B,S4_0,12)

S5 = uShort(B,S4_0,12)
numeric apply(S5,v->ft(B,v)) -- second and third
 
-- has one more level, no intermediary terms


---------------------------------------------------
-- This example has a "second coefficient" and cycles

A = matrix {{9, 7, 8}, {2, 8, 5}, {0, 1, 3}}
u = colVec {6,3,1}
r = 3
S1 = {u}
M1 = ft(A,u)*p - uDeficit(A,u,r)

solveIP theta(A,u,specialPt(A,u),3)
solveIP theta(collapse(A,u),collapseMap(A,u)*u,specialPt(A,u),3)

A2 = collapse(A,u)
S2 = uShort(A,u,r)

M2 = ft(A2,S2_0)*p-uDeficit(A2,S2_0,r)

S3 = uShort(A2,S2_0,r)
A3 = collapse(A2,S2_0)
numeric apply(S3,v->ft(A3,v)) -- first
S3={S3_0}
M3 = ft(A3,S3_0)*p-uDeficit(A3,S3_0,r)

S4 = uShort(A3,S3_0,r)
A4 = collapse(A3,S3_0)
numeric apply(S4,v->ft(A4,v)) -- first
S4={S4_0}
M4 = ft(A4,S4_0)*p-uDeficit(A4,S4_0,r)

S5 = uShort(A4,S4_0,r)
A5 = collapse(A4,S4_0)
numeric apply(S5,v->ft(A5,v)) -- first
S5={S5_0}
M5 = ft(A5,S5_0)*p-uDeficit(A5,S5_0,r)

S6 = uShort(A5,S5_0,r)
A6 = collapse(A5,S5_0)
numeric apply(S6,v->ft(A6,v)) -- first
S6={S6_0}
M6 = ft(A6,S6_0)*p-uDeficit(A6,S6_0,r)

S7 = uShort(A6,S6_0,r)
A7 = collapse(A6,S6_0)
numeric apply(S7,v->ft(A7,v)) -- first
S7={S7_0}
M7 = ft(A7,S7_0)*p-uDeficit(A7,S7_0,r)

S8 = uShort(A7,S7_0,r)
A8 = collapse(A7,S7_0)
numeric apply(S8,v->ft(A8,v)) -- first
S8={S8_0}
M8 = ft(A8,S8_0)*p-uDeficit(A8,S8_0,r)

S9 = uShort(A8,S8_0,r)
A9 = collapse(A8,S8_0)
numeric apply(S9,v->ft(A9,v)) -- first
S9={S9_0}
M9 = ft(A9,S9_0)*p-uDeficit(A9,S9_0,r)

(M1,M2,M3,M4,M5,M6,M7,M8,M9)

gf = (M1*t+M2*t^2)/(1-p*t) + (M3*t^3+M4*t^4+M5*t^5+M6*t^6+M7*t^7+M8*t^8)/((1-p*t)*(1-t^6))

toString gf

---------------------------------------------------
-- A very simple example with intermediate coeff and a 1-cycle and bifurcation

r = 3
A = matrix {{3, 4, 6}, {3, 7, 3}, {8, 2, 6}}
u = colVec {2,4,3}
graph = {{(A,u)}}
num = {(ft(A,u),uDeficit(A,u,r))}

S = last graph
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )) 
eps = max apply(S,pair->ft pair) 
S= select(S, pair -> ft pair == eps )
delta = min apply(S,pair-> uDeficit(pair_0,pair_1,r))
S= select(S, pair -> uDeficit(pair_0,pair_1,r) == delta )
graph = append(graph, S)
num = append(num,(eps,delta))

QQ[p,t]
M = apply(num, v -> v_0*p-v_1)

gf = (M_0*t + M_1*t^2)/(1-p*t) + M_2*t^3/((1-p*t)*(1-t))
toString gf

      (A,u)
     /     \
(B,(2,6))  (B,(2,7))
    \        / 
     \      /
      (C,3) cycle to itself
      
B = collapse(A,u)
uShort(B,colVec{2,6},r)      
uShort(B,colVec{2,7},r)      


---------------------------------------------------
-- 6-cycle, 1 intermediate coeff, 1 - 4 - 1 - 1 ...

r = 3
A = matrix {{7, 7, 5}, {10, 9, 4}, {7, 10, 8}}
u = colVec {9,3,3}
graph = {{(A,u)}}
num = {(ft(A,u),uDeficit(A,u,r))}

S = last graph
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )) 
eps = max apply(S,pair->ft pair) 
S= select(S, pair -> ft pair == eps )
delta = min apply(S,pair-> uDeficit(pair_0,pair_1,r))
S= select(S, pair -> uDeficit(pair_0,pair_1,r) == delta )
graph = append(graph, S)
num = append(num,(eps,delta))

---------------------------------------------------
-- linear with 6-cycl way deep, 4 intermediate coeffs 

r = 3
A = matrix {{10, 9, 5}, {3, 5, 9}, {4, 4, 7}}
u = colVec {6,6,10}
graph = {{(A,u)}}
num = {(ft(A,u),uDeficit(A,u,r))}

S = last graph
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )) 
eps = max apply(S,pair->ft pair) 
S= select(S, pair -> ft pair == eps )
delta = min apply(S,pair-> uDeficit(pair_0,pair_1,r))
S= select(S, pair -> uDeficit(pair_0,pair_1,r) == delta )
graph = append(graph, S)
num = append(num,(eps,delta))

---------------------------------------------------
-- Example from paper; other classes

A = matrix {{5,3,4},{5,4,3},{2,8,5}}
u = colVec {1,1,1}

r = 1 -- u -> ubar (cycle)

r = 2 -- 1122x (meet not very small pair)

r = 3 -- 11x

r = 4 -- 121x

r = 5 -- 1x

r = 6 -- 11122221111x

r = 7 -- 121121x

r = 8 -- 12x

r = 9 -- 1x

r = 10 -- 111c

r = 11 -- 111x

r = 12 -- 1221x

r = 13 -- 1x

r = 14 -- 11x

r = 15 -- 112x

r = 16 -- 11111c

r = 17 -- 13c

r = 18
graph = {{(A,u)}}
num = {(ft(A,u),uDeficit(A,u,r))}

S = last graph
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )) 
eps = max apply(S,pair->ft pair) 
S= select(S, pair -> ft pair == eps )
delta = min apply(S,pair-> uDeficit(pair_0,pair_1,r))
S= select(S, pair -> uDeficit(pair_0,pair_1,r) == delta )
graph = append(graph, S)
num = append(num,(eps,delta))

---------------------------------------------------
r = 5
(A,u) = search(r)
num = {(ft(A,u),uDeficit(A,u,r))};
graph = {{(A,u)}}

S = last graph;
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )); 
eps = max apply(S,pair->ft pair); 
S= select(S, pair -> ft pair == eps );
delta = min apply(S,pair-> uDeficit(pair_0,pair_1,r));
S= select(S, pair -> uDeficit(pair_0,pair_1,r) == delta )
graph = append(graph, S);
num = append(num,(eps,delta))

graph

num

apply(graph, x -> #x)

apply(graph, S -> apply(S, x -> first entries transpose last x))    
-- Good examples
toString(A,u)

r = 5
(A,u) = (matrix {{10, 3, 5}, {3, 9, 8}, {3, 8, 5}}, matrix {{6}, {6}, {5}})
-- 122c, one interm power, different collapses on same level, 2-cycle            
(A,u) = (matrix {{5, 6, 5}, {7, 10, 3}, {10, 4, 5}},matrix {{6}, {6}, {3}})
-- 132c, one iterm power, collapses of different sizes on same level, 1-cycle
-- But this is a binomial!  

(A,u) = (matrix {{14, 3, 11}, {10, 4, 15}, {2, 14, 5}, {7, 1, 11}},matrix {{3}, {9}, {6}, {3}})  
-- BEST YET! Could even start in 3rd level:
(A,u) = (matrix {{14, 3, 11}, {2, 14, 5}},matrix {{6}, {1}})

-- or start with a collase
(A,u) = (matrix {{14, 3, 11}, {2, 14, 5}},matrix {{3}, {6} })  

A
 
r = 7
(A,u) = (matrix {{9, 8, 9}, {1, 5, 5}, {1, 8, 2}},matrix {{4}, {3}, {1}})
-- 1422c, 2-cycle, collapses of different size on same level, one interm power
-- but this is actually a binomial!

-- running example
r = 11
A = matrix {{5,3,4},{5,4,3},{2,8,5}}
u = colVec {1,1,1}

univDenom A

------------------------------
(A,u) = (matrix {{14, 3, 11}, {10, 4, 15}, {2, 14, 5}, {7, 1, 11}},matrix {{3}, {9}, {6}, {3}})  

r = 5
(A,u) = (matrix {{14, 3, 11}, {10, 4, 15}, {2, 14, 5}, {7, 1, 11}},matrix {{3}, {5}, {6}, {5}})  
num = {(ft(A,u),uDeficit(A,u,r))};
graph = {{(A,u)}}

S = last graph;
S =  unique flatten apply( S, t -> apply(uShort(t_0,t_1,r),v -> (collapse(t_0,t_1),v) )); 
eps = max apply(S,pair->ft pair); 
S= select(S, pair -> ft pair == eps );
delta = min apply(S,pair-> uDeficit(pair_0,pair_1,r));
S= select(S, pair -> uDeficit(pair_0,pair_1,r) == delta )
graph = append(graph, S);
num = append(num,(eps,delta))

graph

num

apply(graph, x -> #x)

-- In search of smaller univDenom

-- running example

A = matrix {{5,3,4},{5,4,3},{2,8,5}}

univDenom A
univDenom2 A

facesOfN = properFaces newton A

apply( facesOfN, F -> selectColumnsInFace( A, F ) | rb F )

----------------------------------------------------------

A = matrix{ {2,1,0,2},{0,1,2,2} }
u = colVec {1,1}
ft(A,u)
s = specialPt(A,u)
bracket(s,4)

uDeficit(A,u,4)

solveIP theta(A,u,s,4)

A = matrix{{3,0},{0,2},{1,1}}
apply(2..20,i->numeric ft(A,colVec{2,1,i}))
------------------------

A = matrix{ {36,10,31},{19,46,31},{47,25,36} }
u = colVec {29,24,30}

univDenom2 A
univDenom A

mu(A,u,11)
crit(A,u,11)

toString oo

-----------------------------------
A = matrix { {5,3,4}, {5,4,3}, {2,8,5} }
u = colVec {1,1,1}

univDenom2 A
univDenom A

mu(A,u,11)
toString oo

crit(A,u,11)

N = newton A
vertices N

Nbar = newton collapse(A,u)
vertices Nbar

c1 = convexHull matrix{{0,5,3},{0,2,8}}
latticePoints c1

------------------------------------
A = matrix { {2,4,7}, {6,4,3} }
N = newton A

mu(A,colVec {3,4},11)
crit(A,colVec {3,4},11)

propfaces = properFaces N
regions = apply( propfaces, F -> convexHull {F, colVec {0,0}})
compactregions = select(regions,isCompact)
apply(compactregions,latticePoints)

univDenom A

G = mu(A,colVec {3,4},11)

g = G*(1-p*t)
sub(numerator g, t => 1/p)/sub(denominator g, t => 1/p)



apply( propfaces, F -> - objectiveVector(N,F) )

viewHelp Polyhedra

peek N#cache
halfspaces N
faces N

--- test isStandard, properStandardFaces

N = newton transpose matrix {{0,4},{2,2},{5,1}}
facesOfN = properFaces N
isStandard \ facesOfN

properStandardFaces N

N = newton transpose matrix {{4,0,0},{0,3,0},{0,0,5}}
properStandardFaces N
isStandard \ properFaces N

--- test pointsAimedAtCompactFace

N = newton transpose matrix {{4,0},{0,4}}
L = first properStandardFaces N
pointsAimedAtCompactFace L

N = newton matrix { {2,4,7}, {6,4,3} }
L = select( properStandardFaces N, isCompact)
pts = apply( pointsAimedAtCompactFace \ L, x -> apply(x, y -> first entries transpose y))

N = newton transpose matrix {{3, 11}, {4, 8}, {6, 5}, {10, 4}}
L = select( properStandardFaces N, isCompact)
toString apply( pointsAimedAtCompactFace \ L, x -> apply(x, y -> first entries transpose y))

--- tests collapseMap, collapse

collapseMap { colVec {1,0,0}}
collapseMap { colVec {1,0,0,0}, colVec {0,0,1,0}}

A = matrix { {2,4,7}, {6,4,3} }
N = newton A
L = properStandardFaces N
rb \ L
collapseMap \ L

pointsAimedAtUnboundedFace \ L

apply(L, F -> collapse(A,F))
    
-- running example
A = matrix { {5,3,4}, {5,4,3}, {2,8,5} }
u = colVec {1,1,1}
L = pointsAimedAtUnboundedFace minimalFace(A,u)
toString apply(L, x -> first entries transpose x)

rb(A,u)
rb(collapse(A,u), colVec {10,1})
rb(collapse(A,u), colVec {1,10})

-- test matrixToPoints, pointsToMatrix

A = matrix { {5,3,4,1}, {5,4,0,3}, {1,2,8,5} }
pts = matrixToPoints A
mat = pointsToMatrix pts
A == mat

-- test liftPoint, pointsAimedAtUnboundedFace

rbasis = { colVec {0,1,0,0,0}, colVec {0,0,0,0,1} }
P = liftPoint( colVec {1,2,3}, rbasis ) 

-- test makeMonomial
 
QQ[x,y,z]
makeMonomial({x,y,z},{3,7,1})
makeMonomial({x,y,z}, colVec {3,7,1})

-- test steps

-- From Fig, 6 in arithmetic integer program paper
A = transpose matrix { {1,10},{3,6},{7,3},{10,2} }
steps A

-- running example
A = matrix { {5,3,4}, {5,4,3}, {2,8,5} };
steps A

print \ irreducibleDecomposition matrixToIdeal A;

steps transpose matrix { {5,0},{4,1},{3,2},{2,3},{1,4},{0,5} }

-- test matrixToIdeal
A =  transpose matrix { {1,7,10},{5,0,6},{7,3,4},{10,2,0} }
I = matrixToIdeal A
B = idealToMatrix I
A == B

-- test types

timing newton matrix{ {5,3,4}, {5,4,3}, {2,8,5} }
timing univDenom monomialMatrix { {5,3,4}, {5,4,3}, {2,8,5} }
A = monomialMatrix { {5,3,4}, {5,4,3}, {2,8,5} }
peek A#cache
timing newton A
timing univDenom A

properFaces newton A
n = first keys (A#cache)
peek A#cache#n#cache

timing ft monomialPair( { {5,3,4}, {5,4,3}, {2,8,5} }, {1,1,1} )
P = monomialPair( { {5,3,4}, {5,4,3}, {2,8,5} }, {1,1,1} )
peek P#cache
peek P#matrix#cache
timing ft P

timing minimalFace( { {5,3,4}, {5,4,3}, {2,8,5} }, {1,1,1} )
P = monomialPair( { {5,3,4}, {5,4,3}, {2,8,5} }, {1,1,1} )
peek P#cache
peek P#matrix#cache
timing minimalFace P

timing specialPoint( { {5,3,4}, {5,4,3}, {2,8,5} }, {1,1,1} )
P = monomialPair( { {5,3,4}, {5,4,3}, {2,8,5} }, {1,1,1} )
peek P#cache
timing specialPoint P

----------

--- From Examples paper
-- 3.14, 3.15
QQ[x,y,z];
m=ideal(x,y,z);
A = transpose matrix apply( (m^7)_*, f -> first exponents f );
print \  criticalExponents( A, 6, Verbose => true );
print \  criticalExponents( A, 5, Verbose => true );
-- taking way too long (even after several hours, could not 

--  5.11, 5.12
A = 7*identityMatrix(3);
print \  criticalExponents( A, 6, Verbose => true );
print \  criticalExponents( A, 5, Verbose => true );
-- got all crits!
print \ frobeniusPowers( A, 6, {x,y,z} );
print \ frobeniusPowers( A, 5, {x,y,z} );
-- Missing last ideal in each
    
-- 5.15
A = matrix {{6,0},{0,4}};
print \ criticalExponents( A, 5, Verbose => true );
-- got all crits!
QQ[x,y]
print \ frobeniusPowers( A, 5, {x,y}, Verbose => true );
-- PERFECT!

-- 5.13
A = 47*identityMatrix(2);
print \ criticalExponents( A, 7, Verbose => true );
-- got all listed in paper.

-- checking a random pair, for what was stored:

peek (monomialPair( A, colVec {4,42} ))#cache
peek (monomialMatrix A)#cache
--- FROM Frobenius paper

-- 3.24
QQ[x,y];
m=ideal(x,y);
A = transpose matrix apply( (m^7)_*, f -> first exponents f );
print \ criticalExponents( A, 4, Verbose => true );
-- got all crits!
print \ frobeniusPowers( A, 4, {x,y});
-- PERFECT!

-- 3.25
QQ[x,y];
m=ideal(x,y);
A = transpose matrix apply( (m^5)_*, f -> first exponents f );
print \ criticalExponents( A, 3, Verbose => true );
-- got all crits!
print \ frobeniusPowers( A, 3, {x,y} );
-- PERFECT!

A = 5*identityMatrix(2);
print \ criticalExponents( A, 3, Verbose => true );
-- got all crits!
QQ[x,y]
print \ frobeniusPowers( A, 3, {x,y} );
-- PERFECT!

--- A homogeneous trinomial in 3 vars (INTERESTING!)
A = transpose matrix { {5,7,0}, {0,5,7}, {7,0,5} };
print \ criticalExponents( A, 3, Verbose => true );
QQ[x,y,z]
print \ frobeniusPowers( A, 3, {x,y,z} );
-- taking too long

--- A homogeneous trinomial in 3 vars
A = transpose matrix { {10,0,0}, {1,6,3}, {0,3,7} };
print \ criticalExponents( A, 7, Verbose => true );

--- A homogeneous trinomial in 3 vars
A = transpose matrix { {8,7,0}, {0,9,6}, {5,0,10} };
print \ criticalExponents( A, 3, Verbose => true );

--- Trevor's example
A = matrix{ {0,3,2}, {6,0,2} }
univDenom A
print \ criticalExponents( A, 11, Verbose => true );
print \ frobeniusPowers( A, 5, {x,y}, Verbose => true );

---------------------------------------------------------------------------------------------
--- Our running example
---------------------------------------------------------------------------------------------

A = matrix { {5,3,4}, {5,4,3}, {2,8,5} };
print \ criticalExponents( A, 11, Verbose => true );

QQ[x,y,z]
print \ frobeniusPowers( A, 11, {x,y,z} );

-- checking random pair
P = monomialPair( A, colVec {1,1,1} )
peek P#cache
peek P#matrix#cache

---------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------

QQ[x,y]
m = ideal(x,y)    
timing integralClosure(m^5)
timing integralClosure(m^5, Strategy => RadicalCodim1)
timing integralClosure(m^5, Strategy => Radical)
timing integralClosure(m^5, Strategy => AllCodimensions)
timing integralClosure(m^5, Strategy => Vasconcelos)
timing integralClosure(m^5, Strategy => SimplifyFractions)
timing integralClosure(m^5, Strategy => StartWithOneMinor)
timing integralClosure monomialIdeal m^5

timing integralClosure(m^7, Strategy => StartWithOneMinor)
timing integralClosure monomialIdeal m^7

timing I = integralClosure ideal(x^7,y^7)
timing J = integralClosure monomialIdeal (x^7,y^7)
I == J 

R = QQ[x,y,z]
A = matrix { {5,3,4}, {5,4,3}, {2,8,5} };

timing I = integralClosure matrixToIdeal( A, R )
timing J = integralClosure ideal I
J == I

vertices hypercube( 3, 0, 1 )
