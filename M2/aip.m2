loadPackage("Polyhedra", Reload => true)

-------------------------------------------------------------------------------
-- Auxiliary Functions
-------------------------------------------------------------------------------

constantList := (c,n) -> apply( n, x -> c )

identityMatrix := n -> id_(ZZ^n)

denominator List := L -> lcm apply( L, denominator )
numerator List := L -> denominator(L) * L

posRes = method()
posRes (ZZ,ZZ) := (a,d) -> (
    residue := a % d;
    if residue == 0 then d else residue
)
posRes (List,ZZ) := (L,d) -> apply(L, x -> posRes(x,d) )

bracket = method()
bracket (QQ,ZZ) := (t,q) -> (
    a := numerator t;
    b := denominator t;
    posRes( a*q, b )/b
)
bracket (ZZ,ZZ) := (t,q) -> bracket(t/1,q)
bracket (List,ZZ) := (L,q) -> apply(L, t -> bracket(t,q))

canVec := (n,i) -> apply( n, j -> if i == j then 1 else 0 )

randomMatrix := (m,n,maximum) -> matrix apply( m, i -> apply( n, j -> random(maximum) ) )

-------------------------------------------------------------------------------
-- Polyhedral Stuff
-------------------------------------------------------------------------------

-- newtonPolyhedron
newton := A -> convexHull( A ) + posOrthant( rank target A )

-- splitting polytope
split = method() 
split ( Matrix, List ) := ( A, u ) -> 
(
    n := rank source A;
    M := A || - identityMatrix n; 
    v := u | constantList( 0, n );
    polyhedronFromHData( M, transpose matrix {v} )
) 
split Matrix := A -> split( A, constantList( 1, rank target A) )

-- optimal set for linear program P(A,u)
optP = method()
optP ( Matrix, List ) := ( A, u ) -> maxFace( transpose matrix {u}, split(A, u) )
optP Matrix := A -> maxFace( transpose matrix { constantList( 1, rank source A) }, split A )     

ft = method()
ft ( Matrix, List ) := (A,u) -> (
    NA := newton A;
    intPt := first entries vertices intersection( coneFromVData transpose matrix {u}, NA );
    u#0/intPt#0
)
ft Matrix := A -> ft( A, constantList( 1, rank target A ) )
    
-- minimal face mf(A,u)
minimalFace = method()
minimalFace ( Matrix, List ) := (A,u) -> (
    NA := newton A;
    int := intersection( coneFromVData transpose matrix {u}, NA );
    smallestFace( vertices int, NA )
)
minimalFace Matrix := A -> minimalFace( A, constantList( 1, rank target A ) )
     
-- recession basis for minimal face     
rb = method()
rb ( Matrix, List ) := (A,u) -> entries transpose rays tailCone minimalFace(A,u)
rb Matrix := A -> entries transpose rays tailCone minimalFace A

collapse = method()
collapse (Matrix, List) := (A,u) -> (
    rbasis := rb(A,u);
    d := rank target A;
    idMat := entries identityMatrix d;
    proj := matrix select( idMat, v -> not member( v, rbasis ) )
)
collapse Matrix := A -> collapse( A, constantList( 1, rank target A ) )

-- a minimal coordinate
minCoord = method()
minCoord (Matrix,List) := (A,u) -> first entries transpose interiorPoint optP(A,u)
minCoord Matrix := A -> first entries transpose interiorPoint optP A

consTheta = (A,u,s,q) -> (
    n := rank source A;
    d := rank target A;
    nonnegConstraints := apply(select(n, i -> s#i == 0), i -> -canVec(n,i));
    nonnegConstraintsRHS := apply(select(n, i -> s#i == 0), i -> 0);
    B := collapse(A,u);
    otherConstraints := B || matrix {constantList(-1,n)};  
    otherConstraintsRHS := B*(transpose matrix {bracket(s,q)}) || matrix {{0}};
    constraints := if nonnegConstraints === {} then otherConstraints else matrix nonnegConstraints | otherConstraints;
    constraintsRHS := if nonnegConstraints === {} then otherConstraintsRHS else matrix nonnegConstraintsRHS | otherConstraintsRHS;
    print( constraints | constraintsRHS );
    polyhedronFromHData( constraints, constraintsRHS )
)

--------------------------------------------

PA = consTheta(A,{1,1,1},minCoord A,2)        

PB = consTheta(B,{1,1},minCoord B,224)        

toString minCoord B


hyperplanes PA
hyperplanes PB

hyperplanes maxFace(matrix {{1},{1}},PA)
hyperplanes maxFace(matrix {{1},{1},{1},{1},{1},{1}},PB)

--------------------------------------------------------------------------------------------------     
A = matrix { {2, 7}, {7, 2}, {5, 5} }    
B = matrix { {5, 4, 3, 2, 1, 0}, {0, 1, 2, 3, 4, 5} }

NA = newton A
NB = newton B

halfspaces NA

SA = split A
SB = split B

halfspaces SA

dim SB
ambDim NA

int = intersection( coneFromVData matrix {{1},{1},{1}}, NA )
vertices int
minFace A

rays tailCone minFace A

optA = optP A
vertices optA

optB = optP B
vertices optB

rb A
rb B

vertices minFace B
vertices optP B

minCoord A
minCoord B

ft A
ft B

sum minCoord A
sum minCoord B

minCoord A
A*(minCoord A)
B*(minCoord B)

rb A
A
collapse B
minCoord B

---------------
-- Example 1

A = matrix {{3, 1}, {9, 1}, {0, 4}, {3, 10}, {7, 8}}

split A

toString entries transpose vertices split A

vertices optP A

ZZ/11[x,y,z,u,v]
fpt(x^3*y^9*u^3*v^7+x*y*z^4*u^10*v^8)

---------------
-- Example 2

A = matrix {{6, 9}, {6, 8}, {10, 4}, {4, 10}}

split A

toString entries transpose vertices split A

vertices optP A

ZZ/7[x,y,z,u]
fpt(x^6*y^6*z^10*u^4 + x^9*y^8*z^4*u^10)

---------------
-- Example 3

A = matrix {{1, 11}, {5, 10}, {9, 8}, {11, 1}}

split A

toString entries transpose vertices split A

vertices optP A

ZZ/2[x,y,z,u]
fpt(x^1*y^5*z^9*u^11 + x^11*y^10*z^8*u^1)

---------------
-- Example 3

A = matrix {{4, 9}, {6, 7}, {9, 3}, {1, 7}}

split A

toString entries transpose vertices split A

vertices optP A

ZZ/2[x,y,z,u]
fpt(x^1*y^5*z^9*u^11 + x^11*y^10*z^8*u^1)

---------------
-- Example 4

A = matrix {{3, 11}, {11, 2}, {5, 10}, {2, 0}}

toString entries transpose vertices split A

vertices optP A

ZZ/5[x,y,z,u]
fpt(x^3*y^11*z^5*u^2 + x^11*y^2*z^10*u^0)

----------------
ZZ/2[x,y]
fpt(x + y)

apply(1..7, i -> nu(i,ideal(x,y))/2^i)

---------------------

scan(100, i ->
    ( 
        A = randomMatrix(3,3,10);
        c = collapse A;
        if #(rb A) == 1 and vertices optP A != vertices optP(c*A)
            then (print toString entries transpose A; print "\n")        
    )
)

entries A

ZZ/5[x,y,z]
I := L -> ideal apply( L, u -> x^(u#0)*y^(u#1)*z^(u#2) )
trim( I {{5, 5, 2}, {3, 4, 8}, {4, 3, 5}} )

A = transpose matrix {{9, 0, 7}, {4, 5, 3}, {2, 0, 7}}
ft A

A = transpose matrix {{8, 6, 7}, {4, 4, 9}, {4, 9, 4}}
ft A

--- tHiS!
A = transpose matrix {{5, 5, 2}, {3, 4, 8}, {4, 3, 5}}
--- ThIs!

vertices minimalFace A
isCompact minimalFace A
rb A
c = collapse A

toString entries transpose vertices split A
toString entries transpose vertices optP A

toString entries transpose vertices split(c*A)
toString entries transpose vertices optP(c*A)

ft A

halfspaces optP A
halfspaces optP(c*A)

entries A -- {{2, 0, 4}, {4, 0, 4}, {2, 2, 1}, {1, 1, 4}} -- optimal set different from optimal set of collapse


-- matrix {{2, 0, 4}, {4, 0, 4}, {2, 2, 1}, {1, 1, 4}}

ft(A)
ft(c*A)

halfspaces split A
halfspaces split (c*A)
contains(split(c*A),optP(c*A))
halfspaces( optP(c*A) )
toString entries transpose vertices optP(c*A)

contains(optP(c*A),optP A)
contains(split(c*A),split A)

toString entries transpose vertices split A
toString entries transpose vertices split(c*A)

--------------------------------------------------------
A = transpose matrix {{5, 5, 2}, {3, 4, 8}, {4, 3, 5}}

L = faces(1, newton A)
vert = vertices newton A
apply(L, f -> vert_(f#0))
