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
minFace = method()
minFace ( Matrix, List ) := (A,u) -> (
    NA := newton A;
    int := intersection( coneFromVData transpose matrix {u}, NA );
    smallestFace( vertices int, NA )
)
minFace Matrix := A -> minFace( A, constantList( 1, rank target A ) )
     
-- recession basis for minimal face     
rb = method()
rb ( Matrix, List ) := (A,u) -> entries transpose rays tailCone minFace(A,u)
rb Matrix := A -> entries transpose rays tailCone minFace A

collapse = method()
collapse (Matrix, List) := (A,u) -> (
    rbasis := rb(A,u);
    d := rank target A;
    idMat := entries identityMatrix d;
    proj := matrix select( idMat, v -> not member( v, rbasis ) );
    proj*A
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
