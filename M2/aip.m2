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
rb ( Matrix, List ) := (A,u) -> tailCone minFace(A,u)
rb Matrix := A -> tailCone minFace A
    
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

rays rb B
vertices minFace B
vertices optP B
