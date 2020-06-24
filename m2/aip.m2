loadPackage("Polyhedra")
loadPackage("FrobeniusThresholds")
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

colVec := u -> transpose matrix {u}
--transforms a one-dimensional list into a column vector

constantMatrix := (c,m,n) -> matrix toList apply(m, i -> toList apply(n, x -> c) )

zeroMatrix := (m,n) -> constantMatrix(0,m,n)
    
getFilename = () -> 
(
    filename := temporaryFileName();
    while 
    (
        fileExists filename 
        or 
        fileExists( filename|".mat" ) 
        or 
        fileExists( filename|".zsol" ) 
        or 
        fileExists( filename|".cost" ) 
        or 
        fileExists( filename|".min" ) 
        or 
        fileExists( filename|".sign" ) 
    )    
    do filename = temporaryFileName();
    filename
)

-------------------------------------------------------------------------------
-- Polyhedral Stuff
-------------------------------------------------------------------------------

-- newtonPolyhedron
newton := A -> convexHull( A ) + posOrthant( rank target A )

-- feasLPting polytope
feasLP = method() 
feasLP ( Matrix, Matrix ) := ( A, u ) -> 
(
    n := rank source A;
    M := A || - identityMatrix n; 
    v := u || colVec constantList( 0, n );
    polyhedronFromHData( M, v )
)
feasLP ( Matrix, List ) := ( A, u ) -> feasLP( A, colVec u ) 
feasLP Matrix := A -> feasLP( A, constantList( 1, rank target A) )

-- optimal set for linear program P(A,u)
optLP = method()
optLP ( Matrix, Matrix ) := ( A, u ) -> maxFace( transpose matrix { constantList( 1, rank source A) }, feasLP(A, u) )
optLP ( Matrix, List ) := ( A, u ) -> optLP( A, colVec u )
optLP Matrix := A -> maxFace( colVec constantList( 1, rank source A ), feasLP A )     

univDenom = method()
univDenom Matrix := A ->
(
    n := rank source A;
    m := rank target A;
    I := identityMatrix n;
    M := A || -A || I || -I;
    allMinors := (minors(n, M))_*;
    (m-1)*(lcm allMinors)
)

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
specialPt = method()
specialPt (Matrix,List) := (A,u) -> first entries transpose interiorPoint optLP(A,u)
specialPt Matrix := A -> first entries transpose interiorPoint optLP A

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

solveIP := ( A, u, q ) ->
(
    m = rank target A;
    n = rank source A;
    path242 := prefixDirectory | currentLayout#"programs";
    file := getFilename();
    M := openOut(file | ".mat");
    putMatrix( M, A | identityMatrix m );
    close M;
    sol = openOut(file | ".zsol");
    putMatrix( sol, matrix { join( constantList( 0, n ), apply( first entries transpose u, x -> x*q - 1 ) ) } );
    close sol;
    cost = openOut(file | ".cost");
    putMatrix( cost, matrix { join( constantList( -1, n ), constantList( 0, m ) ) } );
    close cost;
    execstr := path242 | "minimize -q " | rootPath | file;
    ret := run(execstr);
    if ret =!= 0 then error "solveIP: error occurred while executing external program 4ti2/minimize";
    opt := getMatrix(file | ".min");
    value := first first entries (opt*(colVec join( constantList( 1, n ), constantList( 0, m ) ) ));
    -- will also return an optimal point
    optPt := transpose( opt*(identityMatrix(n) || zeroMatrix(m,n)) );
    ( value, optPt )
)    
    
valueIP := ( A, u, q ) -> first solveIP( A, u, q)

optPtIP := ( A, u, q ) -> last solveIP( A, u, q)

--------------------------------------------

PA = consTheta(A,{1,1,1},specialPt A,2)        

PB = consTheta(B,{1,1},specialPt B,224)        

toString specialPt B


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

SA = feasLP A
SB = feasLP B

halfspaces SA

dim SB
ambDim NA

int = intersection( coneFromVData matrix {{1},{1},{1}}, NA )
vertices int
minFace A

rays tailCone minFace A

optA = optLP A
vertices optA

optB = optLP B
vertices optB

rb A
rb B

vertices minFace B
vertices optLP B

specialPt A
specialPt B

ft A
ft B

sum specialPt A
sum specialPt B

specialPt A
A*(specialPt A)
B*(specialPt B)

rb A
A
collapse B
specialPt B

---------------
-- Example 1

A = matrix {{3, 1}, {9, 1}, {0, 4}, {3, 10}, {7, 8}}

feasLP A

toString entries transpose vertices feasLP A

vertices optLP A

ZZ/11[x,y,z,u,v]
fpt(x^3*y^9*u^3*v^7+x*y*z^4*u^10*v^8)

---------------
-- Example 2

A = matrix {{6, 9}, {6, 8}, {10, 4}, {4, 10}}

feasLP A

toString entries transpose vertices feasLP A

vertices optLP A

ZZ/7[x,y,z,u]
fpt(x^6*y^6*z^10*u^4 + x^9*y^8*z^4*u^10)

---------------
-- Example 3

A = matrix {{1, 11}, {5, 10}, {9, 8}, {11, 1}}

feasLP A

toString entries transpose vertices feasLP A

vertices optLP A

ZZ/2[x,y,z,u]
fpt(x^1*y^5*z^9*u^11 + x^11*y^10*z^8*u^1)

---------------
-- Example 3

A = matrix {{4, 9}, {6, 7}, {9, 3}, {1, 7}}

feasLP A

toString entries transpose vertices feasLP A

vertices optLP A

ZZ/2[x,y,z,u]
fpt(x^1*y^5*z^9*u^11 + x^11*y^10*z^8*u^1)

---------------
-- Example 4

A = matrix {{3, 11}, {11, 2}, {5, 10}, {2, 0}}

toString entries transpose vertices feasLP A

vertices optLP A

ZZ/7[x,y,z,u]
fpt(x^3*y^11*z^5*u^2 + x^11*y^2*z^10*u^0)

f = x^3*y^11*z^5*u^2 + x^11*y^2*z^10*u^0

    
----------------
ZZ/2[x,y]
fpt(x + y)

apply(1..7, i -> nu(i,ideal(x,y))/2^i)

---------------------

scan(100, i ->
    ( 
        A = randomMatrix(3,3,10);
        c = collapse A;
        if #(rb A) == 1 and vertices optLP A != vertices optLP(c*A)
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

toString entries transpose vertices feasLP A
toString entries transpose vertices optLP A

toString entries transpose vertices feasLP(c*A)
toString entries transpose vertices optLP(c*A)

ft A

halfspaces optLP A
halfspaces optLP(c*A)

entries A -- {{2, 0, 4}, {4, 0, 4}, {2, 2, 1}, {1, 1, 4}} -- optimal set different from optimal set of collapse


-- matrix {{2, 0, 4}, {4, 0, 4}, {2, 2, 1}, {1, 1, 4}}

ft(A)
ft(c*A)

halfspaces feasLP A
halfspaces feasLP (c*A)
contains(feasLP(c*A),optLP(c*A))
halfspaces( optLP(c*A) )
toString entries transpose vertices optLP(c*A)

contains(optLP(c*A),optLP A)
contains(feasLP(c*A),feasLP A)

toString entries transpose vertices feasLP A
toString entries transpose vertices feasLP(c*A)

--------------------------------------------------------
A = transpose matrix {{5, 5, 2}, {3, 4, 8}, {4, 3, 5}}

L = faces(1, newton A)
vert = vertices newton A
apply(L, f -> vert_(f#0))

----------------------------------

A = matrix {{5,3,4},{5,4,3},{2,8,5}}
d = univDenom A

opt = optLP(A,{random(100),random(100),random(100)});
v = entries transpose vertices opt;
apply(v,denominator)
apply(d*v,x->apply(x,t->lift(t,ZZ)))

installPackage "FourTiTwo"

debugLevel = 1
A = matrix "1,1,1,1; 1,2,3,4"
B = syz A
hilbertBasis transpose B
hilbertBasis(A,InputType=>"lattice")
prefixDirectory | currentLayout#"programs"

path442 = "/usr/libexec/Macaulay2/bin/"
A = matrix {{5,3,4},{5,4,3},{2,8,5}}
M = openOut("test.mat")
putMatrix( M, A | identityMatrix 3 )
close M
p = 5
e = 3
sol = openOut("test.zsol")
putMatrix( sol, matrix {{0,0,0,p^e-1,p^e-1,p^e-1}} )
close sol
signs = openOut("test.sign")
putMatrix( signs, matrix {{1,1,1,1,1,1}} )
close signs
cost = openOut("test.cost")
putMatrix( cost, matrix {{-1,-1,-1,0,0,0}} )
close cost
run "/usr/libexec/Macaulay2/bin/minimize test"
opt = getMatrix "test.min"
first first entries (opt*(colVec {1,1,1,0,0,0}))

R = ZZ/7[x,y,z]
I = monomialIdeal(x^5*y^5*z^2,x^3*y^4*z^8,x^4*y^3*z^5)
D = monomialIdeal(x^2,y^3,z^5)
frobeniusNu(3,I,D)

solveIP(A,colVec {2,3,5}, 7^3 )
optPtIP(A,colVec {2,3,5}, 7^3 )
valueIP(A,colVec {2,3,5}, 7^3 )
