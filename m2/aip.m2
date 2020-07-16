loadPackage("Polyhedra", Reload => true)
-- loadPackage("FrobeniusThresholds")
-- loadPackage("FourTiTwo") -- loaded with Polyhedra
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
    if t == 0 then return 0;
    a := numerator t;
    b := denominator t;
    posRes( a*q, b )/b
)
bracket (ZZ,ZZ) := (t,q) -> bracket(t/1,q)
bracket (List,ZZ) := (L,q) -> apply(L, t -> bracket(t,q))
bracket (Matrix,ZZ) := (M,q) -> matrix apply(entries M, t -> bracket(t,q))

canVec := (n,i) -> apply( n, j -> if i == j then 1 else 0 )

randomMatrix := (m,n,maximum) -> matrix apply( m, i -> apply( n, j -> random(maximum) ) )

colVec := u -> transpose matrix {u}
--transforms a one-dimensional list into a column vector

constantMatrix := (c,m,n) -> matrix toList apply(m, i -> toList apply(n, x -> c) )

constantVector := (c,m) -> constantMatrix(c,m,1)

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
feasLP Matrix := A -> feasLP( A, constantVector( 1, rank target A) )

-- optimal set for linear program P(A,u)
optLP = method()
optLP ( Matrix, Matrix ) := ( A, u ) -> maxFace( transpose matrix { constantList( 1, rank source A) }, feasLP(A, u) )
optLP ( Matrix, List ) := ( A, u ) -> optLP( A, colVec u )
optLP Matrix := A -> maxFace( constantVector( 1, rank source A ), feasLP A )     

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

properFaces = method() 

properFaces Polyhedron := P -> 
(
    d := dim P;
    toList sum(1..d, i -> set facesAsPolyhedra( i, P ) )
)

selectColumnsInFace = method()

selectColumnsInFace ( Matrix, Polyhedron ) := ( A, P ) ->
(
   indices := select( rank source A, i -> contains( P, A_{i} ) );
   A_indices
)

lcmMinors := A -> 
(
    d := min( numRows A, rank source A );
    lcm ( minors( d, A ) )_*
)

univDenom2 = method()
univDenom2 Matrix := A ->
(
    faces := properFaces newton A;
    matrices := apply( faces, F -> selectColumnsInFace( A, F ) | rb F );
    ( numRows( A ) - 1 )*lcm apply( matrices, M -> lcmMinors M )
) 
 
ft = method()
ft ( Matrix, Matrix ) := (A,u) -> (
    NA := newton A;
    intPt := first entries vertices intersection( coneFromVData u, NA );
    u_(0,0)/intPt#0
)
ft ( Matrix, List ) := (A,u) -> ft(A,colVec u)
ft Matrix := A -> ft( A, constantVector( 1, rank target A ) )


-- minimal face mf(A,u)
minimalFace = method()
minimalFace ( Matrix, Matrix ) := (A,u) -> (
    NA := newton A;
    int := intersection( coneFromVData u, NA );
    smallestFace( vertices int, NA )
)
minimalFace ( Matrix, List ) := (A,u) -> minimalFace(A, colVec u)
minimalFace Matrix := A -> minimalFace( A, constantVector( 1, rank target A ) )
     
-- recession basis for minimal face     
rb = method()
rb ( Matrix, Matrix ) := (A,u) -> entries transpose rays tailCone minimalFace(A,u)
rb ( Matrix, List ) := (A,u) -> rb(A, colVec u)
rb Matrix := A -> entries transpose rays tailCone minimalFace A
rb Polyhedron := P -> rays tailCone P

collapseMap = method()
collapseMap (Matrix, Matrix) := (A,u) -> (
    rbasis := rb(A,u);
    d := rank target A;
    idMat := entries identityMatrix d;
    proj := matrix select( idMat, v -> not member( v, rbasis ) )
)
collapseMap (Matrix,List) := (A,u) -> collapseMap(A,colVec u)
collapseMap Matrix := A -> collapseMasp( A, constantVector( 1, rank target A ) )

collapse = method()
collapse (Matrix,Matrix) := (A,u) -> collapseMap(A,u)*A
collapse (Matrix,List) := (A,u) -> collase(A, colVec u)
    
-- a special point
specialPt = method()
specialPt (Matrix,Matrix) := (A,u) -> interiorPoint optLP(A,u)
specialPt (Matrix,List) := (A,u) -> interiorPoint optLP(A,u)
specialPt Matrix := A -> interiorPoint optLP A

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
-- Integer Programs

IntegerProgram = new Type of HashTable
-- IntegerProgram is a hash table that carries the information of an integer program of the following type:
-- Maximize w^T*x, subject to Ax <= u, x >= 0, x \in ZZ^n 

-- integerProgram creates an IntegerProgram from a matrix A, a column vector u 
-- (the RHS of the linear constraint inequality), and a column vector w 
-- (the weights/cost defining the linear function to be maximized) 
integerProgram = method()

integerProgram ( Matrix, Matrix, Matrix ) := ( A, u, w ) -> new IntegerProgram from
{
    cache => new CacheTable,
    "matrix" => A,
    "RHS" => u,
    "weights" => w,
    "dim" => ( numRows A, rank source A ),
    "augmentedMatrix" => A | identityMatrix numRows A -- adds columns corresponding to slack variables
}

integerProgram ( Matrix, Matrix, Matrix, Matrix ) := ( A, u, w, s ) -> new IntegerProgram from
{
    cache => new CacheTable,
    "matrix" => A,
    "RHS" => u,
    "weights" => w,
    "dim" => ( numRows A, rank source A ),
    "augmentedMatrix" => A | identityMatrix numRows A, -- adds columns corresponding to slack variables
    "signs" => s
}
        
solveIP := IP ->
(
    -- if the result is already cached, just return it
    if IP#cache#?"value" then return ( IP#cache#"value", IP#cache#"optimalPoint" );
    -- if not, now let's compute things...
    ( m, n ) := IP#"dim";
--    path242 := prefixDirectory | currentLayout#"programs";
    path242 := "/usr/local/bin/";
    file := getFilename();
    -- store the augmented matrix
    M := openOut( file | ".mat");
    putMatrix( M, IP#"augmentedMatrix" );
    close M;
    -- store a (all-slack) solution to Mx=u 
    sol := openOut( file | ".zsol");
    putMatrix( sol, matrix { constantList( 0, n ) } | transpose IP#"RHS" );
    close sol;
    -- store the cost (weight) vector
    cost := openOut( file | ".cost");
    putMatrix( cost, transpose( -IP#"weights" ) | matrix { constantList( 0, m ) } );
    close cost;
    -- store signs (if available)
    if IP#?"signs" then
    (
        signs := openOut( file | ".sign");
        putMatrix( signs, transpose( IP#"signs" ) | matrix { constantList( 1, m ) } );
        close signs
    );
    -- run 4ti2
    execstr := path242 | "minimize --quiet --precision=64 " | rootPath | file;
    ret := run execstr;
    if ret =!= 0 then error "solveIP: error occurred while executing external program 4ti2/minimize";
    opt := getMatrix( file | ".min" );
    value := first first entries (opt*( IP#"weights" || zeroMatrix(m,1) ) );
    -- will also return an optimal point
    optPt := transpose( opt*(identityMatrix(n) || zeroMatrix(m,n)) );
    IP#cache#"value" = value;
    IP#cache#"optimalPoint" = optPt;
    ( value, optPt )
)    

solveIP = memoize solveIP

valueIP := IP -> first solveIP IP

optPtIP := IP -> last solveIP IP

-- TO DO: Check for compactness to see if this is finite
optSetIP := IP ->
(
    -- if the result is already cached, just return it
    if IP#cache#?"optimalSet" then return IP#cache#"optimalSet";
    -- if not, now let's compute things...
    ( m, n ) := IP#"dim";
    value := valueIP IP;
    M := IP#"matrix" || - identityMatrix n;
    uu := IP#"RHS" || zeroMatrix( n, 1 );
    N := transpose IP#"weights";
    vv := matrix {{ value }};
    optPts := latticePoints polyhedronFromHData( M, uu, N, vv );
    optImage := unique apply( optPts, u -> A*u );
    IP#cache#"optimalSet" = optPts;
    IP#cache#"optimalImage" = optImage;
    optPts
)    

optImageIP := IP ->
(
    -- if the result is already cached, just return it
    if IP#cache#?"optimalImage" then return IP#cache#"optimalImage";
    -- if not, now let's compute things...
    optSetIP IP;
    IP#cache#"optimalImage"
    -- TBC
    -- Use process used in uData    
)    

-- this just sets up the integer program Theta
theta := (A,u,s,q) -> (
    Abar := collapse(A,u);
    m := numRows Abar;
    n := rank source Abar;
    rhs := Abar*bracket(s,q) - constantVector(1,m);
    signs := colVec apply(n, i -> if s_0_i == 0 then 1 else 0 );
    weights := constantVector(1,n);
    integerProgram(Abar,rhs,weights,signs)
)

-- Transform the thing below into a general optimal image command

-- returns the universal deficit and shortfall
-- TO DO: need to check that points in the shortfall really come from integral optimal points.
uData := (A,u,q) -> 
(
    s := specialPt(A,u);
    sq := bracket(s,q);
    Abar := collapse(A,u);
    Asq := Abar*sq;
    m := numRows Abar;
    n := rank source Abar;
    val := first solveIP theta(A,u,s,q);
    eqsMat := Abar | -identityMatrix m;
    eqsMat = eqsMat || matrix { join( constantList( 1, n ), constantList( 0, m ) ) };
    eqsRHS := colVec append( constantList( 0, m ), val );
    nonnegConstraints := apply(select(n, i -> s_0_i == 0), i -> - canVec(m+n,i));
    nonnegConstraintsRHS := apply(select(n, i -> s_0_i == 0), i -> 0);
    otherConstraints := Abar | zeroMatrix(m,m);
    otherConstraintsRHS := Asq - constantVector(1,m);
    ineqsMat := if nonnegConstraints === {} then otherConstraints else matrix nonnegConstraints || otherConstraints;
--    print(nonnegConstraints);
--    print(nonnegConstraintsRHS);
--    print(otherConstraints);
--    print(otherConstraintsRHS);
--    print(matrix { nonnegConstraintsRHS });
    ineqsRHS := if nonnegConstraintsRHS === {} then otherConstraintsRHS else (colVec nonnegConstraintsRHS) || otherConstraintsRHS;
    polyh := polyhedronFromHData( ineqsMat, ineqsRHS, eqsMat, eqsRHS );
    proj := zeroMatrix(m,n) | identityMatrix(m);
    im := latticePoints affineImage(proj,polyh);
    ( sum(first entries transpose sq) - val, apply(im, v -> Asq - v ) )
)

uDeficit := (A,u,q) -> first uData(A,u,q)

uShort := (A,u,q) -> last uData(A,u,q)
    
-- This solves the integer program Pi from the paper
solveMyIP := ( A, u, q ) ->
(
    rhs := q*u - colVec constantList( 1, numRows A );
    weights := colVec constantList( 1, rank source A );
    IP := integerProgram( A, rhs, weights );
    solveIP IP
)    
    
valueMyIP := ( A, u, q ) -> first solveMyIP( A, u, q)

optPtMyIP := ( A, u, q ) -> last solveMyIP( A, u, q)

mPrimaryMu := ( A, u, p0, p, t ) ->
(
    localUShort := memoize uShort;
    localUDeficit := memoize uDeficit;
    localFt := memoize ft;
    S := Sstar := { set{}, set{u} };
    e := 1;
    M := { 0, localFt(A,u)*p - localUDeficit(A,u,p0) };
    local newS;
    local newSstar;
    local k;
    local epsilon;
    local delta;
    while true do 
    (
        e = e + 1;
        newS = sum apply( toList Sstar#(e-1), v -> localUShort(A,v,p0) );
        if ( k = position( S, x -> x === set newS ) ) =!= null then 
            return sum(1..(k-1),i -> M_i*t^i)/(1-p*t) + sum(k..(e-1), i -> M_i*t^i )/((1-p^t)*(1-t^(e-k)));
        -- this process of maximization and minimization can be improved.    
        epsilon = max apply( newS, v -> localFt(A,v) );
        if epsilon > 1 then 
           return sum(1..(e-1),i -> M_i*t^i)/(1-p*t) + (p-1)*t^e/((1-p*t)*(1-t));
        newSStar = select( newS, v -> localFt(A,v) == epsilon );
        delta = min apply( newSstar, v -> localUDeficit(A,v,p0) );
        newSStar = select( newSstat, v -> localUDeficit(A,v,p0) == delta );   
        S = append( S, set newS);
        Sstar = append( Sstar, set newSstar );
        M = append( M, epsilon*p - delta )
    )
)

