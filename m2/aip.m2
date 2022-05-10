loadPackage("Polyhedra", Reload => true)

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

MonomialMatrix = new Type of HashTable

-- Creates a MonomialMatrix from a Matrix or a List.
-- TODO: should check if matrix is indeed a monomial matrix
-- (nonzero rows/columns, nonnegative integer coords)
monomialMatrix = method()
monomialMatrix Matrix := A -> new MonomialMatrix from { matrix => A, cache => new CacheTable }
monomialMatrix = memoize monomialMatrix
-- If monomialMatrix is called multiple times with the same matrix, memoize
-- will prevent the creation of a copy, therefore keeping the cached values

MonomialPair = new Type of HashTable

-- Creates a MonomialPair from a MonomialMatrix and a column vector, from a Matrix and a 
-- column vector, or from two Lists. 
-- TODO: should check if it is indeed a monomial pair
-- (compatible dim, positive integer point)
monomialPair = method()
monomialPair ( MonomialMatrix, Matrix ) := ( A, u ) -> 
   new MonomialPair from { matrix => A, ( symbol point ) => u, cache => new CacheTable }
monomialPair ( Matrix, Matrix ) := ( A, u ) -> monomialPair( monomialMatrix A, u )
monomialPair = memoize monomialPair
-- If monomialPair is called multiple times with the same pair, memoize
-- will prevent the creation of a copy, therefore keeping the cached values

-------------------------------------------------------------------------------
-- Auxiliary Functions
-------------------------------------------------------------------------------

-- constantList(c,n) returns a list with n copies of c
constantList := ( c, n ) -> apply( n, x -> c )

-- identityMatrix(n) returns the nxn identity matrix
identityMatrix := n -> id_( ZZ^n )

-- If L is a list of rational numbers, denominator(L) returns a
-- common denominator D for all members of L, while numerator(L) 
-- returns a list with the numerators, once all entries are written
-- with denominator D. 
-- In other words, L = numerator(L)/denominator(L).
denominator List := L -> lcm apply( L, denominator )
numerator List := L -> denominator( L ) * L

-- If t = a/b is a rational number, and q is an integer, then 
-- bracket(t,q) = (positive residue of aq module b)/b (or 0, if t is 0).
-- This operation extends to lists and matrices, in a componentwise fashion.
bracket = method()
bracket ( QQ, ZZ ) := ( t, q ) -> 
(
    if t == 0 then 0
    else
    (
        a := numerator t;
        b := denominator t;
        residue := a*q % b;
        -- make it a *positive* residue
        if residue == 0 then residue = b;
        residue / b
    )
)
bracket ( ZZ, ZZ ) := ( t, q ) -> bracket( t/1, q )
bracket ( List, ZZ ) := ( L, q ) -> apply( L, t -> bracket( t, q ) )
bracket ( Matrix, ZZ ) := ( M, q ) -> matrix apply( entries M, t -> bracket( t, q ) )

--pointsToMatrix gathers mx1 matrices into a big matrix
pointsToMatrix := L -> fold( ( x, y ) -> x | y, L )

--columns returns the columns of a matrix in a list 
--(the reverse of what pointsToMatrix does)
columns := M -> apply( rank source M, i -> M_{i} )

standardBasis := n -> columns identityMatrix n

-- columnVector(u) transforms a one-dimensional list u into a column vector
columnVector := u -> transpose matrix { u }

-- constantMatrix(c,m,n) generates an mxn matrix whose entries all equal c. 
constantMatrix := ( c, m, n ) -> matrix toList apply( m, i -> toList apply( n, x -> c ) )

-- constantVector(c,m) generates an m dimensional column vector whose entries all equal c. 
constantVector := ( c, m ) -> constantMatrix( c, m, 1 )

-- zeroMatrix(m,n) returns the mxn zero matrix.
zeroMatrix := ( m, n ) -> constantMatrix( 0, m, n )

-- zeroVector(m) returns the m-dim zero vector.
zeroVector := m -> zeroMatrix( m, 1 )

-- getFilename generates a random name for temporary files.    
getFilename := () -> 
(
    filename := temporaryFileName();
    while 
    (
        fileExists filename 
        or 
        fileExists( filename | ".mat" ) 
        or 
        fileExists( filename | ".zsol" ) 
        or 
        fileExists( filename | ".cost" ) 
        or 
        fileExists( filename | ".min" ) 
        or 
        fileExists( filename | ".sign" ) 
        or 
        fileExists( filename | ".rhs" ) 
        or 
        fileExists( filename | ".rel" ) 
        or 
        fileExists( filename | ".zinhom" ) 
    )    
    do filename = temporaryFileName();
    filename
)

fourTiTwo = findProgram(
    "4ti2", 
    "markov -h",
    Prefix => {
        (".*", "4ti2-"), -- debian
        (".*", "4ti2_")}, -- suse
    AdditionalPaths => {"/usr/lib/4ti2/bin", "/usr/lib64/4ti2/bin"} -- fedora
)

-- builds a monomial from a list of variables and a list (or column matrix) of exponents
makeMonomial = method()
makeMonomial ( List, List ) := ( variables, exps ) -> product( variables, exps, ( x, a ) -> x^a )  
makeMonomial ( List, Matrix ) := ( v, e ) -> makeMonomial( v, first entries transpose e )

-- Makes the ideal associated to a monomial matrix.
-- If a ring or variables are not given, it creates a ring.
-- [Used in integralClosure and minimalPoints]
matrixToIdeal = method()
matrixToIdeal ( Matrix, List ) := ( A, variables ) -> 
    monomialIdeal apply( columns A, u -> makeMonomial( variables, u ) )
matrixToIdeal ( Matrix, Ring ) := ( A, R ) -> matrixToIdeal( A, R_* )
matrixToIdeal Matrix := A -> 
(
    m := rank target A;
    X := getSymbol "X";
    R := QQ( monoid[ X_1..X_m ] );
    matrixToIdeal( A, R )
) 

-- Returns the matrix associated with monomial generators of an ideal
-- [Used in integralClosure and minimalPoints]
idealToMatrix := I -> transpose matrix apply( I_*, m -> first exponents m )

-- Given a list of points u, will create the ideal generated by x^(u-1).
-- [Used only in frobeniusPowers]
makeIdeal := ( variables, L ) -> 
    ideal apply( L,  u -> makeMonomial( variables, u - constantVector( 1, #variables ) ) )

-- The order of a Laurent polynomial
-- [Used in criticalExponents]
ord := f -> min( first \ degree \ terms f ) 

-- Integral closure of a monomial ideal, using Newton polytope
-- [Not used anywhere]
integralClosure MonomialIdeal := o -> I -> 
(
    R := ring I;
    A := idealToMatrix I;
    m := numRows A;
    P := convexHull( A ) + hypercube( m, 0, 1 );
    trim matrixToIdeal( pointsToMatrix latticePoints P, R )
)    

-- Given list of points, returns the minimal ones, wrt componentwise inequality.
-- [Used in minimalSmallNotVerySmall]
minimalPoints := L -> columns idealToMatrix trim matrixToIdeal pointsToMatrix L

-- Selects the minimal elements of a list L of sets or lists or polyhedra
-- with respect to containment
-- [Used in maximalBoundedFaces]
maximalSets := L -> 
    select( L, A -> select( L, B -> contains( B, A ) ) == { A } )

-- Finds elements in a list that maximize a function f.
-- Returns the max value of f, and the elements of the list at which the max is attained
-- [Used in mu]
maximize := ( L, f ) ->
(
    vals := apply( L, f );
    maximum := max vals;
    ( maximum, L_( positions( vals, x -> x == maximum ) ) )
)

-- Finds elements in a list that minimize a function f.
-- Returns the min value of f, and the elements of the list at which the min is attained
-- [Used in mu]
minimize := ( L, f ) ->
(
    vals := apply( L, f );
    minimum := min vals;
    ( minimum, L_( positions( vals, x -> x == minimum ) ) )
)

-------------------------------------------------------------------------------
-- Polyhedral Stuff
-------------------------------------------------------------------------------

-- newtonPolyhedon(A) returns the newton polyhedron of a matrix A.
newtonPolyhedon = method()
newtonPolyhedon MonomialMatrix := ( cacheValue symbol newtonPolyhedon )( A -> 
    convexHull( A#matrix ) + posOrthant( rank target A#matrix ) 
)
newtonPolyhedon Matrix := A -> newtonPolyhedon monomialMatrix A

-- properFaces(P) returns a list of all proper nonempty nfaces of the polyhedron P.
properFaces = method() 
properFaces Polyhedron := ( cacheValue symbol properFaces )( P -> 
    flatten toList apply( 1..( dim P ), i -> facesAsPolyhedra( i, P ) )
)

isStandard = method()
isStandard Polyhedron := ( cacheValue symbol isStandard )( P -> 
(
    n := ambDim P;
    I := identityMatrix n;
    coordSpaces := apply(n, j -> coneFromVData transpose matrix drop(entries I, { j, j } ) );
    not any(coordSpaces, S -> contains( S, P ) )
))

-- returns all proper standard faces
standardFaces = method()
standardFaces Polyhedron := ( cacheValue symbol standardFaces )( P -> 
    select( properFaces P, isStandard )
)

-- returns bounded standard faces
boundedFaces = method()
boundedFaces Polyhedron := ( cacheValue symbol boundedFaces )( P -> 
    select( standardFaces P, isCompact )
)

-- returns maximal bounded standard faces
maximalBoundedFaces = method()
maximalBoundedFaces Polyhedron := ( cacheValue symbol maximalBoundedFaces )( P -> 
    maximalSets boundedFaces P
)

-- returns unbounded proper standard faces
unboundedFaces = method()
unboundedFaces Polyhedron := ( cacheValue symbol unboundedFaces )( P -> 
    select( standardFaces P, F -> not isCompact F )
)

-- selectColumnsInFace(A,P) returns a submatrix of A consisting of all columns
-- contained in the polyhedron P.
selectColumnsInFace = method()
selectColumnsInFace ( Matrix, Polyhedron ) := ( A, P ) ->
(
   I := select( rank source A, i -> contains( P, A_{i} ) );
   A_I
)

-- lcmMinors(A) returns the lcm of all maximal minors of A.
lcmMinors := A -> 
(
    d := min( numRows A, rank source A );
    theMinors := ( minors( d, A ) )_*;
    if theMinors == {} then 0 else lcm theMinors 
)

-- This version of universalDenominator is based on the previous version of 
-- the proof in the paper (see, e.g., version 20).
-- It sometimes returns smaller denominators, making it better
-- than the other version.
univDenom2 = method()
univDenom2 Matrix := A ->
(
    local rbasis;
    faces := properFaces newtonPolyhedon A;
    matrices := apply( faces, F -> 
        (
            rbasis = recessionBasis F;
            if rbasis == {} then selectColumnsInFace( A, F ) 
            else selectColumnsInFace( A, F ) | pointsToMatrix rbasis
        )
    );
    ( numRows( A ) - 1 ) * lcm apply( matrices, M -> lcmMinors M )
) 

-- univDenon(A) returns a universal denominator for the matrix A.
universalDenominator = method()
universalDenominator MonomialMatrix := ( cacheValue symbol universalDenominator )( M ->
(
    A := M#matrix;    
    n := rank source A;
    m := rank target A;
    I := identityMatrix n;
    B := A || -A || I || -I;
    allMinors := ( minors( n, B ) )_*;
    denom := ( m - 1 ) * ( lcm allMinors );
    gcd( univDenom2 A, denom)
))
universalDenominator Matrix := A -> universalDenominator monomialMatrix A

-- degree(A,u) returns the F-threshold of the monomial pair (A,u), that is, the unique 
-- scalar lambda such that u/lambda lies in the boudary of the Newton polyhedron of A.
-- u can be a column matrix or a list.
degree MonomialPair := ( cacheValue degree )( P ->
(
    N := newtonPolyhedon P#matrix;
    u := P#point;
    -- the intersection point of the ray spanned by u and the newton polyhedron of A:
    intPt := first entries vertices intersection( coneFromVData u, N );
    u_(0,0) / intPt#0
))
degree ( Matrix, Matrix ) := ( A, u ) -> degree monomialPair( A, u ) 

-- minimalFace(A,u) returns the minimal face mf(A,u), that is, the smallest
-- face of the Newton polyhedron of A containing the scaled point u/degree(A,u).
-- u is a column matrix.
minimalFace = method()
minimalFace MonomialPair := ( cacheValue symbol minimalFace )( P ->
(
    N := newtonPolyhedon P#matrix;
    u := P#point;
    int := intersection( coneFromVData u, N );
    smallestFace( vertices int, N )
))
minimalFace ( Matrix, Matrix ) := ( A, u ) -> minimalFace monomialPair( A, u ) 

-- recession basis for polyhedron
-- returns list of points (expressed as column matrices)     
recessionBasis = method()
recessionBasis Polyhedron := P -> columns rays tailCone P

collapseMap = method()
-- collapse along a recession basis
-- Assumes basis is nonempty, because othewise it can't possibly know the size of the identity matrix.
collapseMap List := rbasis ->
(
    d := rank target first rbasis;
    idMat := entries identityMatrix d;
    rb := apply( rbasis, x -> first entries transpose x );
    matrix select( idMat, v -> not member( v, rb ) )    
)
-- collapse along recession basis of a polyhedron
collapseMap Polyhedron := P -> 
(
    rbasis := recessionBasis P;
    if rbasis == {} then identityMatrix ambDim P else collapseMap rbasis
) 
-- collapseMap(A,u) returns the matrix of the collapsing map along mf(A,u).
-- u is a column matrix
collapseMap ( Matrix, Matrix ) := ( A, u ) -> collapseMap minimalFace( A, u )

-- collapse(A,u) returns the collapse of matrix A along mf(A,u)
-- u is a column matrix.
collapse = method()
collapse ( Matrix, Matrix ) := ( A, u ) -> collapseMap( A, u ) * A
collapse MonomialPair := ( cacheValue symbol collapse )( pair -> 
    collapseMap( pair#matrix#matrix, pair#point ) * pair#matrix#matrix )
-- the collapse of a polyhedron along its own recession basis
collapse Polyhedron := ( cacheValue symbol collapse )( P -> affineImage( collapseMap P, P ) )
collapse ( Matrix, Polyhedron ) := ( A, P ) -> collapseMap( P ) * A
        
-- a special point
specialPoint = method()
specialPoint MonomialPair := ( cacheValue symbol specialPoint )( P ->
(
    -- First, get the feasible region of the linear program P(A,u), that is, 
    -- the polyhedron consisting of nonnegative points x in the domain of A 
    -- such that Ax <= u.
    A := P#matrix#matrix;
    u := P#point;
    n := rank source A;
    M := A || - identityMatrix n; 
    v := u || zeroVector( n );
    feasibleRegion := polyhedronFromHData( M, v );
    -- Now, the optimal set:
    optimalSet := maxFace( transpose matrix { constantList( 1, rank source A ) }, feasibleRegion );
    -- an interior point of the optimal set is a special point:
    interiorPoint optimalSet
))
specialPoint ( Matrix, Matrix ) := ( A, u ) -> specialPoint monomialPair ( A, u )

isSmall = method()
isSmall MonomialPair := ( cacheValue symbol isSmall )( pair ->
(
    u := pair#point;
    cols := columns pair#matrix#matrix;
    not any( cols, a -> all( first entries transpose( u - a ), x -> x > 0 ) ) 
))

isVerySmall = method()
isVerySmall MonomialPair := ( cacheValue symbol isVerySmall )( pair -> degree( pair ) <= 1 )

isSmallNotVerySmall = method()
isSmallNotVerySmall MonomialPair := pair -> isSmall( pair) and not isVerySmall( pair )

pointsAimedAtInteriorOfCompactFace := L -> 
(
    O := constantVector( 0, ambDim L );
    P := convexHull { O, L };
    join( interiorLatticePoints P, interiorLatticePoints L )
)

pointsAimedAtCompactFace := L -> 
(
    O := constantVector( 0, ambDim L );
    P := convexHull { O, L };
    pts := latticePoints P;
    -- select positive points
    select( pts, u -> all( first entries transpose u, x -> x > 0 ) )
)

-- the preimage of a collapsed point
liftPoint := ( u, rbasis ) ->
(
    n := rank target first rbasis; -- ambient dimension
    rbPerp := select( standardBasis n, x -> not member( x, rbasis ) );
    -- lift u inserting zeros in coordinates corresponding to basis vectors in rbasis
    v := sum( first entries transpose u, rbPerp, ( i, j ) -> i * j );
    convexHull( { v } ) + coneFromVData( rbasis )
)

-- u is a point collapsed along face F
minimalLifts := ( u, F ) ->
(
    rbasis := recessionBasis F;
    n := ambDim F;
    P := intersection( liftPoint( u, rbasis ), convexHull( { constantVector( 0, n ), F } ) );
    eqns := hyperplanes P;
    ineqs := halfspaces P;
    numEqns := rank target first eqns;
    numIneqs := rank target first ineqs;
    -- build matrix, rhs, and relations
    mat := eqns#0 || ineqs#0;
    rhs := eqns#1 || ineqs#1;
    rel := "1 " | toString( numEqns + numIneqs );
    scan( numEqns, x -> rel = rel | " =" );
    scan( numIneqs, x -> rel = rel | " <" );
    file := getFilename();
    -- store matrix
    MAT := openOut( file | ".mat" );
    putMatrix( MAT, mat );
    close MAT;
    -- store rhs 
    RHS := openOut( file | ".rhs" );
    putMatrix( RHS, transpose rhs );
    close RHS;
    -- store relations
    REL := openOut( file | ".rel" );
    REL << rel;
    close REL;
    -- run 4ti2
    runProgram( fourTiTwo, "zsolve", "--quiet --precision=64 " | rootPath | file );
    sol := getMatrix( file | ".zinhom" );
    columns transpose sol
)

mf := ( u, L ) -> smallestFace( vertices intersection( coneFromVData u, L ), L )

pointsAimedAtUnboundedFace := L -> 
(
    collapsedPoints := pointsAimedAtInteriorOfCompactFace collapse L;
    pts = flatten apply( collapsedPoints, u -> minimalLifts( u, L ) );
    local v;
    local directions;
    rbasis := recessionBasis L;
    pts = flatten apply( pts, u -> 
        (
            if mf( u, L ) == L then u
            else 
            (
                directions = delete( {}, subsets rbasis);
                directions = select( directions, e -> 
                    (
                        v = u + sum e;
                        mf( v, L ) == L
                    )
                );
                minimalPoints apply( directions, e -> u + sum e )
            )
        )
    ); 
    pts
)

pointsAimedAtFace = method()
pointsAimedAtFace Polyhedron := L -> 
    if isCompact L then pointsAimedAtCompactFace L else pointsAimedAtUnboundedFace L

gatherPoints = method()
gatherPoints MonomialMatrix := ( cacheValue symbol points )( M ->
(
    N := newtonPolyhedon M;
    -- pick only maximal compact faces and unbounded standard faces
    faces := join( maximalBoundedFaces N, unboundedFaces N);    
    unique flatten( pointsAimedAtFace \ faces )
))

minimalSmallNotVerySmall = method()
minimalSmallNotVerySmall MonomialMatrix := ( cacheValue symbol minimalSmallNotVerySmall )( M ->
(
    A := M#matrix;
    P := convexHull( A ) + hypercube( numRows A, 0, 2 );
    -- select positive lattice points
    pts := select( latticePoints P, u -> all( first entries transpose u, x -> x > 0 ) );
    minimalPoints select( pts, u -> isSmallNotVerySmall monomialPair( A, u ) ) 
))

--------------------------------------------
-- Integer Programs
--------------------------------------------

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
integerProgram = memoize integerProgram

-- returns the value of an integer program, along with an optimal point
solveIP := ( cacheValue symbol solveIP )( IP ->
(
    ( m, n ) := IP#"dim";
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
    runProgram( fourTiTwo, "minimize", "--quiet --precision=64 " | rootPath | file );
    opt := getMatrix( file | ".min" );
    value := first first entries (opt*( IP#"weights" || zeroVector( m ) ) );
    -- will also return an optimal point
    optPt := transpose( opt * ( identityMatrix( n ) || zeroMatrix( m, n ) ) );
    ( value, optPt )
))    

valueIP := IP -> first solveIP IP

optPtIP := IP -> last solveIP IP

-- this just sets up the integer program Theta
theta := ( A, u, s, q ) -> (
    Abar := collapse( A, u );
    m := numRows Abar;
    n := rank source Abar;
    rhs := Abar*bracket( s, q ) - constantVector( 1, m );
    signs := columnVector apply(n, i -> if s_0_i == 0 then 1 else 0 );
    weights := constantVector( 1, n );
    integerProgram( Abar, rhs, weights, signs )
)

-- returns the universal deficit and shortfall
deficitAndShortfall = method()
deficitAndShortfall ( MonomialPair, ZZ ) := ( P, q ) -> 
(
    dsInternal := ( cacheValue ( symbol deficitAndShortfall, q ) )( pair -> (
    A := pair#matrix#matrix;
    u := pair#point;
    s := specialPoint pair;
    sq := bracket( s, q );
    Abar := collapse pair;
    Asq := Abar * sq;
    m := numRows Abar;
    n := rank source Abar;
    val := first solveIP theta( A, u, s, q );
    eqsMat := (Abar | -identityMatrix m) || (zeroMatrix( m, n ) | identityMatrix m);    
    eqsMat = eqsMat || matrix { join( constantList( 1, n ), constantList( 0, m ) ) };
    eqsRHS := constantVector( 0, m ) || Asq - constantVector( 1, m ) || columnVector { val };
    rel := "1 " | toString( 2*m + 1 ) | "\n";
    scan( m, i -> rel = rel | "= " );
    scan( m, i -> rel = rel | "< " );
    rel = rel | "=";
    sign := "1 " | toString( m + n ) | "\n";
    scan( n, i -> sign = sign | toString( if s_0_i == 0 then 1 else 0 ) | " ");
    scan( m, i -> sign = sign | "0 " );
    file := getFilename();
    -- store the augmented matrix
    M := openOut( file | ".mat" );
    putMatrix( M, eqsMat );
    close M;
    RHS := openOut( file | ".rhs" );
    putMatrix( RHS, transpose eqsRHS );
    close RHS; 
    Signs := openOut( file | ".sign" );
    Signs << sign;
    close Signs;
    Rels := openOut( file | ".rel" );
    Rels << rel;
    close Rels;
    -- run 4ti2
    runProgram( fourTiTwo, "zsolve", "--quiet --precision=64 " | rootPath | file);
    -- process image
    im := getMatrix( file | ".zinhom" );
    im = apply( entries im, x -> columnVector x ); 
    proj := zeroMatrix( m, n ) | identityMatrix( m );
    im  = apply( im, v -> proj * v );
    ( sum( first entries transpose sq ) - val, apply( im, v -> Asq - v ) )
    ));
    dsInternal P
)
deficitAndShortfall ( Matrix, Matrix, ZZ ) := ( A, u, q ) -> 
    deficitAndShortfall( monomialPair( A, u ), q )

deficit := method()
deficit ( MonomialPair, ZZ ) := ( pair, q ) -> first deficitAndShortfall( pair, q )
deficit ( Matrix, Matrix, ZZ ) := ( A, u, q ) -> deficit( monomialPair( A, u ), q )

shortfall := method()
shortfall ( MonomialPair, ZZ ) := ( pair, q ) -> last deficitAndShortfall( pair, q )
shortfall ( Matrix, Matrix, ZZ ) := ( A, u, q ) -> shortfall( monomialPair( A, u ), q )
    
----------------------------------------------------------------------------------
-- mus, crits, and Frobenius powers
----------------------------------------------------------------------------------

-- Rings needed to create the outputs (generating function for mus, crits)
R1 := memoize ( () -> QQ( monoid[ getSymbol "p", getSymbol "t" ] ) );
R2 := memoize ( () -> QQ[ ( ( R1() )_* )#0, MonomialOrder => Lex, Inverses => true ] )

frobeniusMu = method()
frobeniusMu ( MonomialPair, ZZ ) := ( P, r ) ->
(   muInternal := ( cacheValue ( symbol frobeniusMu, r ) )( pair -> (
    ( p, t ) := toSequence ( R1() )_*;
    S := { set{}, set{ pair } };
    SStar := S;
    e := 1;
    M := { 0, degree( pair ) * p - deficit( pair, r ) };
    local newS;
    local newSStar;
    local k;
    local epsilon;
    local delta;
    while true do 
    (
        e = e + 1;
        newS = apply( toList SStar#(e-1), pp -> apply( shortfall( pp, r ), v -> monomialPair( collapse pp, v ) ) );
        newS = unique flatten newS;
        if ( k = position( S, x -> x === set newS ) ) =!= null then ( -- print(k,e); 
            return sum( 1..(k-1), i -> M_i * t^i ) / ( 1 - p*t ) + sum( k..(e-1), i -> M_i * t^i ) / ( ( 1 - p*t ) * ( 1 - t^(e-k) ) ) ); 
        ( epsilon, newSStar ) = maximize( newS, v -> degree v );
        if epsilon > 1 then ( -- print(e); 
           return sum( 1..(e-1), i -> M_i * t^i ) / ( 1 - p*t ) + ( p - 1 ) * t^e / ( ( 1 - p*t ) * ( 1 - t ) ) ); 
        ( delta, newSStar ) = minimize( newSStar, pp -> deficit( pp, r ) );
        S = append( S, set newS );
        SStar = append( SStar, set newSStar );
        M = append( M, epsilon * p - delta )
    )
    ));
    muInternal P
)
frobeniusMu ( Matrix, Matrix, ZZ ) := ( A, u, r ) -> frobeniusMu( monomialPair( A, u ), r )

-- TODO: adapt to work with MonomialPair; cache value
criticalExponent = method()
criticalExponent ( MonomialPair, ZZ ) := ( pp, r ) -> 
(
    critInternal := ( cacheValue ( symbol criticalExponent, r ) )( pair -> (
    G := frobeniusMu( pair, r );
    (p,t) := toSequence (R1())_*;
    G = G * ( 1 - p*t );
    G = sub( numerator G, t => 1/p ) / sub( denominator G, t => 1/p );
    f = sub( numerator G, R2() );
    g = sub( denominator G, R2() );
    f * g^(-1)
    ));
    critInternal pp
)
criticalExponent ( Matrix, Matrix, ZZ ) := ( A, u, r ) -> criticalExponent( monomialPair( A, u ), r )

criticalExponents = method( Options => { Verbose => false, ReturnPoints => false } )
criticalExponents ( MonomialMatrix, ZZ ) := o -> ( M, r ) -> 
(  
    pts := gatherPoints M;
    local crit;
    local ptsRealizingC;
    ptsAndCrits := apply( pts, u -> 
        ( 
            crit = criticalExponent( monomialPair( M, u), r );
            if o.Verbose then print toString ( first entries transpose u, crit );
            { u, crit }
        )
    );
    -- Take all distinct crits and sort them
    allcrits := unique apply( ptsAndCrits, last );
    minOrder := min( ord \ allcrits );
    p := first (R2())_*;
    allcrits =  last \ sort apply( allcrits, c -> 
        append( apply( 0..(-minOrder), i -> coefficient( p^(-i), c ) ) , c ) 
    );
    if not o.ReturnPoints then return allcrits;
    allcrits = apply( allcrits, c -> 
        (
            ptsRealizingC = select( ptsAndCrits, u -> u#1 == c );
            ptsRealizingC = apply( ptsRealizingC, first );
            { c, ptsRealizingC }
        )
    );
    -- Gathering small but not very small points.
    -- These should be listed as points realizing crit exp 1
    smallNotVerySmall := minimalSmallNotVerySmall M; 
    lastCrit := last allcrits;
    if lastCrit#0 == 1_(R2()) then 
        -- if 1 is already in crit list, add small not very small points to its list
        append( drop( allcrits, { #allcrits - 1, #allcrits - 1 } ), { 1_(R2()), join( lastCrit#1, smallNotVerySmall ) } )
    else 
        -- if not, add one more entry to crits
        append( allcrits, { 1_(R2()), smallNotVerySmall } )
)
criticalExponents ( Matrix, ZZ ) := o -> ( A, r ) -> 
    criticalExponents( monomialMatrix A, r, o )
 
frobeniusPowers = method( Options => { Verbose => false } )
frobeniusPowers ( MonomialMatrix, ZZ, List ) := o -> ( A, r, variables ) ->
(
    crits := criticalExponents( A, r, o, ReturnPoints => true );
    I := ideal 0_( ring variables#0 );
    skewedList :=apply( reverse crits, 
         c -> { c#0, I = trim (I + makeIdeal( variables, c#1 )) } );
    u := first transpose skewedList;
    v := last transpose skewedList;
    answer := reverse transpose( { drop( u, { 0, 0 } ), drop( v, { #v - 1, #v - 1 } ) } );
    apply( answer, u -> u#0 => u#1 )
)
frobeniusPowers ( Matrix, ZZ, List ) := o -> ( A, r, var ) -> 
    frobeniusPowers( monomialMatrix A, r, var, o )

-------------------------------------------------

