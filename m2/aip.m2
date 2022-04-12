loadPackage("Polyhedra", Reload => true)

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

MonomialMatrix = new Type of HashTable

monomialMatrix = method()
monomialMatrix Matrix := A -> new MonomialMatrix from {matrix => A, cache => new CacheTable}
monomialMatrix List := A -> monomialMatrix matrix A
monomialMatrix = memoize monomialMatrix
-- If monomialMatrix is called multiple times with the same matrix, memoize
-- will prevent the creation of a copy, therefore keeping the cached values

MonomialPair = new Type of HashTable

monomialPair = method()
monomialPair ( MonomialMatrix, Matrix ) := ( A, u ) -> 
   new MonomialPair from {matrix => A, (symbol point) => u, cache => new CacheTable}
monomialPair ( Matrix, Matrix ) := ( A, u ) -> monomialPair( monomialMatrix A, u )
monomialPair ( List, List ) := ( A, u ) -> monomialPair( monomialMatrix A, transpose matrix {u} )
monomialPair = memoize monomialPair
-- If monomialPair is called multiple times with the same pair, memoize
-- will prevent the creation of a copy, therefore keeping the cached values

-------------------------------------------------------------------------------
-- Auxiliary Functions
-------------------------------------------------------------------------------

-- constantList(c,n) returns a list with n copies of c
constantList := (c,n) -> apply( n, x -> c )

-- identityMatrix(n) returns the nxn identity matrix
identityMatrix := n -> id_(ZZ^n)

-- If L is a list of rational numbers, denominator(L) returns a
-- common denominator D for all members of L, while numerator(L) 
-- returns a list with the numerators, once all entries are written
-- with denominator D. 
-- In other words, L = numerator(L)/denominator(L).
denominator List := L -> lcm apply( L, denominator )
numerator List := L -> denominator( L ) * L

-- posRes(a,d) returns the least positive residue of a modulo D.
-- If the first entry is a list, this operation is carried out in a 
-- componentwise fashion.
posRes = method()
posRes ( ZZ, ZZ ) := ( a, d ) -> 
(
    residue := a % d;
    if residue == 0 then d else residue
)
posRes ( List, ZZ ) := ( L, d ) -> apply( L, x -> posRes( x, d ) )

-- If t = a/b is a rational number, and q is an integer, then 
-- bracket(t,q) = posRes(aq,b)/b (or 0, if t is 0).
-- This operation extends to lists and matrices, in a 
-- componentwise fashion.
bracket = method()
bracket ( QQ, ZZ ) := ( t, q ) -> 
(
    if t == 0 then 0
    else
    (
        a := numerator t;
        b := denominator t;
        posRes( a*q, b )/b
    )
)
bracket ( ZZ, ZZ ) := ( t, q ) -> bracket( t/1, q )
bracket ( List, ZZ ) := ( L, q ) -> apply( L, t -> bracket( t, q ) )
bracket ( Matrix, ZZ ) := ( M, q ) -> matrix apply( entries M, t -> bracket( t, q ) )

--pointsToMatrix gathers mx1 matrices into a big matrix
pointsToMatrix := L -> fold( ( x, y ) -> x | y, L )

--columns returns the columns of a matrix in a list 
columns := M -> apply( rank source M, i -> M_{i} )

-- -- canVec(n,i) returns the (i+1)-th canonical basis vector of ZZ^n.
-- canVec := (n,i) -> apply( n, j -> if i == j then 1 else 0 )

stdBasis := n -> columns identityMatrix n

-- all sums of standard basis vectors
cube := m -> 
(    
    L := select( columns vertices hypercube( m, 0, 1 ), x -> x != 0 );
    apply( L, u -> lift( u, ZZ ) )
)

-- -- randomMatrix(m,n,max) returns a random mxn matrix with integer entries in [0,max).
-- randomMatrix := (m,n,maximum) -> matrix apply( m, i -> apply( n, j -> random(maximum) ) )

-- conVec(u) transforms a one-dimensional list u into a column vector
colVec := u -> transpose matrix {u}

-- constantMatrix(c,m,n) generates an mxn matrix whose entries all equal c. 
constantMatrix := ( c, m, n ) -> matrix toList apply( m, i -> toList apply( n, x -> c ) )

-- constantVector(c,m) generates an m dimensional column vector whose entries all equal c. 
constantVector := ( c, m ) -> constantMatrix( c, m, 1 )

-- zeroMatrix(m,n) returns the mxn zero matrix.
zeroMatrix := ( m, n ) -> constantMatrix( 0, m, n )

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
    )    
    do filename = temporaryFileName();
    filename
)

-- selects the minimal elements of a list L of sets
minimalSets := L -> 
(
    select( L, A -> select( L, B -> isSubset( B, A ) ) == { A } )
)

matrixToIdeal = method()
matrixToIdeal Matrix := A -> 
(
    m := rank target A;
    X := getSymbol "X";
    R := QQ(monoid[X_1..X_m]);
    monomialIdeal ideal apply( columns A, u -> 
        product( R_*, first entries transpose u, ( x, i ) -> x^i )
    )  
) 
matrixToIdeal ( Matrix, Ring ) := ( A, R ) -> 
(
    monomialIdeal ideal apply( columns A, u -> 
        product( R_*, first entries transpose u, ( x, i ) -> x^i )
    )  
) 

idealToMatrix := I -> transpose matrix apply( I_*, m -> first exponents m )

-- builds a monomial from a list of variables and a list (or column matrix) of exponents
makeMonomial = method()
makeMonomial ( List, List ) := ( variables, exps ) -> product( variables, exps, (x,a) -> x^a )  
makeMonomial ( List, Matrix ) := ( v, e ) -> makeMonomial( v, first entries transpose e )

-- Given a list of points u, will create the ideal generated by x^(u-1)
makeIdeal := ( variables, L ) -> 
    ideal apply( L,  u -> makeMonomial( variables, u - constantVector( 1, #variables ) ) )

-- the order of a Laurent polynomial
ord := f -> min( first \ degree \ terms f ) 

integralClosure MonomialIdeal := o -> I -> 
(
    R := ring I;
    A := idealToMatrix I;
    m := numRows A;
    P := convexHull( A ) + hypercube( m, 0, 1 );
    trim matrixToIdeal( pointsToMatrix latticePoints P, R )
)    

-- given list of points, returns the minimal ones
minimalPoints := L -> columns idealToMatrix trim matrixToIdeal pointsToMatrix L

-------------------------------------------------------------------------------
-- Polyhedral Stuff
-------------------------------------------------------------------------------

-- newton(A) returns the newton polyhedron of a matrix A.
newton = method()
newton MonomialMatrix := ( cacheValue symbol newton )( A -> 
    convexHull( A#matrix ) + posOrthant( rank target A#matrix ) 
)
newton Matrix := A -> newton monomialMatrix A

-- univDenon(A) returns a universal denominator for the matrix A.
univDenom = method()
univDenom MonomialMatrix := ( cacheValue symbol univDenom )( M ->
(
    A := M#matrix;    
    n := rank source A;
    m := rank target A;
    I := identityMatrix n;
    B := A || -A || I || -I;
    allMinors := ( minors( n, B ) )_*;
    ( m-1 )*( lcm allMinors )
))
univDenom Matrix := A -> univDenom monomialMatrix A

-- properFaces(P) returns a list of all proper faces of the polyhedron P.
properFaces = method() 
properFaces Polyhedron := ( cacheValue symbol properFaces )( P -> 
    flatten toList apply( 1..( dim P ), i -> facesAsPolyhedra( i, P ) )
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
    lcm ( minors( d, A ) )_*
)

univDenom2 = method()
univDenom2 Matrix := A ->
(
    local rbasis;
    faces := properFaces newton A;
    matrices := apply( faces, F -> 
        (
            rbasis = recessionBasis F;
            if rbasis == {} then selectColumnsInFace( A, F ) 
            else selectColumnsInFace( A, F ) | pointsToMatrix rbasis
        )
    );
    ( numRows( A ) - 1 )*lcm apply( matrices, M -> lcmMinors M )
) 

-- ft(A,u) returns the F-threshold of the monomial pair (A,u), that is, the unique 
-- scalar lambda such that u/lambda lies in the boudary of the Newton polyhedron of A.
-- u can be a column matrix or a list.
ft = method()
ft MonomialPair := ( cacheValue symbol ft )( P ->
(
    N := newton P#matrix;
    u := P#point;
    -- the intersection point of the ray spanned by u and the newton polyhedron of A:
    intPt := first entries vertices intersection( coneFromVData u, N );
    u_(0,0)/intPt#0
))
ft ( Matrix, Matrix ) := ( A, u ) -> ft monomialPair( A, u ) 
ft ( List, List ) := ( A, u ) -> ft monomialPair( A, u ) 

-- minimalFace(A,u) returns the minimal face mf(A,u), that is, the smallest
-- face of the Newton polyhedron of A containing the scaled point u/ft(A,u).
-- u can be a column matrix or plain list.
minimalFace = method()
minimalFace MonomialPair := ( cacheValue symbol minimalFace )( P ->
(
    N := newton P#matrix;
    u := P#point;
    int := intersection( coneFromVData u, N );
    smallestFace( vertices int, N )
))
minimalFace ( Matrix, Matrix ) := ( A, u ) -> minimalFace monomialPair( A, u ) 
minimalFace ( List, List ) := ( A, u ) -> minimalFace monomialPair( A, u ) 

-- recession basis for minimal face or polyhedron
-- returns list of points (expressed as column matrices)     
recessionBasis = method()
-- recessionBasis MonomialPair := ( cacheValue symbol recessionBasis )( P -> 
--     columns rays tailCone minimalFace P )
-- recessionBasis ( Matrix, Matrix ) := ( A, u ) -> recessionBasis monomialPair( A, u )
-- recessionBasis ( List, List ) := ( A, u ) -> recessionBasis monomialPair( A, u )
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
-- u can be a column matrix or plain list; if not provided, assumed to be {1,...,1}.
collapseMap (Matrix, Matrix) := (A,u) -> collapseMap minimalFace(A,u)
collapseMap (Matrix,List) := (A,u) -> collapseMap(A,colVec u)
collapseMap Matrix := A -> collapseMap( A, constantVector( 1, rank target A ) )

-- collapse(A,u) returns the collapse of matrix A along mf(A,u)
-- u can be a column matrix or plain list; if not provided, assumed to be {1,...,1}.
collapse = method()
collapse (Matrix,Matrix) := (A,u) -> collapseMap(A,u)*A
collapse (Matrix,List) := (A,u) -> collase(A, colVec u)
collapse Matrix := A -> collapseMap(A)*A
-- the collapse of a polyhedron along its own recession basis
collapse Polyhedron := P -> affineImage( collapseMap P, P )
collapse (Matrix,Polyhedron) := (A,P) -> collapseMap(P)*A

-- -- feasLP of a pair (A,u) returns the polyhedron consisting of all nonnegative points x
-- -- in the domain of A such that Ax<=u (i.e., the feasible region of the linear 
-- -- program P(A,u)). 
-- feasLP = method() 
-- feasLP MonomialPair := P -> 
-- (
--     A := P#matrix#matrix;
--     u := P#point;
--     n := rank source A;
--     M := A || - identityMatrix n; 
--     v := u || colVec constantList( 0, n );
--     polyhedronFromHData( M, v )
-- )
-- feasLP ( Matrix, Matrix ) := ( A, u ) -> feasLP monomialPair( A, u )
-- feasLP ( List, List ) := ( A, u ) -> feasLP monomialPair( A, u )

-- -- optLP of a pair (a,u) returns the the optimal set for the linear program P(A,u).
-- optLP = method()
-- optLP MonomialPair := ( cacheValue symbol optLP )( P -> 
-- (   A := P#matrix#matrix;
--     u := P#point;
--     maxFace( transpose matrix { constantList( 1, rank source A) }, feasLP(A, u) )
-- ))
-- optLP ( Matrix, Matrix ) := ( A, u ) -> optLP monomialPair( A, u )
-- optLP ( List, List ) := ( A, u ) -> optLP monomialPair( A, u )
        
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
    v := u || colVec constantList( 0, n );
    feasibleRegion := polyhedronFromHData( M, v );
    -- Now, the optimal set:
    optimalSet := maxFace( transpose matrix { constantList( 1, rank source A) }, feasibleRegion );
    -- an interior point of the optimal set is a special point:
    interiorPoint optimalSet
))
specialPoint ( Matrix, Matrix ) := ( A, u ) -> specialPoint monomialPair ( A, u )
specialPoint ( List, List ) := ( A, u ) -> specialPoint monomialPair ( A, u )

isStandard = method()
isStandard Polyhedron := ( cacheValue symbol isStandard )( P -> 
(
    n := ambDim P;
    I := identityMatrix n;
    coordSpaces := apply(n, j -> coneFromVData transpose matrix drop(entries I,{j,j}));
    not any(coordSpaces, S -> contains(S,P))
))

properStandardFaces = method()
properStandardFaces Polyhedron := ( cacheValue symbol properStandardFaces )( P -> 
    select( properFaces P, isStandard )
)

pointsAimedAtCompactFace := L -> 
(
    O := constantVector( 0, ambDim L );
    P := convexHull({ O, L });
    join( interiorLatticePoints P, interiorLatticePoints L )
)

-- the preimage of a collapsed point
liftPoint := (u,rbasis) ->
(
    n := rank target first rbasis; -- ambient dimension
    rbPerp := select( stdBasis n, x -> not member(x,rbasis) );
    -- lift u inserting zeros in coordinates corresponding to basis vectors in rbasis
    v := sum( first entries transpose u, rbPerp, (i,j) -> i*j );
    convexHull( {v} ) + coneFromVData( rbasis )
)

-- u is a point collapsed along face F
minimalLifts := (u,F) ->
(
    rbasis := recessionBasis F;
    n := ambDim F;
    P := intersection( liftPoint( u, rbasis ), convexHull( { constantVector(0,n), F } ) );
    eqns := hyperplanes P;
    ineqs := halfspaces P;
    numEqns := rank target first eqns;
    numIneqs := rank target first ineqs;
    -- build matrix, rhs, and relations
    mat := eqns#0 || ineqs#0;
    rhs := eqns#1 || ineqs#1;
    rel := "1 " | toString(numEqns+numIneqs);
    scan(numEqns, x -> rel = rel | " =");
    scan(numIneqs, x -> rel = rel | " <");
--    path242 := prefixDirectory | currentLayout#"programs";
    path242 := "/usr/local/bin/";
    file := getFilename();
    -- store matrix
    MAT := openOut( file | ".mat");
    putMatrix( MAT, mat );
    close MAT;
    -- store rhs 
    RHS := openOut( file | ".rhs");
    putMatrix( RHS, transpose rhs );
    close RHS;
    -- store relations
    REL := openOut( file | ".rel");
    REL << rel;
    close REL;
    -- run 4ti2
    execstr := path242 | "zsolve --quiet " | rootPath | file;
    ret := run execstr;
    if ret =!= 0 then error "minimalLifts: error occurred while executing external program 4ti2/zsolve";
    sol := getMatrix( file | ".zinhom" );
    columns transpose sol
)

mf := (u,L) -> smallestFace( vertices intersection( coneFromVData u, L ), L )

pointsAimedAtUnboundedFace := L -> 
(
    collapsedPoints := pointsAimedAtCompactFace collapse L;
    pts = flatten apply( collapsedPoints, u -> minimalLifts(u,L) );
    local v;
    local directions;
    rbasis := recessionBasis L;
    -- print("Original minimal lifts");
    -- print pts;
    pts = flatten apply( pts, u -> 
        (
            if mf( u, L ) == L then u
            else 
            (
--                print("Problem point", u, "Intersection with face", vertices int);
                directions = delete( {}, subsets rbasis);
                directions = select( directions, e -> 
                    (
                        v = u + sum e;
                        mf( v, L ) == L
                    )
                );
--                print("Directions we can go", apply( directions, e -> fold( plus, e ) ));
                directions = minimalSets directions;
--                print("Minimal directions we can go", apply( directions, e -> fold( plus, e ) ));
                apply( directions, e -> u + sum e )
            )
            -- apply( rbasis, e ->
            --     ( 
            --         print("Trying to move in direction ", e);
            --         int = intersection( coneFromVData(u + e), L );
            --         print("Is the intersection of ray with L empty? ", int == emptyPolyhedron(ambDim L) );
            --         mf = smallestFace( vertices int, L );
            --         print("Is the min face of u+e the face equal L? ", mf == L)
            --     )
            -- )             
        )
    ); 
    -- print("Here are the points", pts);
    -- print("Now let's see if they all work");
--    print apply( pts, u -> mf( u, L ) == L ); 
    pts
)

pointsAimedAtFace := L -> 
    if isCompact L then pointsAimedAtCompactFace L else pointsAimedAtUnboundedFace L

-- Feasible region of the auxiliary integer program Theta;
-- not used in code below
-- consTheta = (A,u,s,q) -> (
--     n := rank source A;
--     d := rank target A;
--     nonnegConstraints := apply(select(n, i -> s#i == 0), i -> -canVec(n,i));
--     nonnegConstraintsRHS := apply(select(n, i -> s#i == 0), i -> 0);
--     B := collapse(A,u);
--     otherConstraints := B || matrix {constantList(-1,n)};  
--     otherConstraintsRHS := B*(transpose matrix {bracket(s,q)}) || matrix {{0}};
--     constraints := if nonnegConstraints === {} then otherConstraints else matrix nonnegConstraints | otherConstraints;
--     constraintsRHS := if nonnegConstraints === {} then otherConstraintsRHS else matrix nonnegConstraintsRHS | otherConstraintsRHS;
--     print( constraints | constraintsRHS );
--     polyhedronFromHData( constraints, constraintsRHS )
-- )

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

-- MAKE THIS A METHOD THAT USES cacheValue     
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

--- Probably useless, since we cache results
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
uData := (A,u,q) -> 
(
    s := specialPoint(A,u);
    sq := bracket(s,q);
    Abar := collapse(A,u);
    Asq := Abar*sq;
    m := numRows Abar;
    n := rank source Abar;
    val := first solveIP theta(A,u,s,q);
    eqsMat := (Abar | -identityMatrix m) || (zeroMatrix(m,n) | identityMatrix m);    
    eqsMat = eqsMat || matrix { join( constantList( 1, n ), constantList( 0, m ) ) };
    eqsRHS := constantVector( 0, m ) || Asq - constantVector(1,m) || colVec {val};
    rel := "1 " | toString(2*m+1) | "\n";
    scan(m,i->rel=rel|"= ");
    scan(m,i->rel=rel|"< ");
    rel = rel | "=";
    sign := "1 " | toString(m+n) | "\n";
    scan(n, i-> sign = sign | toString( if s_0_i == 0 then 1 else 0 ) | " ");
    scan(m, i-> sign = sign | "0 ");
    --    path242 := prefixDirectory | currentLayout#"programs";
    path242 := "/usr/local/bin/";
    file := getFilename();
    -- store the augmented matrix
    M := openOut( file | ".mat");
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
    execstr := path242 | "zsolve --quiet --precision=64 " | rootPath | file;
    ret := run execstr;
    if ret =!= 0 then error "solveIP: error occurred while executing external program 4ti2/zsolve";
    -- process image
    im := getMatrix( file | ".zinhom" );
    im = apply( entries im, x -> colVec x ); 
    proj := zeroMatrix(m,n) | identityMatrix(m);
    im  = apply( im, v -> proj*v );
    ( sum(first entries transpose sq) - val, apply(im, v -> Asq - v ) )
)

-- -- returns the universal deficit and shortfall
-- -- TO DO: need to check that points in the shortfall really come from integral optimal points.
-- uData := (A,u,q) -> 
-- (
--     s := specialPoint(A,u);
--     sq := bracket(s,q);
--     Abar := collapse(A,u);
--     Asq := Abar*sq;
--     m := numRows Abar;
--     n := rank source Abar;
--     val := first solveIP theta(A,u,s,q);
--     eqsMat := Abar | -identityMatrix m;
--     eqsMat = eqsMat || matrix { join( constantList( 1, n ), constantList( 0, m ) ) };
--     eqsRHS := colVec append( constantList( 0, m ), val );
--     nonnegConstraints := apply(select(n, i -> s_0_i == 0), i -> - canVec(m+n,i));
--     nonnegConstraintsRHS := apply(select(n, i -> s_0_i == 0), i -> 0);
--     otherConstraints := Abar | zeroMatrix(m,m);
--     otherConstraintsRHS := Asq - constantVector(1,m);
--     ineqsMat := if nonnegConstraints === {} then otherConstraints else matrix nonnegConstraints || otherConstraints;
-- --    print(nonnegConstraints);
-- --    print(nonnegConstraintsRHS);
-- --    print(otherConstraints);
-- --    print(otherConstraintsRHS);
-- --    print(matrix { nonnegConstraintsRHS });
--     ineqsRHS := if nonnegConstraintsRHS === {} then otherConstraintsRHS else (colVec nonnegConstraintsRHS) || otherConstraintsRHS;
--     polyh := polyhedronFromHData( ineqsMat, ineqsRHS, eqsMat, eqsRHS );
--     proj := zeroMatrix(m,n) | identityMatrix(m);
--     im := if isCompact polyh then apply(latticePoints polyh, v -> proj*v ) else latticePoints affineImage(proj,polyh);
--     -- the else above is wrong; that set may properly contain the image.
--     ( sum(first entries transpose sq) - val, apply(im, v -> Asq - v ) )
-- )

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

maximize := (L,f) ->
(
    vals := apply(L,f);
    maximum := max vals;
    ( maximum, L_(positions(vals, x -> x == maximum )) )
)

minimize := (L,f) ->
(
    vals := apply(L,f);
    minimum := min vals;
    (minimum, L_(positions(vals, x -> x == minimum )) )
)

----------------------------------------------------------------------------------
-- mu and crit
----------------------------------------------------------------------------------

R1 := memoize ( () -> QQ(monoid[getSymbol "p",getSymbol "t"]) );
R2 := memoize ( () -> QQ[((R1())_*)#0, MonomialOrder => Lex, Inverses => true ] )

mu := ( A, u, p0 ) ->
(
--    R := QQ(monoid[getSymbol "p",getSymbol "t"]);
    (p,t) := toSequence (R1())_*;
    localUShort := memoize uShort;
    localUDeficit := memoize uDeficit;
    localFt := memoize ft;
    localCollapse := memoize collapse;
    S := { set{}, set{(A,u)} };
    SStar := S;
    e := 1;
    M := { 0, localFt(A,u)*p - localUDeficit(A,u,p0) };
    local newS;
    local newSStar;
    local k;
    local epsilon;
    local delta;
    while true do 
    (
        e = e + 1;
        newS = apply( toList SStar#(e-1), pair -> apply( localUShort(pair_0,pair_1,p0), v -> ( localCollapse pair, v ) ) );
        newS = unique flatten newS;
        if ( k = position( S, x -> x === set newS ) ) =!= null then 
            return sum(1..(k-1),i -> M_i*t^i)/(1-p*t) + sum(k..(e-1), i -> M_i*t^i )/((1-p*t)*(1-t^(e-k)));
        ( epsilon, newSStar ) = maximize( newS, v -> localFt v );
        if epsilon > 1 then 
           return sum(1..(e-1),i -> M_i*t^i)/(1-p*t) + (p-1)*t^e/((1-p*t)*(1-t));
        ( delta, newSStar ) = minimize( newSStar, pair -> localUDeficit(pair_0,pair_1,p0) );
        S = append( S, set newS);
        SStar = append( SStar, set newSStar );
        M = append( M, epsilon*p - delta )
    )
)
mu = memoize mu

crit := ( A, u, p0 ) -> 
(
    G := mu( A, u, p0 );
--     (p,t) := toSequence (ring numerator G)_*;
    (p,t) := toSequence (R1())_*;
    G = G*(1-p*t);
--    sub(numerator G, t => 1/p)/sub(denominator G, t => 1/p)
    G = sub(numerator G, t => 1/p)/sub(denominator G, t => 1/p);
    f = sub( numerator G, R2() );
    g = sub( denominator G, R2() );
    f*g^(-1)
)
crit = memoize crit

criticalExponents = method( Options => { Verbose => false } )
criticalExponents ( Matrix, ZZ ) := o -> ( A, p0 ) -> 
(
    N := newton A;
    F := properStandardFaces N;
    pts := flatten( pointsAimedAtFace \ F );
    local c;
    local ptsRealizingC;
    ptsAndCrits := apply( pts, u -> 
        ( 
            c = crit( A, u, p0 );
            if o.Verbose then print toString ( first entries transpose u, c );
            { u, c }
        )
    );
    -- Take all distinct crits and sort them
    crits := unique apply( ptsAndCrits, last );
    minOrder := min( ord \ crits );
    p := first (R2())_*;
    crits =  last \ sort apply( crits, c -> 
        append( apply( 0..(-minOrder), i -> coefficient( p^(-i), c ) ) , c ) 
    );
    crits = apply( crits, c -> 
        (
            ptsRealizingC = select( ptsAndCrits, u -> u#1 == c );
            ptsRealizingC = apply( ptsRealizingC, first );
            { c, ptsRealizingC }
        )
    );
    m := numRows A; 
    -- Here, I'm gathering small but not very small points.
    -- These should be listed as points realizing crit exp 1
    aa := matrixToIdeal A;
    ic := integralClosure aa;
    bb := apply( ic_*, m -> transpose matrix exponents m ); -- make points
    -- if a point is not in ri(N), move in every direction that takes to the interior
    bb = flatten apply( bb, u -> 
        if not inInterior(u,N) then 
            select( apply( cube m, e -> u+e ), v -> inInterior( v, N ) ) 
        else u 
    ); 
    bb = minimalPoints bb;
    lastCrit := last crits;
    if lastCrit#0 == 1_(R2()) then 
        -- if 1 as already in crit list, add small not very small points to its list
        crits = append( drop( crits, {#crits - 1,#crits - 1} ), { 1_(R2()), join( lastCrit#1, bb ) } )
    else 
        -- if not, add one more entry to crits
        crits = append( crits, { 1_(R2()), bb } );
    crits
)

frobeniusPowers = method( Options => { Verbose => false } )
frobeniusPowers ( Matrix, ZZ, List ) := o -> ( A, p0, variables ) ->
(
    crits := criticalExponents( A, p0, o );
    print \ crits;
    I := ideal 0_(ring variables#0);
    skewedList :=apply( reverse crits, 
         c -> { c#0, I = trim (I + makeIdeal( variables, c#1 )) } );
    u := first transpose skewedList;
    v := last transpose skewedList;
    answer := reverse transpose( { drop(u,{0,0}), drop(v,{#v - 1, #v - 1}) } );
    apply( answer, u -> u#0 => u#1 )
)

-------------------------------------------------
-- MonomialMatrix:

-- matrix => A
-- cache => {
--     u => {
--              ft => ...
--              mf => ...
--              mu => { p => ... } 
--              crit => {p =>
--                   }
--     v => { p3 => { mu(A,v,p3), crit(A,v,p3), p3 => ...}
-- }

