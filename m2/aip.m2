--installPackage("Polyhedra")

loadPackage("Polyhedra", Reload => true)
-- loadPackage("FrobeniusThresholds")
-- loadPackage("FourTiTwo") -- loaded with Polyhedra

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
numerator List := L -> denominator(L) * L

-- posRes(a,d) returns the least positive residue of a modulo D.
-- If the first entry is a list, this operation is carried out in a 
-- componentwise fashion.
posRes = method()
posRes (ZZ,ZZ) := (a,d) -> (
    residue := a % d;
    if residue == 0 then d else residue
)
posRes (List,ZZ) := (L,d) -> apply(L, x -> posRes(x,d) )

-- If t = a/b is a rational number, and q is an integer, then 
-- bracket(t,q) = posRes(aq,b)/b (or 0, if t is 0).
-- This operation extends to lists and matrices, in a 
-- componentwise fashion.
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

-- canVec(n,i) returns the (i+1)-th canonical basis vector of ZZ^n.
canVec := (n,i) -> apply( n, j -> if i == j then 1 else 0 )

-- randomMatrix(m,n,max) returns a random mxn matrix with integer entries in [0,max).
randomMatrix := (m,n,maximum) -> matrix apply( m, i -> apply( n, j -> random(maximum) ) )

-- conVec(u) transforms a one-dimensional list u into a column vector
colVec := u -> transpose matrix {u}

-- constantMatrix(c,m,n) generates an mxn matrix whose entries all equal c. 
constantMatrix := (c,m,n) -> matrix toList apply(m, i -> toList apply(n, x -> c) )

-- constantVector(c,m) generates an m dimensional column vector whose entries all equal c. 
constantVector := (c,m) -> constantMatrix(c,m,1)

-- zeroMatrix(m,n) returns the mxn zero matrix.
zeroMatrix := (m,n) -> constantMatrix(0,m,n)

-- getFilename generates a random name for temporary files.    
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

-- newton(A) returns the newton polyhedron of a matrix A.
newton := A -> convexHull( A ) + posOrthant( rank target A )

-- feasLP(A,u) returns the polyhedron consisting of all nonnegative points x
-- in the domain of A such that Ax<=u (i.e., the feasible region of the linear 
-- program P(A,u)). u can be a simple list, or a column matrix; if not provided, it's
-- assumed to be the column matrix with all entries equal to 1.
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

-- optLP(A,u) returns the the optimal set for the linear program P(A,u).
-- u can be a simple list, or a column matrix; if not provided, it's
-- assumed to be the column matrix with all entries equal to 1.
optLP = method()
optLP ( Matrix, Matrix ) := ( A, u ) -> maxFace( transpose matrix { constantList( 1, rank source A) }, feasLP(A, u) )
optLP ( Matrix, List ) := ( A, u ) -> optLP( A, colVec u )
optLP Matrix := A -> maxFace( constantVector( 1, rank source A ), feasLP A )     

-- univDenon(A) returns a universal denominator for the matrix A.
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

-- properFaces(P) returns a list of all proper faces of the polyhedron P.
properFaces = method() 
properFaces Polyhedron := P -> 
(
    d := dim P;
    toList sum(1..d, i -> set facesAsPolyhedra( i, P ) )
)

-- selectColumnsInFace(A,P) returns a submatrix of A consisting of all columns
-- contained in the polyhedron P.
selectColumnsInFace = method()
selectColumnsInFace ( Matrix, Polyhedron ) := ( A, P ) ->
(
   indices := select( rank source A, i -> contains( P, A_{i} ) );
   A_indices
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
    faces := properFaces newton A;
    matrices := apply( faces, F -> selectColumnsInFace( A, F ) | rb F );
    ( numRows( A ) - 1 )*lcm apply( matrices, M -> lcmMinors M )
) 

-- ft(A,u) returns the F-threshold of the monomial pair (A,u).
-- u can be a column matrix or a list; if not provided, assumed to be {1,1,...1}. 
ft = method()
ft ( Matrix, Matrix ) := (A,u) -> (
    NA := newton A;
    -- the intersection point of the ray spanned by u and the newton polyhedron of A:
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
uData := (A,u,q) -> 
(
    s := specialPt(A,u);
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
--     s := specialPt(A,u);
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

mu := ( A, u, p0, p, t ) ->
(
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


