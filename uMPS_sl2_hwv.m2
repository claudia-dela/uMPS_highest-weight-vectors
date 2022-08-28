--open terminal, go to the folder of the script and use M2 filename.m2 to run the code
restart
K =QQ;
N=8;	     	    --number of sites 
k=2;	    	    --degree of the polynomials
maxWeight=N*k;	    --higher degree of monomials
print(concatenate{"Number of sites: N=",toString(N),", degree: k=",toString(k),", max weight: N*k=",toString(maxWeight)})
---------------------------------------------------------------------------------------BINARY BRACELETS
--List all q-tuples of numbers in the alphabet [k]:= {0,..,k-1}
qkmaps = (q,k) ->(
    if q==0 then return {{}}
    else (
	foo = qkmaps(q-1,k);
	antw={};
	i = 0;
	while i<k do {
	    b={};
            for el in foo do {
                b=join(b,{join(el,{i})})
                };
            antw=join(antw,b);
	    i=i+1
	    };
        return antw)
    )

--Check if 2 lists are equal up to cyclic and dihedral permutation, 
--i.e. if they are equivalent under the action of the cyclic group and the dihedral group.
equalUpToRevOrCycPermutation = (L1,L2) -> (
    theLength = #L1;
    for m from 1 to theLength do{
        L2=append(L2,L2#0);
        L2=drop(L2,1);
	--print L2;
	--print reverse(L2);
        if (L1==L2 or L1==reverse(L2)) then {
       	    --if L1==L2 then {
	    return true;
	    }
	};
    return false
    )

-- Generation of the set  (the set B(2,N)): the set of words of lenght N in the alphabet [2]
Bracelets=qkmaps(N,2);
c=0;
while (c<#Bracelets) do {
    -- print c;
    el = Bracelets#c;
    cc = 0;
    noDuplicateFound = true;
    while (cc<c and noDuplicateFound) do {
	if equalUpToRevOrCycPermutation(el,Bracelets#cc) then {
	    noDuplicateFound = false;
	    };
	cc=cc+1;
	};
    if noDuplicateFound then {c = c+1;} else {Bracelets=remove(Bracelets,c);};
    };

--Bracelets= B(2,N)
c=#Bracelets

-------------------------------------------------------------------------POLYNOMIAL RING
-- Construction of the ring of polynomial functions 
-- Generation of the coordinates of the polynomial ring C[Dih]: 
-- x_b, with b element of Bracelets = B(2,N)
xRing= apply(Bracelets,j->x_j);
RS=K[xRing];
xRingGens = generators RS;

--List of all monomials in the ring RS of degree k
kMonomials = flatten entries basis(k,RS); 

-------------------------------------------------------------------------WEIGHTS
--Function that computes the weight of a monomial
-- Input: the set of Bracelets and a monomial in RS
weight=(pt,pol)->(
    E = exponents(pol);
    a = {};
    for e in E do(
	a=append(a,sum for i from 0 to #pt-1 list((e#i)*sum(pt#i)));
	);
    return a;
    )
--EXAMPLE
--weight(Bracelets,kMonomials#1)

--Ordered list of weights of the elements in kMonomials, i.e. the monomials in RS of degree k 
wlist={};
for j in kMonomials do(
    wlist=flatten append(wlist, weight(Bracelets,j));
    );
--wlist
--List of monomials of a fixed weight w
wpoly = (w) ->(
    sel={};
    for i from 0 to #kMonomials-1 do(
	if wlist#i==w then sel=append(sel,kMonomials#i) else continue; 
    	);
    return sel;
    )

-------------------------------------------------TRACE PARAMETRIZATION
S=K[T_0..T_4];
H = new MutableHashTable;
--H#(i,j,k,...)=trace(A_i*A_j*A_k*...), written in the T_i's
H#{0} = T_0;
H#{1} = T_1;
H#{0,0} = T_2;
H#{0,1} = T_3;
H#{1,0} = T_3;
H#{1,1} = T_4;

for i in (toList ((set {0,1})^**3/deepSplice)) do {
    i=toList i;
    H#i = ((H#{i#0})*(H#{i#1,i#2})+(H#{i#1})*(H#{i#2,i#0})+(H#{i#2})*(H#{i#0,i#1})-(H#{i#0})*(H#{i#1})*(H#{i#2}))/2
    }

for n in 4..N do {
    for i in (toList ((set {0,1})^**n/deepSplice)) do {
    	i = toList i;
    	a={i#0};
    	bi={i#1};
    	ci={i#2};
    	d=apply(n-3,j->(i#(j+3)));
    	H#i = (
	    (H#a)*((H#(bi|ci|d))-((H#bi)*(H#(ci|d))))
	    +(H#bi)*((H#(ci|d|a))-((H#ci)*(H#(d|a))))
	    +(H#ci)*((H#(d|a|bi))-((H#d)*(H#(a|bi))))
	    +(H#d)*((H#(a|bi|ci))-((H#a)*(H#(bi|ci))))
	    -(H#(a|ci))*(H#(bi|d))
	    +(H#(a|bi))*(H#(ci|d))
	    +(H#(a|d))*(H#(bi|ci))
	    +(H#a)*(H#bi)*(H#ci)*(H#d)
	    )/2
	};
    }

coordinates=apply(Bracelets,j->H#j);
#coordinates
----------------------------------------------------------------------------RAISING OPERATOR
--Given q polynomial in RS, the raising operator acs as follows: 
--for each input coordinate x_{i_1,..i_m} it outputs the sum of x_{j_1,..,j_m}, 
--where {j_1,..,j_m} is in Bracelets and it is {i_1,..,i_m} with a 0 substituted by a 1
 
-- for every I={i_1,..,i_m}, creation of the set {{j_1,..,j_m}: it is {i_1,..,i_m} with a 0 substituted by a 1}
-- EXAMPLE: if {i_1,i_2}={0,0} then {0,0}->{{1,0},{0,1}}

le={};
for v in Bracelets do(
    l1={};
    for j from 0 to N-1 do(
	var= new MutableList from v;
	if v#j==0 then (var#j=1,l1=append(l1,toList var));
	);
    le=append(le,l1);
    )  
lf={};
for v in Bracelets do(
    l1={};
    for j from 0 to N-1 do(
	var= new MutableList from v;
	if v#j==1 then (var#j=0,l1=append(l1,toList var));
	);
    lf=append(lf,l1);
    )  

g={};
--Division into equivalence classes, counting the cardinality
--EXAMPLE: if {1,0} in Bracelets and {0,1} (since {1,0}={0,1} in Bracelets)
-- in EqClassList we have: {0,0} ->{{1,0},2}
for l2 in {le,lf} do(
    EqClassList={};
    for l3 in l2 do (
	l4={};
       	for i from 0 to #l3-1 do(
	    A= new MutableList from l3#i;
	    --if A is not in Bracelets, find its rapresentative in Bracelets
	    if member(toList A,Bracelets)==false then (
		kk1=0;
		condition=false;
		while (kk1<#Bracelets and (not condition)==true) do (
		    if equalUpToRevOrCycPermutation(toList A,Bracelets#kk1)==true then (A=Bracelets#kk1,condition=true); 
		    kk1=kk1+1;
		    ) 
		);
	    kk2 = 0;
	    if member(toList A,Bracelets)==true then (
		for j from 0 to #l3-1 do(
		    if equalUpToRevOrCycPermutation(toList A,l3#j)==true then (kk2=kk2+1);
		    )
		);
	    l4 = append(l4,{toList A,kk2});
	    );
	l4 = unique l4;
	EqClassList = append(EqClassList,l4);
       	);
    f={};
    for i from 0 to #EqClassList-1 do (
	e=EqClassList#i;
	if e=={} then f=append(f,0) else(
	    t = sum apply(#e,j->((e#j)#1)*x_((e#j)#0));
	    f = append(f,t);
	    );
	);
    --The map on the element x_I acts:
    g=append(g,map(RS,RS,f));
    )

--------------------------------------------------
--Input: 
-- g: action on the monomials 
-- the set Bracelets
-- a polynomial with all monomials of the same weight
derivFunctionF = (g,pt,pol)->(
    deg = (degree pol)#0;
    (M,C)= coefficients pol;
    C= flatten entries C;
    E = exponents(pol);
    l = {};
    for e in E do(
	a={};
	for i from 0 to #pt-1 do if e#i!=0 then a=join(a,apply(e#i,j->x_(pt#i)));
	l=append(l,a);
	);
    lii={};
    for j from 0 to #l-1 do(
	li={};
	ll=l#j;
    	for i from 0 to deg-1 do (
	    --i=0
    	    copyl=new MutableList from ll;
	    copyl#i=g(ll#i);          
    	    li=append(li,product (toList copyl));
    	    );
	lii=append(lii,sum li);
	);
    Fpol = sum apply(#C,j->(C#j*lii#j));
    return Fpol;
    )


--EXAMPLE:
--derivFunctionF(g#0,Bracelets,x_(Bracelets#1)^k)
--g#0 is the action of the raising operator 0->1
--g#1 is the action of the lowering operator 1->0
----------------------------------------------------------------------------ALGORITHM
----------------------------------------------------------------------------Solve the linear system
--Compute all the highest wight vectors of C[Dih]_k
--V = vector space of degree k polynomials in C[Dih] (with basis "x^deg_k")
--W1 = vector space of polynomials in the trace-algebra coordinates T_i (non homogeneous)
--W2 = vector space of polynomials in coordinates x_I, with I in Bracelets (with basis "x^deg_k" given by the image of derivFunctionF)

z=map(K,RS);
zz=map(K,S);

-----------------------------------------------------------------------------HIGHEST WEIGHT AMBIENT SPACE
print "Computing the highest weight vectors of the ambient space";
LISTPOLY = {};
for w from 0 to ceiling(N*k/2) do(	       
    LPOLY = wpoly(w);
    d = apply(#LPOLY,j->derivFunctionF(g#1,Bracelets,LPOLY#j));	--time (changed from g#0)
    dmatrix = matrix{d};
    mondBasis = unique flatten entries monomials(dmatrix);
    Lv2 = #mondBasis;    
    ---------------------------------------------------------------
    if Lv2 != 0 then(
	Matrix2 = matrix(apply(Lv2,i->{0}));
	for i from 0 to #d-1 do(
	    (Mon2,Coeff2) = coefficients(d#i,Monomials=>matrix{mondBasis});
	    Matrix2 = Matrix2|Coeff2;
	    );
	Matrix2 = z(submatrix(Matrix2,{1..#d}));
	tempMat = Matrix2;
	tempMat =  gens kernel tempMat;
	listpolyw = {};
	for i from 0 to (numgens source tempMat)-1 do (
	    listpolyw = append(  listpolyw, (  (matrix{LPOLY})*tempMat_{i}  )_(0,0) );
	    );
	LISTPOLY = append(LISTPOLY,listpolyw);
    	)
    else LISTPOLY = append(LISTPOLY,{});
    )

HWvectors = LISTPOLY;
print "Done. Writing in file"

--------------------------------------------------------------------------------------WRITE TO FILE SUMMARY
summaryhw = concatenate {"HWsummary_",toString(N),"_",toString(k)};
summaryhw<< concatenate {"N=",toString(N),",k=",toString(k),",maxweight=",toString(maxWeight)};
summaryhw << " ; \n";
----
for i from 0 to #HWvectors-1 do (
    string =  toString(#(HWvectors#i));
    summaryhw << string;
    summaryhw << " polynomials of weight ";
    summaryhw << toString(i);
    summaryhw << " ; \n";
    );
----
summaryhw <<close

-------------------------------------------------------------------WRITE TO FILE EXPLICIT POLYNOMIALS
hwset = concatenate {"HWpolynomials_",toString(N),"_",toString(k)};
hwset << concatenate {"N=",toString(N),",k=",toString(k),",maxweight=",toString(maxWeight)};
hwset << " ; \n";
----
for i from 0 to #HWvectors-1 do (
    string =  toString(#(HWvectors#i));
    hwset << string ;
    hwset << " polynomials of weight ";
    hwset << toString(i);
    hwset << " : ";
    hwset << toString(HWvectors#i);
    hwset << " ; \n";
    );
----
hwset << close

-----------------------------------------------------------HIGHEST WEIGHT IN THE IDEAL OF THE VARIETY
print "Computing the highest weight vectors of the variety";
VarietyHWvectors = {};
for i from 0 to #HWvectors-1 do ( 							    	    
    if #(HWvectors#i) !=0 then(
	monBasis = {};
	mw = {};
	for j from 0 to #(HWvectors#i)-1 do ( 							   	
	    m = sub(HWvectors#i#j,apply(#xRingGens, i -> (xRingGens#i => coordinates#i)));
	    mw = append(mw,m);
	    monBasis = unique flatten append(monBasis,unique flatten entries monomials(m));
    	    );
	monBasis = unique monBasis;
	Lv1=#monBasis;
	if Lv1 != 0 then(
	    Matrix1 = matrix(apply(Lv1,i->{0}));
	    for k from 0 to #mw-1 do(
		(Mon,Coeff)=coefficients(mw#k,Monomials=>matrix{monBasis});
		Matrix1 = Matrix1|Coeff;
    		);
	    --print numgens source Matrix1; 
	    Matrix1 = zz(submatrix(Matrix1,{1..#mw}));
	    varHWgens =  gens kernel Matrix1;    
	    varHWv = {};
	    if (numgens source varHWgens) !=0 then (
		for l from 0 to (numgens source varHWgens)-1 do (
		    oneof = {};
		    for t from 0 to (numgens target varHWgens)-1 do(
			oneof = append(oneof, (HWvectors#i#t)*((flatten entries varHWgens_{l})#t)   );
			);
		    varHWv = append(varHWv, sum(oneof));
		    );
		VarietyHWvectors = append(VarietyHWvectors,{i,varHWv});
		); 	          	    
	    );
	); 
    )

print "Done. Writing in file"
------------------------------------------------------------------WRITE TO FILE SUMMARY
uMPSsummaryhw = concatenate {"uMPS_HWsummary_",toString(N),"_",toString(k)};
uMPSsummaryhw<< concatenate {"N=",toString(N),",k=",toString(k),",maxweight=",toString(maxWeight)};
uMPSsummaryhw << " ; \n";
----
for i from 0 to #VarietyHWvectors-1 do (
    string =  toString(#(VarietyHWvectors#i#1));
    uMPSsummaryhw << string;
    uMPSsummaryhw << " polynomials of weight ";
    uMPSsummaryhw << toString(VarietyHWvectors#i#0);
    uMPSsummaryhw << " ; \n";
    );
----
uMPSsummaryhw <<close
--print "Done summary"
-------------------------------------------------WRITE TO FILE EXPLICIT POLYNOMIALS
uMPShw = concatenate {"uMPS_HWpolynomials_",toString(N),"_",toString(k)};
uMPShw << concatenate {"N=",toString(N),",k=",toString(k),",maxweight=",toString(maxWeight)};
uMPShw << " ; \n";
----
for i from 0 to #VarietyHWvectors-1 do (
    string =  toString(#(VarietyHWvectors#i#1));
    uMPShw << string ;
    uMPShw << " polynomials of weight ";
    uMPShw << toString(VarietyHWvectors#i#0); --toString(i);
    uMPShw << " : ";
    uMPShw << toString(VarietyHWvectors#i);
    uMPShw << " ; \n";
    );
----
uMPShw << close


    
