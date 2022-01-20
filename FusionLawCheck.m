function AdjointMatrix(a);
  A := Parent(a);
  return Matrix([ Vector(a*A.i) : i in [1..Dimension(A)]]);
end function;
/*

A sorting function for sorting eigenvalues into the normal order for fusion rules.

*/
function EigenSort(x, y)
  if x eq y then
    return 0;
  elif x eq 1 then
    return -1;
  elif y eq 1 then
    return 1;
  elif x eq 0 then // y neq 0, 1
    return -1;
  elif y eq 0 then // x neq 0, 1
    return 1;
  else // x, y neq 0, 1
    return x-y;
  end if;
end function;

function IdentifyFusionLaw(a)
  A := Parent(a);
  ad_a := AdjointMatrix(a);
  evals := IndexedSet(Eigenvalues(ad_a));
  //require &+[ t[2] : t in evals] eq Dimension(A): "The element is not semisimple.";
  if &+[ t[2] : t in evals] ne Dimension(A) then
    print "The element is not semisimple.";
    return false;
  end if;
  
  Sort(~evals, func<x,y | EigenSort(x[1], y[1])>);
  espaces := [ Eigenspace(ad_a, t[1]) : t in evals];
  ebas := [ Basis(U) : U in espaces];
  
  //require Dimension(sub<VectorSpace(A) | &cat(ebas)>) eq Dimension(A): "The element is not semisimple.";
  if Dimension(sub<VectorSpace(A) | &cat(ebas)>) ne Dimension(A) then
    print "The element is not semisimple.";
    return false;
  end if;
  V := VectorSpaceWithBasis(&cat(ebas));
  
  dimseq := [ [f..f+Dimension(espaces[i])-1] where f := i eq 1 select 1 else Self(i-1)[#Self(i-1)]+1 : i in [1..#evals]];
  
  function Indicator(v)
    coords := Coordinates(V, V!Eltseq(v));
    return { i : i in [1..#evals] | not IsZero(coords[dimseq[i]])};
  end function;
  
  FT := [[ {@Universe({e[1] : e in evals})|@}: i in [1..#evals] ] : i in [1..#evals] ];
  for i in [1..#espaces] do
    for j in [i..#espaces] do
      prods := [ (A!v)*(A!w) : v in ebas[i], w in ebas[j]];
      inds := &join[ Indicator(p) : p in prods];
      FT[i,j] := {@ Universe({e[1] : e in evals})| evals[k,1] : k in inds @};
      FT[j,i] := FT[i,j];
    end for;
  end for;
  return evals, espaces, FT;
end function;

function MiyamotoInvolution(a, lm)
  A := Parent(a);
  ad_a := AdjointMatrix(a);
  evals := IndexedSet(Eigenvalues(ad_a));
  Sort(~evals, func<x,y | x[1] eq lm select -1 else y[1] eq lm select 1 else -1>);
  if &+[ t[2] : t in evals] ne Dimension(A) then
    print "The element is not semisimple.";
    return false;
  end if;
  
  espaces := [ Eigenspace(ad_a, t[1]) : t in evals];
  ebas := [ Basis(U) : U in espaces];
  if Dimension(sub<VectorSpace(A) | &cat(ebas)>) ne Dimension(A) then
    print "The element is not semisimple.";
    return false;
  end if;
  
  CoB := Matrix(&cat(ebas));
  
  F := BaseRing(A);
  dim := Dimension(Eigenspace(ad_a, lm));
  M := DiagonalJoin(-IdentityMatrix(F, dim), IdentityMatrix(F, Dimension(A)-dim));
  
  return CoB^-1*M*CoB;
end function;

function IdealOfIdempotents(A);
  P := PolynomialRing(BaseRing(A), Dimension(A));
  
  AA := ChangeRing(A, P);
  x := AA![P.i : i in [1..Dimension(A)]];
  
  I := ideal<P | Eltseq(x^2 -x)>;

  return I;
end function;

Monster_FT := [ [ {@ 1 @}, {@ @}, {@ 3 @}, {@ 4 @} ],
                [ {@ @}, {@ 2 @}, {@ 3 @}, {@ 4 @} ],
                [ {@ 3 @}, {@ 3 @}, {@ 1, 2 @}, {@ 4 @} ],
                [ {@ 4 @}, {@ 4 @}, {@ 4 @}, {@ 1, 2, 3 @} ]];
Jordan_FT := [ [ {@ 1 @}, {@ @}, {@ 3 @} ],
               [ {@ @}, {@ 2 @}, {@ 3 @} ],
               [ {@ 3 @}, {@ 3 @}, {@ 1, 2 @} ] ];

function ClearDenominators(v)
  if IsFinite(BaseRing(v)) then  // in a finite field there are no denominators and Denominator fails
    return v;
  else
    lcm := LCM([ Denominator(r) : r in Eltseq(v) | r ne 0]);
    return lcm*v;
  end if;
end function;

// let S be the "normal" ordering of eigenvalues in the Monster fusion law
function ImposeMonsterFusionLaw(a, S)
  A := Parent(a);
  eval_mults, espace, FT := IdentifyFusionLaw(a);
  if not assigned FT then
    print "Error, fusion law is not defined.";
    return false, _;
  end if;
  
  evals := {@ t[1] : t in eval_mults @};
  if evals ne Set(S) or Type(S) notin {SeqEnum, SetIndx} then
    print "You have not given an ordered set of eigenvalues.";
    return false, _;
  elif 1 notin evals then
    print "1 is not an eigenvalue.";
    return false, _;
  elif #evals notin {3,4} then
    print "The number of eigenvalues must be 3, or 4.";
    return false, _;
  end if;
  
  if #evals eq 4 then
    tar := Monster_FT;
  else
    tar := Jordan_FT;
  end if;
  
  FT_to_tar := map< evals -> [1..#evals] | i:-> Position(S, i), j:-> S[j]>;
  
  V := VectorSpaceWithBasis([ ClearDenominators(v) : v in Basis(espace[i]), i in [1..#evals]]);
  
  index := Partition([1..Dimension(V)], [ Dimension(espace[i]) : i in [1..#evals]]);

  // For an elt v in A_i A_j, return the coords which must be in the ideal
  P := RingOfIntegers(BaseRing(A));
  function idealelts(v, i, j)
    coords := Coordinates(V, Vector(v));
    lcm := IsZero(coords) select 1 else LCM([ Denominator(r) : r in coords | r ne 0]); // Clear any denominators
    coords := [r*lcm : r in coords];
    real := tar[evals[i]@FT_to_tar, evals[j]@FT_to_tar]@@FT_to_tar;
    return {@ coords[k] : k in [1..Dimension(V)] | k notin &cat[ index[Position(evals,f)] : f in real] @} diff {@ 0@};
  end function;
  
  rels := [ [ &join{@ idealelts((A!v)*(A!w), i,j) : v in Basis(espace[i]), w in Basis(espace[j]) @} : j in [1..i]] : i in [1..#evals]];

  pos := [ [i,j] : j in [1..i], i in [1..#evals] | not IsEmpty(rels[i,j]) ];
  
  return ideal<P | ChangeUniverse(&join Flat(rels), P)>, pos;
end function;

function IsFrobeniusForm(frob, A : ideal := ideal<RingOfIntegers(BaseRing(A))|>)
  bas := Basis(A);
  so := forall(err){ <i,j,k> : i,j,k in [1..#bas] | Numerator(InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j]))) in ideal};
  if so then
    return so, _;
  else
    return so, err;
  end if;
end function;

