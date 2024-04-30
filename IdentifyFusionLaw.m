/*

Define some intrinsics to be used to find (axial) decompositions of algebras and the Miyamoto automorphisms

*/

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

//
//
// ========== Functions to check deompositions ==========
//
//
/*

Adjoint

*/
intrinsic AdjointMatrix(a::AlgGenElt) -> AlgMatElt
  {
  The adjoint matrix for the (right) action of a.
  }
  A := Parent(a);
  return Matrix([ Vector(A.i*a) : i in [1..Dimension(A)]]);
end intrinsic;
/*

Eigenvalues and Eigenspaces

*/
intrinsic Eigenvalues(a::AlgGenElt) -> SetIndx
  {
  Returns the Eigenvalues for the adjoint action of a.
  }
  ad_a := AdjointMatrix(a);
  evals := IndexedSet(Eigenvalues(ad_a));
  Sort(~evals, func<x,y | EigenSort(x[1], y[1])>);
  
  return evals;
end intrinsic;

intrinsic Eigenspace(a::AlgGenElt, lm::RngElt) -> ModTupRng
  {
  The lm-eigenspace of the adjoint action of a.
  }
  ad_a := AdjointMatrix(a);
  return Eigenspace(ad_a, lm);
end intrinsic;
/*

check semisimplicity

*/
intrinsic IsSemisimple(a::AlgGenElt) -> BoolElt, SeqEnum, SetIndx
  {
  Returns whether the element semisimple.  If true also returns the set of eigenvalues and the eigenspaces.
  }
  A := Parent(a);
  
  evals := Eigenvalues(a);
  Sort(~evals, func<x,y | EigenSort(x[1], y[1])>);
  // Must be a sequence as the zero subspace could be repeated
  espaces := [ Eigenspace(a, t[1]) : t in evals ];
  
  if Dimension(A) eq &+[ Dimension(U) : U in espaces] then
    return true, evals, espaces;
  else
    return false;
  end if;
end intrinsic;
/*

Identify fusion law

*/
intrinsic IdentifyFusionLaw(a::AlgGenElt: eigenvalues := Eigenvalues(a)) -> SetEnum, SeqEnum, FusLaw
  {
  If the element is semisimple, returns the eigenvalues, eigenspaces and fusion law.  Optional argument to provide an indexed set of eigenvalues in the desired order.
  }
  so, evals, espaces := IsSemisimple(a);
  if not so then
    print "The element is not semisimple.";
    return evals, _, _;
  end if;

  assert assigned evals and assigned espaces;
  
  require Type(eigenvalues) in {SeqEnum, SetIndx}: "The eigenvalues should be supplied as a sequence or an indexed set.";
  
  if Type(eigenvalues[1]) eq Tup then
    require forall{ t : t in eigenvalues | #t eq 2}: "The eigenvalues aren't given in the required form.";
    eigenvalues := {@ t[1] : t in eigenvalues @};
  end if;
  
  eigenvalues := IndexedSet(eigenvalues); // in case eigenvalues was given as a SeqEnum
  
  Set_evals := {@ t[1] : t in evals@};
  require Set_evals eq eigenvalues: "You have not supplied a valid list of eigenvalues.";
  
  // define so that the eigenvalues are in the desired order
  espaces := [ espaces[Position(Set_evals, lm)] : lm in eigenvalues ];
  evals := {@ <eigenvalues[i], Dimension(espaces[i])> : i in [1..#evals] @};
  
  ebas := [ Basis(U) : U in espaces];
  V := VectorSpaceWithBasis(&cat(ebas));
  
  dimseq := [ [f..f+Dimension(espaces[i])-1] where f := i eq 1 select 1 else Self(i-1)[#Self(i-1)]+1 : i in [1..#evals]];
  
  function Indicator(v)
    coords := Coordinates(V, V!Eltseq(v));
    return {@ i : i in [1..#evals] | not IsZero(coords[dimseq[i]]) @};
  end function;
  
  FL := New(FusLaw);
  FL`set := IndexedSet([1..#evals]);
  
  FL`law := [[ {@ Universe(FL`set)| @} : i in [1..#evals] ] : i in [1..#evals] ];
  
  A := Parent(a);
  for i in [1..#espaces] do
    if IsCommutative(A) then
      for j in [i..#espaces] do
        prods := [ (A!v)*(A!w) : v in ebas[i], w in ebas[j]];
        FL`law[i,j] := &join[ Indicator(p) : p in prods];
        FL`law[j,i] := FL`law[i,j];
      end for;
    else
      // we are not commutative
      for j in [1..#espaces] do
        prods := [ (A!v)*(A!w) : v in ebas[i], w in ebas[j]];
        FL`law[i,j] := &join[ Indicator(p) : p in prods];
      end for;
    end if;
  end for;

  f := map< FL`set -> BaseRing(A) | i:->eigenvalues[i], j:-> Position(eigenvalues,j)>;
  AssignEvaluation(~FL, f);
  
  return evals, espaces, FL;
end intrinsic;
//
//
// ========== Functions to impose a fusion law ==========
//
//
/*

Two seperate ways to impose a fusion law: either find the ideal of the algebra such that in the quotient the fusion law holds, otherwise find the quotient of the base ring such that when quotienting out the scalars by that ideal, the algebra has the fusion law.

*/
function ClearDenominators(v)
  if IsFinite(BaseRing(v)) then  // in a finite field there are no denominators and Denominator fails
    return v;
  else
    lcm := LCM([ Denominator(r) : r in Eltseq(v) | r ne 0] cat [1]);
    return lcm*v;
  end if;
end function;

/*
intrinsic IdealOfCoefficientsToImposeFusionLaw(a::AlgGenElt, FL::FusTab) -> AlgGen, SeqEnum
  {
  For an algebra over a function field, calculate the ideal I over the base ring R of the coefficients such that a semisimple element a has fusion law FL in the algebra over R/I.  Also returns the positions in the fusion law which require change.  Note that FL must have an evaluation map and the eigenvalues must be the same as those of a.
  }
  require IsIdempotent(a): "The element a must be an idempotent.";
  require IsSemisimple(a): "The element a must be semisimple.";
  
  evals, espaces, FL := IdentifyFusionLaw(a);
  so, eval_map := HasEvaluation(FL);
  require so: "The fusion law FL must have an evaluation map.";
  evals := {@ t[1] : t in evals @};
  require evals eq Eigenvalues(FL): "a does not have the same eigenvalues as the fusion law.";
  
  V := VectorSpaceWithBasis([ ClearDenominators(v) : v in Basis(espace[i]), i in [1..#evals]]);
  
  index := Partition([1..Dimension(V)], [ Dimension(espace[i]) : i in [1..#evals]]);
  
  // For an elt v in A_i A_j, return the coords which must be in the ideal
  P := RingOfIntegers(BaseRing(A));
  
  function idealelts(v, i, j)
    coords := ClearDenominators(Coordinates(V, Vector(v)));
    
    wanted_parts := (evals[i]@@eval_map)*(evals[j]@@eval_map);
    
    
  
    coords := Coordinates(V, Vector(v));
    lcm := IsZero(coords) select 1 else LCM([ Denominator(r) : r in coords | r ne 0]); // Clear any denominators
    coords := [r*lcm : r in coords];
    
    real := tar[evals[i]@FT_to_tar, evals[j]@FT_to_tar]@@FT_to_tar;
    return {@ coords[k] : k in [1..Dimension(V)] | k notin &cat[ index[Position(evals,f)] : f in real] @} diff {@ 0@};
  end function;
  

  
  
  
end intrinsic;
*/
//
//
// ========== Find the Miyamoto automorphisms ==========
//
//
// For two subspaces pos and neg s.t pos \oplus neg is the whole vector space, form the involution corresponding to the grading.
function GradedInvolution(pos, neg)
  ebas := [ Basis(U) : U in [pos, neg]];
  CoB := Matrix(&cat(ebas));

  F := BaseRing(pos);
  pos_dim := Dimension(pos);
  neg_dim := Dimension(neg);
  M := DiagonalJoin(IdentityMatrix(F, pos_dim), -IdentityMatrix(F, neg_dim));
  
  return CoB^-1*M*CoB;
end function;


intrinsic MiyamotoInvolution(a::AlgGenElt, lm::RngElt: check_fusion := true) -> AlgMatElt
  {
  The Miyamoto involution for the axis a with respect to the eigenspace lm.  Note the fusion law must be graded and lm be in a part which is mapped to an involution.
  
  Optional argument to check the fusion law.
  }
  so, evals, espaces := IsSemisimple(a);
  require so : "The element is not semisimple.";

  evals := {@ t[1] : t in evals @};

  require lm in evals: "The scalar given is not an eigenvalue.";

  if check_fusion then
    _, _, FL := IdentifyFusionLaw(a);

    T, gr := FinestAdequateGrading(FL);
    FLelts := Elements(FL);
    eval_map := Evaluation(FL);
    
    so := exists(t_lm){ t : t in FLelts | t@eval_map eq lm};
    assert so;
    gr_lm := t_lm@gr;
    require gr_lm ne T!1: "The eigenvalue given must be non-trivially graded.";

    A := Parent(a);

    plus := [ t@eval_map : t in FLelts | t@gr ne gr_lm];
    minus := [ t@eval_map : t in FLelts | t@gr eq gr_lm];
  else
    // don't check fusion law
    plus := evals diff {@ lm @};
    minus := {@ lm @};
  end if;
  
  pos := &+[ espaces[Position(evals, mu)] : mu in plus];
  neg := espaces[Position(evals, lm)];

  return GradedInvolution(pos,neg);
end intrinsic;

intrinsic MiyamotoInvolution(a::AlgGenElt) -> AlgMatElt
  {
  The Miyamoto involution for the axis a.  Note the fusion law must be C_2 (or trivially) graded.
  }
  require IsSemisimple(a) : "The element is not semisimple.";
  
  evals, espaces, FL := IdentifyFusionLaw(a);
  evals := [ t[1] : t in evals];
  
  T, gr := FinestAdequateGrading(FL);
  require Order(T) le 2: "The fusion law is not C_2 graded.";
  
  A := Parent(a);
  eval_map := Evaluation(FL);
  
  FLelts := Elements(FL);
  plus := [ t@eval_map : t in FLelts | t@gr eq T!1];
  minus := [ t@eval_map : t in FLelts | t@gr eq T.1];
  
  pos := &+[ espaces[Position(evals, t)] : t in plus];
  neg := &+[ espaces[Position(evals, t)] : t in minus];
  
  return GradedInvolution(pos, neg);
end intrinsic;

intrinsic MiyamotoInvolution(a::AlgGenElt, chi::AlgChtrElt) -> AlgMatElt
  {
  
  }
  
  
  
  
end intrinsic;



intrinsic AxisSubgroup(a::AlgGenEnt) -> .
  {
  
  }
  
end intrinsic;
//
//
// ========== Frobenius form ==========
//
//
intrinsic IsFrobeniusForm(frob::Mtrx, A::AlgGen : ideal := ideal<RingOfIntegers(BaseRing(A))|>) -> BoolElt, Tup
  {
  Returns whether frob is a frobenius form for the algebra A.  Optional argument of an ideal which equality is checked up to.
  }
  require NumberOfRows(frob) eq NumberOfColumns(frob): "frob must be a square matrix.";
  require NumberOfRows(frob) eq Dimension(A): "frob must have the same dimension as the algebra A.";
  
  bas := Basis(A);
  if IsCommutative(A) then
    require IsSymmetric(frob): "frob is not symmetric.";
    so := forall(err){ <i,j,k> : k in [1..j], j in [1..i], i in [1..#bas] | Numerator(InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j]))) in ideal};
  else
    so := forall(err){ <i,j,k> : i,j,k in [1..#bas] | Numerator(InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j]))) in ideal};
  end if;
  if so then
    return so, _;
  else
    return so, err;
  end if;
end intrinsic;
