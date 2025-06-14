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
intrinsic Annihilator(A::AlgGen) -> AlgGen
  {
  Returns the annihilator of the algebra.
  }
  // create the matrix which is the horizontal join of the matrices ad_a for each a in a basis of A.
  
  M := HorizontalJoin([AdjointMatrix(u) : u in Basis(A)]);
  
  return sub<A | [ A | x : x in Basis(Nullspace(M))]>;
end intrinsic;
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
intrinsic Eigenvalues(a::AlgGenElt: adjoint_matrix := AdjointMatrix(a)) -> SetIndx
  {
  Returns the Eigenvalues for the adjoint action of a.  Optional argument to input the adjoint matrix, if known.
  }
  evals := IndexedSet(Eigenvalues(adjoint_matrix));
  try
    Sort(~evals, func<x,y | EigenSort(x[1], y[1])>);
  catch e;
  end try;
  
  return evals;
end intrinsic;

intrinsic Eigenspace(a::AlgGenElt, lm::RngElt: adjoint_matrix := AdjointMatrix(a)) -> ModTupRng
  {
  The lm-eigenspace of the adjoint action of a.  Optional argument to input the adjoint matrix, if known.
  }
  return Eigenspace(adjoint_matrix, lm);
end intrinsic;
/*

check semisimplicity

*/
intrinsic IsSemisimple(a::AlgGenElt) -> BoolElt, SeqEnum, SetIndx
  {
  Returns whether the element semisimple.  If true also returns the set of eigenvalues and the eigenspaces.
  }
  A := Parent(a);
  
  ad_a := AdjointMatrix(a);
  evals := Eigenvalues(a: adjoint_matrix := ad_a);
  
  // Must be a sequence as the zero subspace could be repeated
  espaces := [ Eigenspace(a, t[1]: adjoint_matrix := ad_a) : t in evals ];
  
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
/*

Checking fusion law is a given one

NB This is adapted from some code originally written for the automorphisms package

*/
/*

A function to check a given fusion law.  Inputs are:

  A       - algebra
  espace  - an associative array of eigenspaces with keys being the FULL set of eigenvalues for the fusion law
            NB also include these even if the subspace is empty
  fus_law - a SeqEnum of tuples <a,b,S>, where a*b = S is what needs checking from the fusion law.

*/
function check_law(A, espace, fus_law)
  fusion_set := Keys(espace);

  // first precompute the adjoints for each element in the eigenspace
  adjs := AssociativeArray([* <lm, [ AdjointMatrix(A!v) : v in Basis(espace[lm])]>
                                 : lm in fusion_set*]);
  V := VectorSpace(A);
  // I := IdentityMatrix(F, Dimension(A));
  for t in fus_law do
    a,b,S := Explode(t);
    // If either eigenspace is empty, then don't need to check
    if not IsEmpty(adjs[b]) and Dimension(espace[a]) ne 0 then
      // slightly slower to do this
      // if not forall{ ad : ad in adjs[b] | BasisMatrix(espace[a])*ad*(&*[adu-s*I : s in S]) eq 0} then
      // Quicker to take the rows of a matrix than join several subspaces.
      U := sub<V | Rows(VerticalJoin([ BasisMatrix(espace[a])*ad : ad in adjs[b]]))>;
      if not U subset &+[espace[s] : s in S] then
        return false;
      end if;
    end if;
  end for;

  return true;
end function;

intrinsic HasMonsterFusionLaw(u::AlgGenElt: fusion_values := {@1/4, 1/32@})-> BoolElt
  {
  Check if an algebra element u satisfies the Monster fusion law.  Optional argument, fusion_values, to provide the alpha and beta for M(alpha, beta).  Defaults to M(1/4,1/32) fusion law.
  }
  require Type(fusion_values) in {SetIndx, SeqEnum} and #fusion_values eq 2 and 1 notin fusion_values and 0 notin fusion_values: "You must provide two distinct non-zero, non-one ring or field elements for the fusion law.";

  require IsIdempotent(u): "The element is not an idempotent";
  
  F := Universe(fusion_values);
  fusion_set := {@ F | 1, 0 @} join IndexedSet(fusion_values);
  
  so, evals, espace := IsSemisimple(u);
  
  require so: "The element is not semisimple.";
  
  // Check we don't have extra eigenvalues
  if exists(ev){ ev[1] : ev in evals | ev[1] notin fusion_set } then
    printf "Eigenvalue %o not in %o\n", ev, fusion_set;
    return false;
  end if;
  evals := {@ t[1] : t in evals @};
  espace := AssociativeArray([* <e, espace[i]> : i->e in evals*]
              cat [* <e, Eigenspace(u,e)> : e in fusion_set | e notin evals *]);
  
  // Check the fusion law
  al := fusion_set[3];
  bt := fusion_set[4];
  // these are the tuples <a,b,S> representing a*b = S in the fusion law
  // NB don't need to check 1*a
  fus_law := [ <0, 0, {0}>, <0, al, {al}>, <0, bt, {bt}>, <al, al, {1,0}>, <al, bt, {bt}>, <bt, bt, {1,0,al}> ];
  
  return check_law(Parent(u), espace, fus_law);
end intrinsic;

intrinsic HasAlmostMonsterFusionLaw(u::AlgGenElt: fusion_values := {@1/4, 1/32@})-> BoolElt
  {
  Check if an algebra element u satisfies the Almost Monster fusion law.  Same as Monster fusion law, except 3*3 = [1,2,3], where the entries of the fusion law are [1,2,3,4].
  
  Optional argument, fusion_values, to provide the alpha and beta for M(alpha, beta).  Defaults to M(1/4,1/32) fusion law.
  }
  require Type(fusion_values) in {SetIndx, SeqEnum} and #fusion_values eq 2 and 1 notin fusion_values and 0 notin fusion_values: "You must provide two distinct non-zero, non-one ring or field elements for the fusion law.";

  require IsIdempotent(u): "The element is not an idempotent";
  
  F := Universe(fusion_values);
  fusion_set := {@ F | 1, 0 @} join IndexedSet(fusion_values);
  
  so, evals, espace := IsSemisimple(u);
  
  require so: "The element is not semisimple.";
  
  // Check we don't have extra eigenvalues
  if exists(ev){ ev[1] : ev in evals | ev[1] notin fusion_set } then
    printf "Eigenvalue %o not in %o\n", ev, fusion_set;
    return false;
  end if;
  evals := {@ t[1] : t in evals @};
  espace := AssociativeArray([* <e, espace[i]> : i->e in evals*]
              cat [* <e, Eigenspace(u,e)> : e in fusion_set | e notin evals *]);
  
  // Check the fusion law
  al := fusion_set[3];
  bt := fusion_set[4];
  // these are the tuples <a,b,S> representing a*b = S in the fusion law
  // NB don't need to check 1*a
  fus_law := [ <0, 0, {0}>, <0, al, {al}>, <0, bt, {bt}>, <al, al, {1,0,al}>, <al, bt, {bt}>, <bt, bt, {1,0,al}> ];
  
  return check_law(Parent(u), espace, fus_law);
end intrinsic;

intrinsic HasJordanFusionLaw(u::AlgGenElt: fusion_value := 1/4)-> BoolElt
  {
  Check if an algebra element u satisfies the Jordan fusion law.  Optional argument, fusion_value, to provide the eta for J(eta).  Defaults to J(1/4) fusion law.
  }
  require fusion_value notin {0,1}: "The fusion_value cannot be 0, or 1";
  
  require IsIdempotent(u): "The element is not an idempotent";
  
  F := Parent(fusion_value);
  fusion_set := {@ F | 1, 0, fusion_value @};
  
  so, evals, espace := IsSemisimple(u);
  
  require so: "The element is not semisimple.";
  
  // Check we don't have extra eigenvalues
  if exists(ev){ ev[1] : ev in evals | ev[1] notin fusion_set } then
    printf "Eigenvalue %o not in %o\n", ev, fusion_set;
    return false;
  end if;
  
  evals := {@ t[1] : t in evals @};
  espace := AssociativeArray([* <e, espace[i]> : i->e in evals*]
              cat [* <e, Eigenspace(u,e)> : e in fusion_set | e notin evals *]);
  
  // Check the fusion law
  eta := fusion_set[3];

  // these are the tuples <a,b,S> representing a*b = S in the fusion law
  // NB don't need to check 1*a
  fus_law := [ <0, 0, {0}>, <0, eta, {eta}>, <eta, eta, {1,0}> ];
  
  return check_law(Parent(u), espace, fus_law);
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
    require gr_lm ne Identity(T): "The eigenvalue given must be non-trivially graded.";

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

intrinsic MiyamotoAutomorphism(a::AlgGenElt, chi::AlgChtrElt) -> AlgMatElt
  {
  The Miyamoto automorphism for the axis a and character chi.
  }
  // TO COMPLETE 
  
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
intrinsic IsFrobeniusForm(frob::Mtrx, A::AlgGen) -> BoolElt, Tup
  {
  Returns whether frob is a frobenius form for the algebra A.
  }
  require NumberOfRows(frob) eq NumberOfColumns(frob): "frob must be a square matrix.";
  require NumberOfRows(frob) eq Dimension(A): "frob must have the same dimension as the algebra A.";
  
  bas := Basis(A);
  if IsCommutative(A) then
    require IsSymmetric(frob): "frob is not symmetric.";
    so := forall(err){ <i,j,k> : k in [1..j], j in [1..i], i in [1..#bas] | InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j])) eq 0};
  else
    so := forall(err){ <i,j,k> : i,j,k in [1..#bas] | InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j])) eq 0};
  end if;
  if so then
    return so, _;
  else
    return so, err;
  end if;
end intrinsic;

intrinsic IsFrobeniusFormUpToIdeal(frob::Mtrx, A::AlgGen, I::.) -> BoolElt, Tup
  {
  Returns whether frob is a frobenius form for the algebra A up to an ideal I.
  }
  require NumberOfRows(frob) eq NumberOfColumns(frob): "frob must be a square matrix.";
  require NumberOfRows(frob) eq Dimension(A): "frob must have the same dimension as the algebra A.";
  
  try
    R := RingOfIntegers(BaseRing(A));
  catch e;
    require false: "Must be able to take the ring of integers of the field of the algebra.";
  end try;
  require I subset R: "I must be an ideal of the ring of integers of the algebra.";
  
  bas := Basis(A);
  if IsCommutative(A) then
    require IsSymmetric(frob): "frob is not symmetric.";
    so := forall(err){ <i,j,k> : k in [1..j], j in [1..i], i in [1..#bas] | Numerator(InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j]))) in I};
  else
    so := forall(err){ <i,j,k> : i,j,k in [1..#bas] | Numerator(InnerProduct(Vector(bas[i]*bas[j])*frob, Vector(bas[k])) - InnerProduct(Vector(bas[i])*frob, Vector(bas[k]*bas[j]))) in I};
  end if;
  if so then
    return so, _;
  else
    return so, err;
  end if;
end intrinsic;
