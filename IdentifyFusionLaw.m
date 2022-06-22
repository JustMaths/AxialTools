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
intrinsic Eigenvalues(a::AlgGenElt) -> IndxSet
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
intrinsic IsSemisimple(a::AlgGenElt) -> BoolElt, SetEnum, IndxSet
  {
  Returns whether the element semisimple.  If true also returns the set of eigenvalues and the eigenspaces.
  }
  A := Parent(a);
  
  evals := Eigenvalues(a);
  Sort(~evals, func<x,y | EigenSort(x[1], y[1])>);
  espaces := {@ Eigenspace(a, t[1]) : t in evals @};
  
  if Dimension(A) eq &+[ Dimension(U) : U in espaces] then
    return true, evals, espaces;
  else
    return false;
  end if;
end intrinsic;
/*

Identify fusion law

*/
intrinsic IdentifyFusionLaw(a::AlgGenElt: eigenvalues := Eigenvalues(a)) -> SetEnum, IndxSet, FusLaw
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
    Set_ordered := {@ t[1] : t in eigenvalues @};
  end if;
  
  Set_evals := {@ t[1] : t in evals@};
  require #evals eq #eigenvalues and Set_evals eq Set_ordered: "You have not supplied a valid list of eigenvalues.";
  // check the order
    
  if Set_evals ne Set_ordered then
    espaces := {@ espaces[Position(Set_ordered, lm)] : lm in Set_evals @};
    evals := {@ <Set_ordered[i], Dimension(espaces[i])> : i in [1..#evals] @};
  end if;
  
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

  Seq_ordered := Setseq(Set_ordered);
  f := map< FL`set -> BaseRing(Parent(a)) | i:->Seq_ordered[i], j:-> Position(Seq_ordered,j)>;
  AssignEvaluation(~FL, f);
  
  return evals, espaces, FL;
end intrinsic;
//
//
// ========== Functions to impose a fusion law ==========
//
//
intrinsic ImposeMonsterFusionLaw(a::AlgGenElt, S::SetIndx) -> AlgGen, SeqEnum
  {
  
  }
    
end intrinsic;
//
//
// ========== Find the Miyamoto automorphisms ==========
//
//
intrinsic MiyamotoInvolution(a::AlgGenElt, lm::RngElt) -> AlgMatElt
  {
  The Miyamoto involution for the axis a with respect to the eigenspace lm.  Note the fusion law must be graded and lm be in a part which is mapped to an involution.
  }
  
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
  plus := [ t : t in FLelts | t@gr eq T!1];
  minus := [ t : t in FLelts | t@gr eq T.1];
  
  plus_pos := [ Position(evals, t@eval_map) : t in plus];
  minus_pos := [ Position(evals, t@eval_map) : t in minus];
  
  ebas := [ Basis(espaces[i]) : i in plus_pos cat minus_pos];
  CoB := Matrix(&cat(ebas));
  
  F := BaseRing(A);
  dim := &+[Dimension(espaces[i]) : i in minus_pos];
  M := DiagonalJoin(IdentityMatrix(F, Dimension(A)-dim), -IdentityMatrix(F, dim));
  
  return CoB^-1*M*CoB;
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
