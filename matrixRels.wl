BeginPackage["psgSolver`matrixRels`"]
Remove["psgSolver`matrixRels`*"]
Needs["psgSolver`definitions`"]
Needs["psgSolver`symmetryG`"]
Needs["psgSolver`z2Utils`"]

MatrixRelations::usage= "MatrixRelations[sgset] gives the set of psg equations from the symmetry group presentation"

Begin["Private`"]
expG[a_]:=SU2[G[a]];
expGI[a_]:= SU2[Inv[G[a]]];

ToMatrixExp[gmult[Inv[a_]],coord_:{x,y,z,s}]:=expGI[a][a[coord]];
ToMatrixExp[gmult[a_],coord_:{x,y,z,s}]:= expG[a][coord];
ToMatrixExp[gmult[Inv[a_],b__], coord_:{x,y,z,s}]:=expGI[a][a[coord]]\[CenterDot]ToMatrixExp[gmult[b],a[coord]];  
ToMatrixExp[gmult[a_,b__], coord_:{x,y,z,s}]:=expG[a][coord]\[CenterDot]ToMatrixExp[gmult[b],Inv[a][coord]];

(* Converts a symmetry group relator to a Equation[] Object*)
(*MatrixRelations[rels_]:=ReleaseHold[(Hold[Equation[ToMatrixExp[rels[[#]]], \[Eta][#]]])&/@Range[Length[rels]]];*)
MatrixRelationsSlat[rels_,slat_]:=ReleaseHold[( Hold[Equation[ToMatrixExp[rels[[#]],{x,y,None,slat}], \[Eta][#]]] )&/@Range[Length[rels]]];
MatrixRelations[rels_]:=Join@@( MatrixRelationsSlat[rels,#]&/@slatList)


End[]
EndPackage[]
