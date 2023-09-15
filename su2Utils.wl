(* ::Package:: *)

BeginPackage["psgSolver`su2Utils`"]
Remove["psgSolver`su2Utils`*"]
Needs["psgSolver`definitions`"] 
Needs[ "psgSolver`symmetryG`"]

(*CenterDot::usage = "SU2utils`CenterDot is redefined for symbolic SU2 matrix multiplicatoin"*)
SU2::usage = "Matrix object, used for all sorts of things"
F::usage = "unit cell part of matrix"
M::usage = "translation independent part of matrix"
ToMatrixExp::usage= "ToMatrixExp[gmult[a,b,c]] converts a SG relator to a symbolic matrix product Ga\[CenterDot]Gb\[CenterDot]Gc"
expGI::usage= "Matrix Symbol from Group element symbol"
expG::usage= "Matrix symbol from Group element symbol"
MatrixRelations::usage= "MatrixRelations[sgset] gives the set of psg equations from the symmetry group presentation"
Equation::usage = "Equation[a,b] is an equation head, possible useful for solving equation";
\[Tau]={SU2[\[Tau]0],SU2[\[Tau]1],SU2[\[Tau]2],SU2[\[Tau]3]};
G::usage = "SU2[G[Tx]] is the matrix corresponding to Tx"
\[Eta]::usage = "Z2 phases"
(*Format ::usage="Redefined Format for equation and SU2 matrices"*)

Begin["Private`"]
(*Redefining System`CenterDot*)
ClearAll[CenterDot]
SetAttributes[CenterDot,{Flat}];
Verbatim[CenterDot][]:=1
Verbatim[CenterDot][x_]:=x;
Verbatim[CenterDot][a___,b_/;FreeQ[b,SU2],c___]:= b CenterDot[a,c];
CenterDot[c___,Times[a_,d___]/;FreeQ[a,SU2],b___]:= a CenterDot[c,d,b];
CenterDot[a__,b__+c__]:=CenterDot[a,b]+CenterDot[a,c];
CenterDot[a__+b__,c__]:= CenterDot[a,c]+CenterDot[b,c];

CenterDot [SU2[\[Tau]0],SU2[\[Tau]0]]:=1;
CenterDot [SU2[\[Tau]1],SU2[\[Tau]1]]:=1;
CenterDot [SU2[\[Tau]2],SU2[\[Tau]2]]:=1;
CenterDot [SU2[\[Tau]3],SU2[\[Tau]3]]:=1;
CenterDot [SU2[\[Tau]1],SU2[\[Tau]0]]:=SU2[\[Tau]1];
CenterDot [SU2[\[Tau]2],SU2[\[Tau]0]]:=SU2[\[Tau]2];
CenterDot [SU2[\[Tau]3],SU2[\[Tau]0]]:=SU2[\[Tau]2];
CenterDot [SU2[\[Tau]1],SU2[\[Tau]2]]:=I SU2[\[Tau]3];
CenterDot [SU2[\[Tau]2],SU2[\[Tau]3]]:=I SU2[\[Tau]1];
CenterDot [SU2[\[Tau]3],SU2[\[Tau]1]]:=I SU2[\[Tau]2];
CenterDot [SU2[x_],SU2[Inv[x_]]]:=1;
CenterDot [SU2[Inv[x_]],SU2[x_]]:=1;
CenterDot[x___,SU2[\[Tau]0],y___]:=CenterDot[x,y];



(*CenterDot[x__]:=Which[x,Sequence[\[Tau]0,\[Tau]0],1]*)


(*Converts a equation with group products, gmult, into a equation object the solver can work with*)
(*expG[a_]:=SU2[ToExpression["G"<>ToString[a]]]*)
(*expG[a_]:=SU2[ToExpression["G"<>ToString[a]]]*)
(*expGI[a_]:= SU2[Inv[ToExpression["G"<>ToString[a]]]];*)
expG[a_]:=SU2[G[a]];
expGI[a_]:= SU2[Inv[G[a]]];

ToMatrixExp[gmult[Inv[a_]],coord_:{x,y}]:=expGI[a][a[coord]];
ToMatrixExp[gmult[a_],coord_:{x,y}]:= expG[a][coord];
ToMatrixExp[gmult[Inv[a_],b__], coord_:{x,y}]:=expGI[a][a[coord]]\[CenterDot]ToMatrixExp[gmult[b],a[coord]];  
ToMatrixExp[gmult[a_,b__], coord_:{x,y}]:=expG[a][coord]\[CenterDot]ToMatrixExp[gmult[b],Inv[a][coord]];

(* Converts a symmetry group relator to a Equation[] Object*)
MatrixRelations[rels_]:=ReleaseHold[(Hold[Equation[ToMatrixExp[rels[[#]]], \[Eta][#]]])&/@Range[Length[rels]]];

(*Transfer space independent phases and constants to the right*)
Equation[ a_/;(Not[ SameQ [a,1] ] &&FreeQ[a,SU2] && FreeQ[a,F]),rhs_]:= Equation[1, Times[Power[a,-1], rhs]]
Equation[Times[a___, b_/;( FreeQ[b,SU2] && FreeQ[b,F]), c___],rhs_]:=      Equation[a c, Power[b,-1] rhs]



(*Property of how inverse works with phases*)
(*Inv[F[A_]][coord_]:=Power[F[A][coord],-1]*)
SU2[Inv[SU2[\[Tau]0]]]=SU2[\[Tau]0]
SU2[Inv[SU2[\[Tau]1]]]=SU2[\[Tau]1]
SU2[Inv[SU2[\[Tau]2]]]=SU2[\[Tau]2]
SU2[Inv[SU2[\[Tau]3]]]=SU2[\[Tau]3]

End[]
EndPackage[]



