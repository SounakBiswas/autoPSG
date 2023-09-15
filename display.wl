(* ::Package:: *)

BeginPackage["psgSolver`display`"]
Needs["psgSolver`definitions`"]
Needs["psgSolver`symmetryG`"]
Needs["psgSolver`su2Utils`"]
Begin["Private`"]
Format[SU2[Inv[K_[a_]]],StandardForm]:= Superscript[Subscript[K, a],-1];
Format[SU2[K_[a_]],StandardForm] :=Subscript[K, a];
Format[SU2[x_],StandardForm] := x;
Format[\[Eta][x_],StandardForm] := Subscript[\[Eta], x];
Format[F[x_],StandardForm] := Subscript[F, x];
Format[Inv[F[x_]],StandardForm] := Superscript[Subscript[F, x],-1];
(*Format[Unevaluated[Equation[lhs_,rhs_]],StandardForm] := DisplayForm[RowBox[{ToBoxes[lhs],RowBox[{"="}],ToBoxes[rhs]}]]*)
Format[HoldPattern[Equation[lhs_,rhs_]],StandardForm] :=  DisplayForm[RowBox[{ToBoxes[lhs],RowBox[{"="}],ToBoxes[rhs]}]]

End[]
EndPackage[]
