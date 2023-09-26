(* ::Package:: *)

BeginPackage["psgSolver`paulis`"]
Remove["psgSolver`paulis`*"]
Needs["psgSolver`definitions`"] 

(*CenterDot::usage = "SU2utils`CenterDot is redefined for symbolic SU2 matrix multiplicatoin"*)
\[Tau]={SU2[\[Tau]0],SU2[\[Tau]1],SU2[\[Tau]2],SU2[\[Tau]3]};
(*Format ::usage="Redefined Format for equation and SU2 matrices"*)

Begin["Private`"]

(*Properties of sU2 matrices*)
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


SU2[Inv[SU2[\[Tau]0]]]=SU2[\[Tau]0]
SU2[Inv[SU2[\[Tau]1]]]=SU2[\[Tau]1]
SU2[Inv[SU2[\[Tau]2]]]=SU2[\[Tau]2]
SU2[Inv[SU2[\[Tau]3]]]=SU2[\[Tau]3]

End[]
EndPackage[]



