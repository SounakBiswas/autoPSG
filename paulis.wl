(* ::Package:: *)

BeginPackage["autoPSG`paulis`"]
Remove["autoPSG`paulis`*"]
Needs["autoPSG`definitions`"] 

(*CenterDot::usage = "SU2utils`CenterDot is redefined for symbolic SU2 matrix multiplicatoin"*)
paulis={SU2[\[Tau]0],SU2[\[Tau]1],SU2[\[Tau]2],SU2[\[Tau]3]};
\[Tau];
\[Tau]0::usage = "pauli mats"
\[Tau]1::usage = "pauli mats"
\[Tau]2::usage = "pauli mats"
\[Tau]3::usage = "pauli mats"
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
CenterDot [SU2[\[Tau]2],SU2[\[Tau]1]]:=-I SU2[\[Tau]3];
CenterDot [SU2[\[Tau]2],SU2[\[Tau]3]]:=I SU2[\[Tau]1];
CenterDot [SU2[\[Tau]3],SU2[\[Tau]2]]:=-I SU2[\[Tau]1];
CenterDot [SU2[\[Tau]3],SU2[\[Tau]1]]:=I SU2[\[Tau]2];
CenterDot [SU2[\[Tau]1],SU2[\[Tau]3]]:=-I SU2[\[Tau]2];
CenterDot [SU2[x_],SU2[Inv[x_]]]:=1;
CenterDot [SU2[Inv[x_]],SU2[x_]]:=1;
CenterDot[x___,SU2[\[Tau]0],y___]:=CenterDot[x,y];
(*CenterDot [Power[SU2[\[Tau]0],2]]:=1;
CenterDot [Power[SU2[\[Tau]1],2]]:=1;
CenterDot [Power[SU2[\[Tau]2],2]]:=1;
CenterDot [Power[SU2[\[Tau]3],2]]:=1;

CenterDot [Power[SU2[Inv[\[Tau]0]],2]]:=1;
CenterDot [Power[SU2[Inv[\[Tau]1]],2]]:=1;
CenterDot [Power[SU2[Inv[\[Tau]2]],2]]:=1;
CenterDot [Power[SU2[Inv[\[Tau]3]],2]]:=1;*)

Equation[SU2[\[Tau]0],rhs_]:=Equation[1,rhs]


SU2[Inv[SU2[\[Tau]0]]]=SU2[\[Tau]0]
SU2[Inv[SU2[\[Tau]1]]]=SU2[\[Tau]1]
SU2[Inv[SU2[\[Tau]2]]]=SU2[\[Tau]2]
SU2[Inv[SU2[\[Tau]3]]]=SU2[\[Tau]3]

SU2[Inv[\[Tau]0]]=SU2[\[Tau]0]
SU2[Inv[\[Tau]1]]=SU2[\[Tau]1]
SU2[Inv[\[Tau]2]]=SU2[\[Tau]2]
SU2[Inv[\[Tau]3]]=SU2[\[Tau]3]
Power[SU2[\[Tau]0],m_?EvenQ] ^:=1
Power[SU2[\[Tau]1],m_?EvenQ] ^:=1
Power[SU2[\[Tau]2],m_?EvenQ] ^:=1
Power[SU2[\[Tau]3],m_?EvenQ] ^:=1
Power[SU2[\[Tau]0],m_?OddQ] ^:=SU2[\[Tau]0]
Power[SU2[\[Tau]1],m_?OddQ] ^:=SU2[\[Tau]1]
Power[SU2[\[Tau]2],m_?OddQ] ^:=SU2[\[Tau]2]
Power[SU2[\[Tau]3],m_?OddQ] ^:=SU2[\[Tau]3]

End[]
EndPackage[]



