(* ::Package:: *)
BeginPackage["psgSolver`display`"]
Needs["psgSolver`definitions`"]
Needs["psgSolver`symmetryG`"]
Needs["psgSolver`paulis`"]
Needs["psgSolver`z2Utils`"]
Begin["Private`"]

Format[ Inv[F[x_]][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Superscript[Subscript[F,x],-1], Superscript[Superscript[Subscript[F,x],slat],-1]];
head[Sequence@@coord]
]
Format[ F[x_][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Subscript[F,x], Superscript[Subscript[F,x],slat]];
head[Sequence@@coord]
]

Format[ SU2[Inv[K_[x_]]][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Superscript[Subscript[K,x],-1], Superscript[Superscript[Subscript[K,x],slat],-1]];
head[Sequence@@coord]
]

Format[ SU2[K_[x_]][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Subscript[K,x], Superscript[Subscript[K,x],slat]];
head[Sequence@@coord]
]
Format[SU2[Inv[K_[a_]]][slat_:None],StandardForm]:= 
If[MatchQ[slat,None],Superscript[Subscript[K, a],-1], Superscript[Superscript[Subscript[K, a],slat],-1]];

Format[SU2[K_[a_]][slat_:None],StandardForm] :=If[MatchQ[slat,None],Subscript[K, a],Superscript[Subscript[K, a],slat]];


(*Format[SU2[Inv[K_[a_]]][{x_,y_}],StandardForm]:= Superscript[Subscript[K, a],-1][x,y];*)
(*Format[SU2[K_[a_]][{x_,y_}],StandardForm] :=Subscript[K, a][x,y];*)
Format[SU2[Inv[K_[a_]]],StandardForm]:= Superscript[Subscript[K, a],-1];
Format[SU2[K_[a_]],StandardForm] :=Subscript[K, a];
Format[SU2[x_],StandardForm] := x;
Format[\[Eta][x_],StandardForm] := Subscript[\[Eta], x];
(*Format[F[x_],StandardForm] := Subscript[F, x];
Format[Inv[F[x_]],StandardForm] := Superscript[Subscript[F, x],-1];*)
Format[HoldPattern[Equation[lhs_,rhs_]],StandardForm] :=  DisplayForm[RowBox[{ToBoxes[lhs],RowBox[{"="}],ToBoxes[rhs]}]]


End[]
EndPackage[]
