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
head=If[MatchQ[slat,None],Superscript[Subscript[F,x],-1], Superscript[Subscript[Superscript[F,slat],x],-1]];
head[Sequence@@coord]
]
Format[ F[x_][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Subscript[F,x], Subscript[Superscript[F,slat],x]];
head[Sequence@@coord]
]

Format[ \[Theta][x_][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Subscript[\[Theta],x], Subscript[Superscript[\[Theta],slat],x]];
head[Sequence@@coord]
]

Format[SU2[\[Tau]0],StandardForm] := Subscript[\[Tau], 0];
Format[SU2[\[Tau]1],StandardForm] := Subscript[\[Tau], 1];
Format[SU2[\[Tau]2],StandardForm] := Subscript[\[Tau], 2];
Format[SU2[\[Tau]3],StandardForm] := Subscript[\[Tau], 3];

Format[ SU2[Inv[K_[x_]]][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Superscript[Subscript[K,x],-1], Superscript[Subscript[Superscript[K,slat],x],-1]];
head[Sequence@@coord]
]

Format[ SU2[K_[x_]][{a_,b_,c_:None,slat_:None}],StandardForm] := 
Module[{head,coord},
coord= If[MatchQ[c,None], {a,b}, {a,b,c}];
head=If[MatchQ[slat,None],Subscript[K,x], Subscript[Superscript[K,slat],x]];
head[Sequence@@coord]
]
Format[SU2[Inv[K_[a_][slat_:None]]],StandardForm]:= 
If[MatchQ[slat,None],Superscript[Subscript[K, a],-1], Superscript[Subscript[Superscript[K, slat],a],-1]];

Format[SU2[K_[a_][slat_:None]],StandardForm] :=If[MatchQ[slat,None],Subscript[K, a],Subscript[Superscript[K, slat],a]];


(*Format[SU2[Inv[K_[a_]]][{x_,y_}],StandardForm]:= Superscript[Subscript[K, a],-1][x,y];*)
(*Format[SU2[K_[a_]][{x_,y_}],StandardForm] :=Subscript[K, a][x,y];*)
Format[SU2[Inv[K_[a_]]],StandardForm]:= Superscript[Subscript[K, a],-1];
Format[SU2[K_[a_]],StandardForm] :=Subscript[K, a];
Format[SU2[x_],StandardForm] := x;
Format[SU2[Inv[x_]],StandardForm] := Superscript[x,-1];
Format[\[Eta][x_],StandardForm] := Subscript[\[Eta], x];
Format[\[Phi][x_],StandardForm] := Subscript[\[Phi], x];
Format[\[Theta][x_],StandardForm] := Subscript[\[Theta], x];
Format[\[ScriptN][x_],StandardForm] := Subscript[\[ScriptN], x];
Format[\[ScriptM][A_][slat_:None],StandardForm] := If[MatchQ[slat,None],Subscript[\[ScriptM], A],Subscript[Superscript[\[ScriptM], slat],A]];
Format[u12pibyk[p_], StandardForm]=  Hold[(2 Pi \[ScriptK])/p]
Format[u12pibyk[p_,k_], StandardForm]=  (2 Pi Superscript[\[ScriptK],k])/p

(*Format[F[x_],StandardForm] := Subscript[F, x];
Format[Inv[F[x_]],StandardForm] := Superscript[Subscript[F, x],-1];*)
Format[HoldPattern[Equation[lhs_,rhs_]],StandardForm] :=  DisplayForm[RowBox[{ToBoxes[lhs],RowBox[{"="}],ToBoxes[rhs]}]]
Format[HoldPattern[EquationU1[lhs_,rhs_]],StandardForm] :=  DisplayForm[RowBox[{ToBoxes[lhs],RowBox[{"="}],ToBoxes[rhs]}]]

(*gmult display*)
gmultToM[gmult[Inv[x_]]] := SU2[Inv[x]];
gmultToM[gmult[x_]] := SU2[x];
gmultToM[gmult[x_, y__]] := CenterDot[gmultToM[gmult[x]], gmultToM[gmult[y]]]
Format[gmult[x__],StandardForm]:= Equation[ gmultToM[gmult[x]], e ]

End[]
EndPackage[]
