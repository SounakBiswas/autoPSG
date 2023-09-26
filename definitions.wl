BeginPackage["psgSolver`definitions`"]
Remove["psgSolver`definitions`*"]
Inv ::usage = "wrapper head to denote inverse of a matrix or group element"
gmult::usage = "wrapper head to denote that gmult[a,b] is a group multiplication of symmetry generators a and b"
Equation::usage = "Equation[a,b] is an equation head, possible useful for solving equation";
SU2::usage = "sU2 Matrix object, used for all sorts of things"
F::usage = "unit cell part of matrix"
M::usage = "translation independent part of matrix"
G::usage = "SU2[G[Tx]] is the matrix corresponding to Tx"
(*Z2 and U1 space dependence part*)
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

(*Transfer space independent phases and constants to the right*)
Equation[ a_/;(Not[ SameQ [a,1] ] &&FreeQ[a,SU2] && FreeQ[a,F]),rhs_]:= Equation[1, Times[Power[a,-1], rhs]]
Equation[Times[a___, b_/;( FreeQ[b,SU2] && FreeQ[b,F]), c___],rhs_]:=      Equation[a c, Power[b,-1] rhs]



(*Property of how inverse works with phases*)
Inv[Inv[F[A_]]]:= F[A]
SU2[Inv[Inv[A_]]]:=SU2[A]
End[]
EndPackage[]
