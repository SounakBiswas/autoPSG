BeginPackage["psgSolver`definitions`"]
Remove["psgSolver`definitions`*"]
Inv ::usage = "wrapper head to denote inverse of a matrix or group element"
gmult::usage = "wrapper head to denote that gmult[a,b] is a group multiplication of symmetry generators a and b"
Equation::usage = "Equation[a,b] is an equation head, possible useful for solving equation";
SU2::usage = "sU2 Matrix object, used for all sorts of things"
F::usage = "unit cell part of matrix"
M::usage = "translation independent part of matrix"
G::usage = "SU2[G[Tx]] is the matrix corresponding to Tx"
DeleteTrivialEquations::usage="Delete Trivial Equations"
IfFSolved::usage="check if phase parts are solved"
SubstFormInvF; SubstFormInvM; DispFormInvF ; DispFormInvM ;
MatrixInvert::usage="product invert"

(*Z2 and U1 space dependence part*)
Begin["Private`"]
(*Redefining System`CenterDot*)
ClearAll[CenterDot]
SetAttributes[CenterDot,{Flat}];
Verbatim[CenterDot][]:=1
Verbatim[CenterDot][x_]:=x;
Verbatim[CenterDot][a___,b_/;FreeQ[b,SU2],c___]:= b CenterDot[a,c];
CenterDot[c___,Times[a_,d___]/;FreeQ[a,SU2],b___]:= a CenterDot[c,d,b];
CenterDot[a_,b_+c__]:=CenterDot[a,b]+CenterDot[a,Plus[c]];
CenterDot[a_+b__,c_]:= CenterDot[a,c]+CenterDot[Plus[b],c];


MatrixInvert[1]:=1
MatrixInvert[HoldPattern[CenterDot[y__,x_]]]:= CenterDot[MatrixInvert[x],MatrixInvert[CenterDot[y]]]
MatrixInvert[SU2[x_]] := SU2[Inv[x]];
MatrixInvert[SU2[Inv[x_]]] := SU2[x];
MatrixInvert[x_/;FreeQ[x,SU2]] :=Power[x,-1];




(*Transfer space independent phases and constants to the right*)
Equation[ a_/;(Not[ SameQ [a,1] ] &&FreeQ[a,SU2] && FreeQ[a,F]),rhs_]:= Equation[1, Times[Power[a,-1], rhs]]
Equation[Times[a___, b_/;( FreeQ[b,SU2] && FreeQ[b,F]), c___],rhs_]:=      Equation[a c, Power[b,-1] rhs]

IfTrivialEquation[HoldPattern[Equation[a_,b_]]]:=SameQ[a,b];
DeleteTrivialEquations[eqSet_]:=DeleteCases[eqSet,x_/;IfTrivialEquation[x]];

IfFSolved[eqset_]:= And@@(FreeQ[HoldPattern[#],F]&/@eqset)

SubstFormInvF = {Inv[F[A_]][coord_] -> Power[F[A][coord], -1]};
SubstFormInvM = {SU2[Inv[M[A_][slat_]]] -> SU2[Inv[SU2[M[A][slat]]]]};
DispFormInvF = {Power[F[A_][coord_], -1] -> Inv[F[A]][coord]};
DispFormInvM = {SU2[Inv[SU2[M[A_][slat_]]]] -> SU2[Inv[M[A][slat]]],
SU2[Inv[SU2[Inv[M[A_][slat_]]]]] -> SU2[M[A][slat]]};


(*Property of how inverse works with phases*)
Inv[Inv[F[A_]]]:= F[A]
SU2[Inv[Inv[A_]]]:=SU2[A]
SU2[Inv[Verbatim[Times][SU2[x_],y__]]]:= Power[Times[y],-1] SU2[Inv[x]]
SU2[Inv[Verbatim[CenterDot][x_,y__]]]:= CenterDot[SU2[Inv[y]],SU2[Inv[x]]]


End[]
EndPackage[]
