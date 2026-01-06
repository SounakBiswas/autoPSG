(* ::Package:: *)

BeginPackage["autoPSG`definitions`"]
Remove["autoPSG`definitions`*"]
Inv ::usage = "wrapper head to denote inverse of a matrix or group element"
gmult::usage = "wrapper head to denote that gmult[a,b] is a group multiplication of symmetry generators a and b"
Equation::usage = "Equation[a,b] is an equation head, possible useful for solving equation";
EquationU1::usage = "Equation[a,b] is an equation head, possible useful for solving equation";
SU2::usage = "sU2 Matrix object, used for all sorts of things"
F::usage = "unit cell part of matrix"
M::usage = "unit-cell independent part of matrix"
G::usage = "SU2[G[Tx]] is the matrix corresponding to Tx"
\[ScriptM]::usage = "unit-cell independent part of matrix"
\[ScriptN]::usage = "index for U1"
\[ScriptK]::usage = "phase integer"
\[Theta]::usage = "SU2[G[Tx]] is the matrix corresponding to Tx"
DeleteTrivialEquations::usage="Delete Trivial Equations"
IfFSolved::usage="check if phase parts are solved"
SubstFormInvF; SubstFormInvM; DispFormInvF ; DispFormInvM ;
matrixInvert::usage="product invert"
e::usage ="group identity"
u12pibyk::usage = "u1 phase mod 2 pi"

(*general things needed in all solvers, perhaps move somewhere else later*)
FAssoc; FSubstAssoc; MAssoc; ifIGGSet; iggAssoc; 
phiAssoc;etaAssoc;
(*only for U1*)
NAssoc;

IGG::usage="variable, u1 or z2"

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
u12pibyk/: Times[ p_,u12pibyk[k_,y_]]:=Mod[p,k] u12pibyk[k,y] /;IntegerQ[p]&& p!=Mod[p,k]
u12pibyk/: Times[x___, p_,u12pibyk[k_]]:=0 /; Divisible[p,k]
u12pibyk/: Times[x___, p_,u12pibyk[k_,y_]]:=0 /; Divisible[p,k]
u12pibyk/: Times[x___, p_,u12pibyk[k_,y_]]:=0 /; Divisible[p,k]
u12pibyk/: Times[x___, p_,u12pibyk[k_,y_]]:=0 /; Divisible[p,k]
u12pibyk[k_?Negative,p_]:=-u12pibyk[-k,p];
u12pibyk[1,p_]:=0;


matrixInvert[1]:=1
matrixInvert[HoldPattern[CenterDot[y__,x_]]]:= CenterDot[matrixInvert[x],matrixInvert[CenterDot[y]]]
matrixInvert[SU2[x_]] := SU2[Inv[x]];
matrixInvert[SU2[Inv[x_]]] := SU2[x];
matrixInvert[x_/;FreeQ[x,SU2]] :=Power[x,-1];




(*Transfer space independent phases and constants to the right*)
(*Equation[ a_/;(Not[ SameQ [a,1] ] &&FreeQ[a,SU2] && FreeQ[a,F]),rhs_]:= Equation[1, Times[Power[a,-1], rhs]]
Equation[Times[a___, b_/;( FreeQ[b,SU2] && FreeQ[b,F]), c___],rhs_]:=      Equation[a c, Power[b,-1] rhs]*)

Equation[ a_/;(Not[ SameQ [a,1] ] &&FreeQ[a,SU2] && FreeQ[a,F] &&FreeQ[a,M]),rhs_]:= Equation[1, Times[Power[a,-1], rhs]]
Equation[Times[a___, b_/;( FreeQ[b,SU2] && FreeQ[b,F] && FreeQ[b,M]), c___],rhs_]:=      Equation[a c, Power[b,-1] rhs]

EquationU1[ a_/;(Not[ SameQ [a,0] ] &&FreeQ[a,\[ScriptM]] && FreeQ[a,\[Theta]]),rhs_]:= EquationU1[0, rhs-a]
EquationU1[Verbatim[Plus][a___, b_/;( FreeQ[b,\[Theta] ]&& FreeQ[b,\[ScriptM]]), c___],rhs_]:=      EquationU1[a+ c,  rhs-b]
(*HoldPattern[EquationU1[ Verbatim[Times][k_,term_],rhs_]]/;Not[k==1]&&FreeQ[k,\[Theta]] &&FreeQ[k,\[ScriptM]]:=   EquationU1[term,  Power[k,-1]*rhs] ;*)
(*EquationU1[Verbatim[Times][terms_ ,k_],rhs_]/;k!=1 &&FreeQ[k,\[ScriptM]] &&FreeQ[k,\[Theta]]:=  EquationU1[terms,  Power[k,-1]*rhs] *)
(*EquationU1[ Verbatim[Times][k_ ,term_],rhs_]/;k!=1 &&FreeQ[k,\[ScriptM]] &&FreeQ[k,\[Theta]]:=  EquationU1[term,  Power[k,-1]*rhs] *)
CancelInverses[HoldPattern[Equation[ CenterDot[SU2[x_],y___,SU2[Inv[x_]]],rhs_]]] := Equation[CenterDot[y],rhs];

IfTrivialEquation[HoldPattern[Equation[a_,b_]]]:=SameQ[a,b];
IfTrivialEquation[HoldPattern[EquationU1[a_,b_]]]:=SameQ[a,b];
DeleteTrivialEquations[eqSet_]:=DeleteCases[eqSet,x_/;IfTrivialEquation[x]];

IfFSolved[eqset_]:= And@@(FreeQ[HoldPattern[#],F]&/@eqset)

SubstFormInvF = {Inv[F[A_]][coord_] -> Power[F[A][coord], -1]};
SubstFormInvM = {SU2[Inv[M[A_][slat_]]] -> SU2[Inv[SU2[M[A][slat]]]]};
DispFormInvF = {Power[F[A_][coord_], -1] -> Inv[F[A]][coord]};
DispFormInvM = {SU2[Inv[SU2[M[A_][slat_]]]] -> SU2[Inv[M[A][slat]]],
SU2[Inv[SU2[Inv[M[A_][slat_]]]]] -> SU2[M[A][slat]]};
SU2[Inv[SU2[M[A_][slat_]]]] -> SU2[Inv[M[A][slat]]];


\[AliasDelimiter]


(*Property of how inverse works with phases*)
Inv[Inv[F[A_]]]:= F[A]
SU2[Inv[Inv[A_]]]:=SU2[A]
SU2[Inv[Verbatim[Times][SU2[x_],y__]]]:= Power[Times[y],-1] SU2[Inv[x]]
SU2[Verbatim[Times][SU2[x_],y__]]:= Times[y] SU2[x]
SU2[Inv[Verbatim[Times][CenterDot[x__],y__]]]:= Power[Times[y],-1] SU2[Inv[CenterDot[x]]]
SU2[Inv[Verbatim[CenterDot][x_,y__]]]:= CenterDot[SU2[Inv[CenterDot[y]]],SU2[Inv[x]]]
CenterDot[pref___, Power[E, Complex[0,x_] (pref1_:1) SU2[k_]], Power[E,Complex[0,y_] (pref2_:1) SU2[k_]], suff___]:= CenterDot[pref, Exp[ Complex[0,1]*(x pref1 + y pref2) SU2[k]], suff] 

(*power for SU2 matrices*)
Unprotect[Power]
Power[ x_  SU2[m_],k_]/;FreeQ[x,SU2] := x^k Power[SU2[m],k]
Power[Power[SU2[k_],m_],n_] := Power[SU2[k],m n]
Protect[Power]
CenterDot[ pref___,Power[SU2[m_],p_],Power[SU2[m_],q_],suff___]:=CenterDot[pref, Power[SU2[m],p+q],suff]





End[]
EndPackage[]
