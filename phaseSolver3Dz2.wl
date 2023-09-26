BeginPackage["psgSolver`phaseSolverPlumbing`"]
Remove["psgSolver`phaseSolver2Dz2`*"]
Needs["psgSolver`definitions`"] 
Needs["psgSolver`symmetryG`"] 
Needs["psgSolver`z2Utils`"] 
Needs["psgSolver`paulis`"] 
FAssoc; FSubstAssoc; MAssoc; ifIGGSet;
InitPSGSolver::usage="initiate solver, basic associations"
decomposeGtoFM::usage = "decompose matrices into phase part and matrix"
phaseSolverIterate ::usage = "solve for phase parts recursively"

Begin["Private`"]
phaseSolverIterate[rels0_]:=Module[
{rels1,rules0,rels2,elementaryFReductions,composedFReductions,FCompositionConstraints, etaRelationConstraints,FSubstRules},
  rules0 = DeleteCases[Join[Values[FAssoc],Values[MAssoc]],Null];
  rels1=ApplyRules[rels0,rules0];
  elementaryFReductions = Join@@(ReduceF/@rels1);
  composedFReductions= FReductions[elementaryFReductions];
  Scan[(AssociateTo[FAssoc,#->composedFReductions[#]]&),Keys[composedFReductions]];
  rels1=reduceEtas[rels1];
  If[  MatchQ[rels1,rels0],
     If[  IfFSolved[rels1],
        rels1,
        (
        rels2=Join@@(SplitEqMF/@rels1);
        rels2=substAllMsIntoAllEqs[rels2]//z2Simplify;
        FSubstRules= Join@@getFSubstitutors/@rels2;
        FSubstAssoc= Association@@ ((#->{}&)/@symGenSet);
        addToFSubstAssoc[FSubstAssoc,#]&/@FSubstRules;
        rels2=Join[rels2,solveByFSubstitutions[FSubstAssoc,#]&/@rels2//z2Simplify];
        elementaryFReductions = Join@@(ReduceF/@rels2);
        composedFReductions= FReductions[elementaryFReductions];
        Scan[(AssociateTo[FAssoc,#->composedFReductions[#]]&),Keys[composedFReductions]];
        If[MatchQ[rels1,rels2],
        "Failed",
        phaseSolverIterate[rels2]
        ]
        )
     ],
    phaseSolverIterate[rels1]
    ]
];
reduceEtas[rels_] := Module[{etaSubRules, etaConstraintEqs, newRels},
   etaConstraintEqs =
    z2Simplify[Join @@ FindRelationConstraints /@ rels];
   etaSubRules = Join @@ RelationConstraintRule /@ etaConstraintEqs;
   newRels = rels //. etaSubRules // z2Simplify;
   (FAssoc[#] =
       FAssoc[#] //. etaSubRules // z2Simplify) & /@ Keys[FAssoc];
   DeleteTrivialEquations[newRels]
];
(****************************************)
InitPSGSolver[]:=(
FAssoc=Association@@(#->(Null)&/@symGenSet);
FSubstAssoc=Association@@((#->{})&/@symGenSet);
MAssoc=Association@@(#->(Null)&/@symGenSet);
ifIGGSet=Association@@(#->False&/@symGenSet);
     MAssoc[Tx]=(SU2[M[Tx]]->SU2[\[Tau]0]); 
FAssoc[Tx]=(F[Tx][{x_,y_}]->1);
MAssoc[Ty]=(SU2[M[Ty]]->SU2[\[Tau]0]); 
FAssoc[Ty]=(F[Ty][{x_,y_}]-> \[Eta][1]^x);
nrel=Length[SGset];
Null)
(****************************************)
decomposeGtoFM[expr_]:= expr/.{SU2[G[A_]][{x_,y_}]-> F[A][{x,y}]SU2[M[A]],SU2[Inv[G[A_]]][{x_,y_}]-> Inv[F[A]][{x,y}] SU2[Inv[M[A]]]};
(****************************************)
ApplyRules[relations_,subrules_]:= (relations/.SubstFormInvF/.SubstFormInvM/.subrules/.DispFormInvF/.DispFormInvM)//z2Simplify//DeleteTrivialEquations;
(******************************************)

(*Solve First Order 2D DEq*)

IfFirstOrderDEq2D[HoldPattern[Equation[Times[ Inv[F[B_]][{x1_,y1_,z1_,s1_}], F[A_][{x2_,y2_,z2_,s2_}]],rhs_]]]:=
With[{k1=x2-x1, k2=y2-y1,k3=z2-z1},
If[((NumericQ[k1]&&Abs[k1]<=1) && (NumericQ[k2] && Abs[k2]<= 1 )&& (NumericQ[k2] && Abs[k2]<= 1 )) &&(Abs[k1]+Abs[k2]+Abs[k3]==1)&&SameQ[A,B]&&SameQ[s1,s2],
True,
False]];
IfFirstOrderDEq2D[expr_]:=False;

FirstOrderDEqSolve2D[ HoldPattern[Equation[Inv[F[A_]][{x1_,y1_,z1_,s_}] F[A_][{x2_,y2_,z2_,s_}], p_]]]:= 
Module[{k1=x2-x1, k2=y2-y1, k3=z2-z1,expr,a,b,c,rules},
rules={};
(If[MemberQ[x1,#,{Infinity}],Append[rules,{#->a}];];&)/@{x,y,z};
(If[MemberQ[y1,#,{Infinity}],Append[rules,{#->b}];];&)/@{x,y,z};
(If[MemberQ[z1,#,{Infinity}],Append[rules,{#->c}];];&)/@{x,y,z};
expr=p//.rules;
If[Abs[k2]==1,
 {Rule@@{F[A][{a_,b_,c_}], F[A][{a,0,c}]expr^b}},
If[Abs[k1]==1 ,
{Rule@@{F[A][{a_,b_,c_}], F[A][{0,b,c}]expr^a}},
If[Abs[k3]==1 ,
{Rule@@{F[A][{a_,b_,c_}], F[A][{a,b,c}]expr^c}}]]]];

ReduceF[HoldPattern[x_Equation]]:= 
If[IfFirstOrderDEq2D[x],
FirstOrderDEqSolve2D[x],
Nothing]

(*First Order solutions*)
FilterReductions[F[A_],reductions_]:=Cases[reductions,HoldPattern[Rule[F[A][coord_],x___]]];

FReductions[reductions_]:=Module[{tempList},
tempList=
(With[{reds=FilterReductions[F[#],reductions]}, 
If[Length[reds]!=0, 
If[FreeQ[Fold[ReplaceAll,F[#][{x,y}],reds],F[#][coord_/;(MemberQ[coord,x|y])]],
#->(F[#][{x_,y_}]->Fold[ReplaceAll,F[#][{x,y}],reds]),Nothing],
Nothing]]& )/@symGenSet /.{F[A_][{0,0,0,s_}]->1,F[A_][{0,0,None,s_}]->1};
Association[tempList]
]

(**** Eta Relations***)
IsolateRelationExponent[expr_,a_]:=Module[
{cases,cond},
cases= Cases[expr,(Power[__,a]|Power[__,HoldPattern[Plus[___,a,___]]])];
cond = Times@@cases/.{Power[b_,__]->b};
If[Length[cases]!=0,
Equation[cond,1],
Nothing]
]


FindRelationConstraints[HoldPattern[Equation[lhs_,rhs_]]]:= 
If[FreeQ[lhs,x]&&FreeQ[lhs,y]&&Not[FreeQ[rhs,x] && FreeQ[rhs,y]],
{IsolateRelationExponent[rhs,x],
IsolateRelationExponent[rhs,y],
IsolateRelationExponent[rhs,x y]},
If[SameQ[lhs,1],
{Equation[1,rhs]},
Nothing
]
]
RelationConstraintRule[HoldPattern[Equation[1,Times[x_,y__]]]]:= {x->Times[y]};
RelationConstraintRule[HoldPattern[Equation[1,x_]]] := {x->1};


(*****Further substitutions by FM separation***)

SplitEqMF[HoldPattern[Equation[Verbatim[Times][x___, Verbatim[CenterDot][y__] ,z___],lhs_]]]:= (nrel=nrel+1;List[Equation[Times[x,z],\[Eta][nrel] lhs],Equation[ CenterDot[y],\[Eta][nrel]]]);
SplitEqMF[HoldPattern[Equation[lhs_,rhs_]]]:= List[Equation[lhs,rhs]];

substMIntoEq[HoldPattern[Equation[Verbatim[CenterDot][x__],rhs1_]],HoldPattern[Equation[Verbatim[CenterDot][y___,x__,z___],rhs2_]]]:= Equation[rhs1 CenterDot[y,z],rhs2]; 
substMIntoEq[HoldPattern[Equation[lhs_,rhs_]],HoldPattern[Equation[lhs2_,rhs2_]]]:=Equation[lhs2,rhs2]
substMIntoAllEqs[rels_,relNum_]:=Module[{newRels},
newRels= substMIntoEq[rels[[relNum]],#]&/@rels; 
newRels[[relNum]]=rels[[relNum]];
newRels];
substAllMsIntoAllEqs[rels_]:= Fold[substMIntoAllEqs[#1,#2]&,rels,Range[Length[rels]]];
IfFOrInvF[a_]:=MatchQ[a,F[A_]] || MatchQ[a,Inv[F[A_]]];
(*Again assume that the symmetries don't take a site at [x,y] to [x+y,x-y]*)
getFSubstitutors[HoldPattern[Equation[Times[(t1_?IfFOrInvF)[{x1_,y1_}],(t2_?IfFOrInvF)[{x2_,y2_}]] ,rhs_]]]:= 
Module[{x1n,y1n,x2n,y2n,rule1,rule2,rule3,rule4,svar,subrules},
svar[Plus[Times[x, m_:1],k_:0]]:=a;
svar[Plus[Times[y, m_:1],k_:0]]:=b;
subrules[Plus[Times[x, m_:1],k_:0]]:= x->m^-1 (a-k);
subrules[Plus[Times[y, m_:1],k_:0]]:= y->m^-1 (b-k);
x2n=x2/.{subrules[x1],subrules[y1]};
y2n=y2/.{subrules[x1],subrules[y1]};
x1n=x1/.{subrules[x2],subrules[y2]};
y1n=y1/.{subrules[x2],subrules[y2]};
If[MatchQ[t1,Inv[A_]],
 rule1=Inv[ t1][{(Pattern[#,_]&)[svar[x1]],(Pattern[#,_]&)[svar[y1]]}]-> ( t2[{#1 ,#2}]rhs^-1)&[x2n,y2n],
rule1=t1[{(Pattern[#,_]&)[svar[x1]],(Pattern[#,_]&)[svar[y1]]}]-> ( Inv[t2][{#1 ,#2}]rhs)&[x2n,y2n]];
If[MatchQ[t2,Inv[A_]],
rule2= Inv[t2][{(Pattern[#,_]&)[svar[x2]],(Pattern[#,_]&)[svar[y2]]}]->  ( t1[{#1 ,#2}]rhs^-1)&[x1n,y1n],
rule2= t2[{(Pattern[#,_]&)[svar[x2]],(Pattern[#,_]&)[svar[y2]]}]->  ( Inv[t1][{#1 ,#2}]rhs)&[x1n,y1n]];
;
List[rule1,rule2]
]

getFSubstitutors[HoldPattern[x__Equation]]:=Nothing
substituteFRule[F1_,F2_,rhs_,rule_,subpart_]:=Module[{newF,newEq},
Which[subpart==1,
(newF=F1//.SubstFormInvF/.rule//.DispFormInvF;
newEq=Equation[Times[newF,F2],rhs];),
subpart==2,
(newF=F2//.SubstFormInvF/.rule//.DispFormInvF;
newEq=Equation[Times[F1,newF],rhs];)
];
If[IfFirstOrderDEq2D[newEq],
newEq,
Nothing
]]

solveByFSubstitutions[FSubstAssoc_,HoldPattern[eq:Equation[Times[(F1:F[A_][coord1_]|Inv[F[A_]][coord1_]),(F2:F[B_][coord2_]|Inv[F[B_]][coord2_])],rhs_]]]:=Module[
{newList},
newList=((substituteFRule[F1,F2,rhs,#,1]&)/@FSubstAssoc[A]);
If[Length[newList]!=0,
First[newList],
If[Not[SameQ[A,B]],
(newList=(substituteFRule[F1,F2,rhs,#,2]&)/@FSubstAssoc[B];
If[Length[newList]!=0 && Not[SameQ[A,B]],
First[newList],
Nothing]),
Nothing]
]]
solveByFSubstitutions[FSubstAssoc_,HoldPattern[eq_Equation]]:=Nothing;
substFIntoEq[HoldPattern[eqi:Equation[Times[(F1i:F[Ai_][coord1i_]|Inv[F[Ai_]][coord1i_]),(F2i:F[Bi_][coord2i_]|Inv[F[Bi_]][coord2i_])],rhsi_]],HoldPattern[eqj:Equation[Times[(F1j:F[Aj_][coord1j_]|Inv[F[Aj_]][coord1j_]),(F2j:F[Bj_][coord2j_]|Inv[F[Bj_]][coord2j_])],rhsj_]]]:=Module[{newList,substitutors},
substitutors=getFSubstitutors[eqi];
newList=((substituteFRule[F1j,F2j,rhsj,#,1]&)/@substitutors);
If[Length[newList]!=0,
First[newList],
eqj]
]

SetAttributes[addToFSubstAssoc,HoldFirst];
addToFSubstAssoc[substAssoc_,rule:Rule[F[A_][{x_,y_}],rhs_]]:=(AppendTo[substAssoc[A],rule];)
End[]

EndPackage[]
