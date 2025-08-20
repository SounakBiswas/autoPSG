(* ::Package:: *)

BeginPackage["psgSolver`phaseSolverU1`"]
Remove["psgSolver`phaseSolverU1`*"]
Needs["psgSolver`definitions`"] 
Needs["psgSolver`symmetryG`"] 
Needs["psgSolver`z2Utils`"] 
Needs["psgSolver`paulis`"] 

initPSGSolverU1::usage ="initiate solver, basic associations"
decomposeGtoFMU1::usage = "decompose matrices into phase part and matrix for U1"
phaseSolverIterateU1::usage = ""
moveTauOnes::usage = "move tau1s to the left"
seperateMinusIotas;
simplifyNs;
performNSubstitutions::usage = "simplify Ns"
ConvertToU1Eqs::usage = "convert to U1 equations"
ReduceFU1;
FReductionsU1;
ApplyRulesU1;
IfFirstOrderDEq2DU1;
FirstOrderDeqSolve2DU1;
reducePhis;
RelationConstraintRuleU1;
FindRelationConstraintsU1;
IsolateRelationExponentU1;
FirstOrderDEqSolve2DU1;
npidx;

Begin["Private`"]
npidx=0;
nrel=Length[SGSet];


(****************************************)
ApplyRulesU1[rels_,rules_]:= rels//.rules/.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]}//DeleteTrivialEquations;
initPSGSolverU1[]:=(
   FSubstAssoc=Association@@((#->{})&/@symGenSet);

   ifIGGSet=Association@@(#->False&/@symGenSet);

   FAssoc = Association @@ (({#1, #2} ->Null) &) @@@ (Distribute[{symGenSet, slatList}, List]) ;
   MAssoc = Association @@ (({#1, #2} ->Null) &) @@@ (Distribute[{symGenSet, slatList}, List]);
   NAssoc=Association@@(#->(Null)&/@symGenSet);
   phiAssoc=Association[];
   (MAssoc[{Tx,#}]=(\[ScriptM][Tx][#]->0);&)/@slatList; 
   (MAssoc[{Ty,#}]=(\[ScriptM][Ty][#]->0);&)/@slatList; 
   If[Not[twoDim],
     (MAssoc[{Tz,#}]=(\[ScriptM][Tz][#]->0);&)/@slatList; 
   ];
   If[twoDim,
      ( ( FAssoc[{Tx,#}]=(\[Theta][Tx][{x_,y_,None,#}]->0); &)/@slatList;
        ( FAssoc[{Ty,#}]=(\[Theta][Ty][{x_,y_,None,#}]-> \[Phi][1]x ); &)/@slatList;
       ),
   
      ( (  FAssoc[{Tx,#}]=(\[Theta][Tx][{x_,y_,z_,#}]->0); &)/@slatList;
        (  FAssoc[{Ty,#}]=(\[Theta][Ty][{x_,y_,z_,#}]-> ExpandAll[-\[Phi][1]x]); &)/@slatList;
        (  FAssoc[{Tz,#}]=(\[Theta][Tz][{x_,y_,z_,#}]-> ExpandAll[-\[Phi][2]y +\[Phi][3]x]); &)/@slatList;
       )
   ]
)

ConvertToU1Eqs[rels_]:=Module[{rules},
rules= {HoldPattern[Equation[Power[E,Complex[0,1] SU2[\[Tau]3] terms1_], Power[E, Complex[0,1] SU2[\[Tau]3] terms2_ ] ]]:>EquationU1[ terms1,  terms2],
HoldPattern[Equation[1, Power[E,Complex[0,1] SU2[\[Tau]3] terms2_]]]:>EquationU1[0, terms2],
HoldPattern[Equation[1, Times[-1,Power[E,Complex[0,1] SU2[\[Tau]3] terms2_]]]]:>EquationU1[0,  -Pi+ terms2]};
rels//.rules
]

(****************************************)
decomposeGtoFMU1[expr_]:= expr/.{SU2[G[A_]][{x_,y_,z_,s_}]-> CenterDot[(I SU2[\[Tau]1])^(\[ScriptN][A]),Exp[ I SU2[\[Tau]3] \[Theta][A][{x,y,z,s}] ] , Exp[I SU2[\[Tau]3] \[ScriptM][A][s] ]],
SU2[Inv[G[A_]]][{x_,y_,z_,s_}]-> CenterDot[Exp[-I SU2[\[Tau]3] \[Theta][A][{x,y,z,s}]], Exp[-I SU2[\[Tau]3] \[ScriptM][A][s] ],(-I SU2[\[Tau]1])^(\[ScriptN][A])]};

phaseSolverIterateU1[rels0_]:=Module[
{rels1,rules0,rels2,elementaryFReductions,composedFReductions,FCompositionConstraints, etaRelationConstraints,FSubstRules},
  rules0 = DeleteCases[Join[Values[FAssoc],Values[MAssoc]],Null];
  rels1=ApplyRulesU1[rels0,rules0];
  (*Print["Applied:"];
  Print[Column[rels1]];*)
  elementaryFReductions = Join@@(ReduceFU1/@rels1);
  composedFReductions= FReductionsU1[elementaryFReductions];
  Scan[(AssociateTo[FAssoc,#->composedFReductions[#]]&),Keys[composedFReductions]];
  rels1=FixedPoint[reducePhis,rels1];
  If[  MatchQ[rels1,rels0],
     If[  IfFSolved[rels1],
        rels1,
        (*(
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
        )*)
        "Failed"
     ],
    phaseSolverIterateU1[rels1]
    ]
];
moveTauOnes= HoldPattern[
   CenterDot[a___,
    Power[E, Complex[0, x_] m_ SU2[\[Tau]3]], (SU2[\[Tau]1])^(k_),
    b___]] :> CenterDot[a, ( SU2[\[Tau]1])^k,
   Exp[Complex[0, x] (-1)^k m SU2[\[Tau]3]], b];

SeparatePowersTau =
With[{VPower=Verbatim[Power],VPlus=Verbatim[Plus],VTimes=Verbatim[Times]},
{ VPower[a__,VPlus[b__]]:>Inactive[Times]@@((Power[a,#]&)/@List[b])}];

killEvenPowers={Power[SU2[\[Tau]1],k_?EvenQ \[ScriptN][A_]] -> 1,Power[SU2[\[Tau]1],k_?OddQ \[ScriptN][A_]] -> Power[SU2[\[Tau]1], \[ScriptN][A]]};

simplifyNs[exp_]:=  exp//.SeparatePowersTau//.killEvenPowers//.{Inactive[Times]-> Times}

seperateMinusIotas={Complex[0,x_?Negative]^y_ -> (-1)^y Complex[0,-x]^y};

updateNAssoc[A_,subRule_]:=
  Module[{newRHS,oldRule},
    oldRule=NAssoc[A];
    If[Not[MatchQ[oldRule,Null]],
      (newRHS=oldRule[[2]]//.{subRule};
       NAssoc[A]=Rule[oldRule[[1]],newRHS];)
    ]
  ];

getNSubstitutor[HoldPattern[Equation[CenterDot[Power[SU2[\[Tau]1],Plus[\[ScriptN][A_],x_:0]],others___],rhs_]]]:= Module[{subRule},subRule=(\[ScriptN][A] -> -x); NAssoc[A]=subRule;subRule]

getNSubstitutor[HoldPattern[Equation[CenterDot[Power[SU2[\[Tau]1],Plus[-\[ScriptN][A_],x_:0]],others___],rhs_]]]:= Module[{subRule},subRule=(\[ScriptN][A] -> x); NAssoc[A]=subRule;subRule]
getNSubstitutor[anythingElse_Equation]:= Nothing;

substN[eqSet_,eqno_]:=
  Module[{eq,subRule,newEqSet},
    eq= eqSet[[eqno]];
    subRule= getNSubstitutor[eq];
    If[Not[MatchQ[subRule,Nothing]],
       (newEqSet=eqSet//.{subRule};
       (updateNAssoc[#1,subRule]&)/@symGenSet;
        newEqSet),
      eqSet
    ]
  ];
performNSubstitutions[eqSet_]:= Fold[substN,eqSet,Range[1,Length[eqSet]]];

IfFirstOrderDEq2DU1[HoldPattern[EquationU1[(r1_:1)\[Theta][A_][{x1_,y1_,z1_,s1_}]+(r2_:1)\[Theta][B_][{x2_,y2_,z2_,s2_}],rhs_]]]:=
With[{k1=x2-x1, k2=y2-y1,k3=z2-z1},
If[((NumericQ[k1]&&Abs[k1]<=1) && (NumericQ[k2] && Abs[k2]<= 1 )&& (NumericQ[k3] && Abs[k3]<= 1 )) &&(Abs[k1]+Abs[k2]+Abs[k3]==1)&&SameQ[A,B]&&SameQ[s1,s2],
True,
False]];
IfFirstOrderDEq2DU1[expr_]:=False;

FirstOrderDEqSolve2DU1[ HoldPattern[EquationU1[(r1_:1)\[Theta][A_][{x1_,y1_,z1_,s_}]+(r2_:1)\[Theta][B_][{x2_,y2_,z2_,s_}],rhs_]]]:= 
Module[{k1=x2-x1, k2=y2-y1, k3=z2-z1,expr,a,b,c,rules},
rules={};
(If[MemberQ[x1,#,{0,Infinity}],AppendTo[rules,#->a];];&)/@{x,y,z};
(If[MemberQ[y1,#,{0,Infinity}],AppendTo[rules,#->b];];&)/@{x,y,z};
(If[MemberQ[z1,#,{0,Infinity}],AppendTo[rules,#->c];];&)/@{x,y,z};
expr=rhs//.rules;
If[Abs[k1]==1 &&(r2*r1==-1),
{Rule@@{\[Theta][A][{a_,b_,c_,s}], \[Theta][A][{0,b,c,s}]+k1*r2*a expr}},
If[Abs[k2]==1 &&(r2*r1==-1),
 {Rule@@{\[Theta][A][{a_,b_,c_,s}], \[Theta][A][{a,0,c,s}]+k2*r2*b expr}},
If[Abs[k3]==1 &&(r2*r1==-1),
{Rule@@{\[Theta][A][{a_,b_,c_,s}], \[Theta][A][{a,b,0,s}]+k3*r2*c expr}},

If[Abs[k1]==1 &&(r2*r1==1), nrel=nrel+1;
{Rule@@{\[Theta][A][{a_,b_,c_,s}], \[Theta][A][{0,b,c,s}]+r2 Power[-1,a]\[Phi][nrel]}},
If[Abs[k2]==1 &&(r2*r1==1), nrel=nrel+1;
 {Rule@@{\[Theta][A][{a_,b_,c_,s}], \[Theta][A][{a,0,c,s}]+r2 Power[-1,b] \[Phi][nrel]}},
If[Abs[k3]==1 &&(r2*r1==1), nrel=nrel+1;
{Rule@@{\[Theta][A][{a_,b_,c_,s}], \[Theta][A][{a,b,0,s}]+r2 Power[-1,c] \[Phi][nrel]}}
]]]]]]];
ReduceFU1[HoldPattern[x_EquationU1]]:= 
If[IfFirstOrderDEq2DU1[x],
FirstOrderDEqSolve2DU1[x],
Nothing]
(*First Order solutions*)
FilterReductionsU1[\[Theta][A_],s_,reductions_]:=Cases[reductions,HoldPattern[Rule[\[Theta][A][{coord__,s}],x___]]];

FReductionsU1[reductions_]:=Module[{tempList},
tempList=
(With[{reds=FilterReductionsU1[\[Theta][#1], #2,reductions]}, 
If[Length[reds]!=0, 
  If[FreeQ[Fold[ReplaceAll,\[Theta][#1][{defaultCoords,#2}],reds],\[Theta][#1][coord_/;(MemberQ[coord,x|y|z])]],
    {#1,#2}->(\[Theta][#1][{defaultCoordsPattern,#2}]->Fold[ReplaceAll,\[Theta][#1][{defaultCoords,#2}],reds]),
   Nothing
  ],
Nothing]]& )@@@ (Distribute[{symGenSet,slatList},List]);
tempList = tempList//.{\[Theta][A_][{0,0,0,s_}]->0,\[Theta][A_][{0,0,None,s_}]->0};
Association[tempList]
]

uniquePhiSubRule[relSet_,k_] := Module[{filterSet, set1, set2, set3,tempF},
filterSet=Cases[relSet, HoldPattern[Rule[ \[Phi][k],x__]]];
set1=Cases[filterSet,HoldPattern[Rule[ \[Phi][k],0]]];
set2=Cases[filterSet,HoldPattern[Rule[\[Phi][k], (p_:1) u12pibyk[x_]]]-> p u12pibyk[x]];
set3=Complement[filterSet,set1,set2];
tempF[u12pibyk[p_],u12pibyk[q_]]:=u12pibyk[GCD[p,q]];
(*If[Length[filterSet]!=0,Print[filterSet,set1,set2,set3];,Nothing];*)
If[Length[set1]!=0,
  {\[Phi][k]->0},
  If[Length[set2]!=0,
  {\[Phi][k]->(Fold[tempF,set2]/.{u12pibyk[1]->0})},
  If[Length[set3]!=0,
  {set3[[1]]},
  Nothing]]]

]
updatePhiAssoc[phiRules_,kRules_]:=Module[{frep},
frep[assoc_,key_,ruleSet_]:= Fold[ReplaceAll,assoc[key],ruleSet];
If[Length[phiRules]!=0,
(If[Not[KeyExistsQ[phiAssoc,#[[1]]]], AssociateTo[phiAssoc,#[[1]] -> #[[2]] ];Nothing]&)/@phiRules;,
Nothing
];
If[(Length[phiRules]+Length[kRules])!=0,(phiAssoc[#]=frep[phiAssoc,#,Join[phiRules,kRules]])&/@Keys[phiAssoc]];
Nothing 
]
nrels=Length[SGSet];
reducePhis[rels_] := Module[{phiSubRules, phiConstraintEqs, uniquePhiSubRules,uniqueKRules,newRels,temp2,frep},
   phiConstraintEqs =
   Join @@ (FindRelationConstraintsU1 /@ rels);
   (*Print["rels:",Column[rels]];*)
   (*Print["constrs:",phiConstraintEqs];*)
   phiSubRules = Join @@ RelationConstraintRuleU1 /@ phiConstraintEqs;
   (*Print["rels:",phiConstraintEqs];*)
   (*Print["maps:",RelationConstraintRuleU1/@phiConstraintEqs];*)
   (*Print[(Cases[phiSubRules,HoldPattern[Rule[\[Phi][#],x__]]])&/@ Range[1,nrels]];*)
   (*Print["fullSubrules=",phiSubRules];*)
   temp2=uniquePhiSubRule[Cases[phiSubRules,HoldPattern[Rule[\[Phi][#],x__]]],#]&/@Range[1,nrels];
   uniquePhiSubRules = Join@@(uniquePhiSubRule[Cases[phiSubRules,HoldPattern[Rule[\[Phi][#],x__]]],#]&/@Range[1,nrels]);
   uniqueKRules=Cases[phiSubRules, HoldPattern[Rule[u12pibyk[k_,p_],x__]]];
    phiSubRules= Join[uniquePhiSubRules,uniqueKRules];
    updatePhiAssoc[uniquePhiSubRules,uniqueKRules];
    frep[assoc_,key_,ruleSet_]:= Fold[ReplaceAll,assoc[key],ruleSet];
   (* newRels=rels;
    Print["subRules=",phiSubRules];
    For[i=1, i <= Length[phiSubRules], i++,
      newRels= newRels//.phiSubRules[[i]];
      ];*)
   (*newRels = rels //. phiSubRules//.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]}//DeleteTrivialEquations;*);
   phiSubRules=Rule[#[[1]],ExpandAll[#[[2]]]]&/@phiSubRules;
   newRels=(Fold[ReplaceAll, rels,phiSubRules]/.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]})//DeleteTrivialEquations;
    If[Length[phiSubRules]!=0, 
    ( ((FAssoc[#]=frep[FAssoc,#,phiSubRules])&)/@ Keys[FAssoc];
     ((MAssoc[#]=frep[MAssoc,#,phiSubRules])&)/@ Keys[MAssoc];
    Nothing)];
   
   (*newRels = rels //. phiSubRules//.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]}//DeleteTrivialEquations;*)
   (*newRels = Fold[ReplaceRepeated[rels,#]&, phiSubRules]//.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]}//DeleteTrivialEquations;*)
   (If[ Not[FAssoc[#] === Null], FAssoc[#]=Rule[FAssoc[#][[1]],(FAssoc[#][[2]]//ExpandAll)];]) &/@ Keys[FAssoc];
   (If[ Not[MAssoc[#] === Null], MAssoc[#]=Rule[MAssoc[#][[1]],(MAssoc[#][[2]]//ExpandAll)];]) &/@ Keys[MAssoc];
   DeleteTrivialEquations[newRels]
];
(**** Phi Relations***)
IsolateRelationExponentU1[expr_,a_]:=Module[
{cases,cond,exprd},
exprd=Expand[expr];
cases=If[Not[MatchQ[exprd,Verbatim[Plus][x___]]],
Cases[{exprd},(Times[k_/;(FreeQ[k,x]&&FreeQ[k,y]&&FreeQ[k,z]),a])],
Cases[exprd,(Times[k_/;(FreeQ[k,x]&&FreeQ[k,y]&&FreeQ[k,z]),a])]];
(*Print[cases];*)
cond = Plus@@cases/.{ Times[b_,a,p___]:> Times[1,b,p]};
(*Print[cond];*)
If[Length[cases]!=0,
EquationU1[ExpandAll[cond],0],
Nothing]
]
FindRelationConstraintsU1[HoldPattern[EquationU1[lhs_,rhs_]]]:= 
If[ FreeQ[lhs,x]&&FreeQ[lhs,y]&& FreeQ[lhs,z] && Not[FreeQ[rhs,x] && FreeQ[rhs,y] &&FreeQ[rhs,z]],
     {IsolateRelationExponentU1[rhs,x],
     IsolateRelationExponentU1[rhs,y],
     IsolateRelationExponentU1[rhs,x y],
     If[Not[twoDim],
        Unevaluated[Sequence[ 
          IsolateRelationExponentU1[rhs,z],
          IsolateRelationExponentU1[rhs,z x],
          IsolateRelationExponentU1[rhs,z y],
          IsolateRelationExponentU1[rhs,x y z]
      ]],
      Nothing
     ]
     },
   If[SameQ[lhs,0],
   {EquationU1[0,ExpandAll[rhs]]},
   Nothing
]
]
(*RelationConstraintRule[HoldPattern[Equation[1,Times[x_,y__]]]]:=Module[{min},min= First[Last[List[y]]]; {min->Times[y*Power[min,-1]]}];*)
RelationConstraintRuleU1[HoldPattern[EquationU1[0,(k_:1)\[Phi][p_]]]] := 
If[(k==1)||(k==-1)||(Abs[k]<=1),
   {\[Phi][p]->0},
   npidx=npidx+1;{\[Phi][p]->(u12pibyk[k,npidx])}
   ] /; IntegerQ[k] ;

RelationConstraintRuleU1[HoldPattern[EquationU1[0,Rational[j_,k_] \[Phi][p_]]]] := 
 (  npidx=npidx+1;{\[Phi][p]->(k u12pibyk[j,npidx])});

RelationConstraintRuleU1[HoldPattern[EquationU1[0,Verbatim[Plus][y__,(k_:1)\[Phi][p_]]]]]:= 
If[(k==1)||(k==-1)||(Abs[k]<=1),
   {\[Phi][p]-> -Plus[y]/k},
   npidx=npidx+1;{\[Phi][p]-> u12pibyk[k,npidx] -Plus[y]/k}
   ] /;IntegerQ[k] ;
RelationConstraintRuleU1[HoldPattern[EquationU1[0,Verbatim[Plus][y__,Rational[j_,k_]\[Phi][p_]]]]]:= 
   (npidx=npidx+1;{\[Phi][p]-> k*u12pibyk[j,npidx] -k*Plus[y]/j})    /;IntegerQ[k] ;

RelationConstraintRuleU1[HoldPattern[EquationU1[0,Verbatim[Plus][y__,(k_:1)u12pibyk[p_,q_] ]]]]:= (npidx=npidx+1;{u12pibyk[p,q]-> u12pibyk[k,npidx]-Plus[y]/k}) /;IntegerQ[k] ;
RelationConstraintRuleU1[HoldPattern[EquationU1[0,Verbatim[Plus][y__,Rational[k_,j_] u12pibyk[p_,q_] ]]]]:= (npidx=npidx+1;{u12pibyk[p,q]-> j*u12pibyk[k,npidx]-j*Plus[y]/k})  ;
RelationConstraintRuleU1[HoldPattern[EquationU1[0,(k_:1)u12pibyk[p_,q_] ]]]:= (npidx=npidx+1;{u12pibyk[p,q]-> u12pibyk[k,npidx]}); /;IntegerQ[k];
RelationConstraintRuleU1[HoldPattern[EquationU1[0,Rational[k_,j_] u12pibyk[p_,q_] ]]]:= (npidx=npidx+1;{u12pibyk[p,q]-> u12pibyk[k,npidx]})
(*
RelationConstraintRuleU1[HoldPattern[EquationU1[0,Verbatim[Plus][y__,Rational[j_,k_] u12pibyk[p_,q_] ]]]]:= (npidx=npidx+1;{u12pibyk[j,npidx]-> -k*Plus[y]/j})/;IntegerQ[k]; 
RelationConstraintRuleU1[HoldPattern[EquationU1[0,Rational[j_,k_] u12pibyk[p_,q_] ]]]:= (npidx=npidx+1;{u12pibyk[p,q]-> k*u12pibyk[j,npidx]})/;IntegerQ[j];*)
End[]

EndPackage[]




