(* ::Package:: *)
BeginPackage["autoPSG`matrixSolver`"]

Remove["autoPSG`matrixSolver`*"]
Needs["autoPSG`definitions`"] 
Needs["autoPSG`symmetryG`"] 
Needs["autoPSG`z2Utils`"] 
Needs["autoPSG`paulis`"] 
Needs["autoPSG`phaseSolverZ2`"] 

ifSlatGaugeSet; slatGaugeSetDependency;
setSlatGauges::usage = "initial setting of sublattice dependent gauges"
matrixSolverIterate::usage = "iteratively reduce sets of SU2 matrix equations"
CancelInversesEq::usage="might help, M exp M-1--> exp"


Begin["Private`"]
matrixSolverIterate[rels0_]:=Module[{rels,rels2},
  rels = replaceAllMEqsIntoAllMEqs[rels0];
  rels = reduceEtas[rels];
  rels = performMSubstitutions[rels] // z2Simplify // DeleteTrivialEquations;
  rels = reduceEtas[rels];
  rels = rels // CancelInverses;
  If[rels==rels0, 
  rels
       , 
       matrixSolverIterate[rels]
       ]
  (*If[rels==rels0, 
       
       rels2 = performMSubstitutions[rels] // z2Simplify // DeleteTrivialEquations;
       rels2 = reduceEtas[rels2];
       rels2 = rels2 // CancelInverses;
       If[rels2==rels0,
        rels2,
        matrixSolverIterate[rels2]
        ]

       , 
       matrixSolverIterate[rels]]*)
]

ifSlatGaugeSet=Association@@((#->False)&/@slatList);



setSlatGauges[]:=
Module[{slatGaugeSetDependency,trySettingSlatGauge,findAllDependencies},
  slatGaugeSetDependency= Association @@(#->Null&/@slatList);
  findAllDependencies[a_]:= 
  If[slatGaugeSetDependency[a]===Null,
   {}, 
   Join[{slatGaugeSetDependency[a]},findAllDependencies[slatGaugeSetDependency[a]]]
  ]; 
  trySettingSlatGauge[A_,a_]:=
  Module[{newSlat},
    newSlat= Inv[A][{x,y,z,a}][[4]];
    If[ And[Not[MatchQ[a,newSlat]], ifSlatGaugeSet[newSlat]==False ,Not[MemberQ[findAllDependencies[a],newSlat]]],
    (MAssoc[{A,a}]=SU2[ M[A][a]]->SU2[\[Tau]0];
    ifSlatGaugeSet[newSlat]=True;
    slatGaugeSetDependency[newSlat]=a;)
    ]
  ];
  (trySettingSlatGauge[#1,#2]&)@@@Distribute[{symGenSet,slatList},List]
];


getMSubstitutor[HoldPattern[Equation[CenterDot[SU2[M[A_][s_]],y__SU2],rhs_]]]/;FreeQ[List[y],M[A][s]] := 
  Module[{subRule},
    subRule=SU2[M[A][s]]-> rhs matrixInvert[CenterDot[y]];
    MAssoc[{A,s }]=subRule;
    subRule
  ];

getMSubstitutor[HoldPattern[Equation[CenterDot[SU2[Inv[M[A_][s_]]],y__SU2],rhs_]]]/;FreeQ[List[y],M[A][s]] := 
   Module[{subRule},
     subRule=SU2[M[A][s]]-> rhs^ -1  CenterDot[y];
     MAssoc[{A,s }]=subRule;
     subRule
   ];

getMSubstitutor[HoldPattern[Equation[SU2[Inv[M[A_][s_]]],rhs_]]] := 
  Module[{subRule},
    subRule=SU2[M[A][s]]-> rhs^ -1  SU2[\[Tau]0] ;
    MAssoc[{A,s }]=subRule;
    subRule
    ];
getMSubstitutor[HoldPattern[Equation[SU2[M[A_][s_]],rhs_]]] := 
  Module[{subRule},
    subRule=SU2[M[A][s]]-> rhs SU2[\[Tau]0] ;
    MAssoc[{A,s }]=subRule;
    subRule
  ];
getMSubstitutor[eq_Equation]=Nothing;

(*Simpler substitors,single point*)
getMSubstitutor2[HoldPattern[Equation[CenterDot[SU2[M[A_][s_]],y_SU2],rhs_]]]/;FreeQ[List[y],M[A][s]] := Module[{subRule},
subRule=SU2[M[A][s]]-> rhs^(-1) matrixInvert[CenterDot[y]];
MAssoc[{A,s }]=subRule;
subRule];
getMSubstitutor2[HoldPattern[Equation[CenterDot[SU2[Inv[M[A_][s_]]],y_SU2],rhs_]]]/;FreeQ[List[y],M[A][s]] := 
Module[{subRule},
subRule=SU2[M[A][s]]-> rhs^   CenterDot[y];
MAssoc[{A,s }]=subRule;
subRule];

getMSubstitutor2[HoldPattern[Equation[SU2[Inv[M[A_][s_]]],rhs_]]] := 
Module[{subRule},
subRule=SU2[M[A][s]]-> rhs  SU2[\[Tau]0] ;
MAssoc[{A,s }]=subRule;
subRule];

getMSubstitutor2[HoldPattern[Equation[SU2[M[A_][s_]],rhs_]]] := 
Module[{subRule},
subRule=SU2[M[A][s]]-> rhs^(-1) SU2[\[Tau]0] ;
MAssoc[{A,s }]=subRule;
subRule];

getMSubstitutor2 [eq_Equation]=Nothing;


updateMAssoc[A_,s_,subRule_]:=
  Module[{newRHS,oldRule},
    oldRule=MAssoc[{A,s}];
    If[Not[MatchQ[oldRule,Null]],
      (newRHS=z2Simplify[oldRule[[2]]]//.SubstFormInvM//.{subRule}//.DispFormInvM;
       MAssoc[{A,s}]=Rule[oldRule[[1]],newRHS];)
    ]
  ];

substM[eqSet_,eqno_]:=
  Module[{eq,subRule,newEqSet},
    eq= eqSet[[eqno]];
    subRule= getMSubstitutor[eq];
    If[Not[MatchQ[subRule,Nothing]],
       (newEqSet=eqSet//.SubstFormInvM//.{subRule}//.DispFormInvM;
       (updateMAssoc[#1,#2,subRule]&)@@@ Distribute[{symGenSet,slatList},List];
        newEqSet),
      eqSet
    ]
  ];

substM2[eqSet_,eqno_]:=
  Module[{eq,subRule,newEqSet},
    eq= eqSet[[eqno]];
    subRule= getMSubstitutor2[eq];
    If[Not[MatchQ[subRule,Nothing]],
       (newEqSet=eqSet//.SubstFormInvM//.{subRule}//.DispFormInvM;
       (updateMAssoc[#1,#2,subRule]&)@@@ Distribute[{symGenSet,slatList},List];
        newEqSet),
      eqSet
    ]
  ];

performMSubstitutions[eqSet_]:= Fold[substM,eqSet,Range[1,Length[eqSet]]];
performMSubstitutions2[eqSet_]:= Fold[substM2,eqSet,Range[1,Length[eqSet]]];

substEq[HoldPattern[Equation[CenterDot[p___,y__],rhs1_]], HoldPattern[Equation[CenterDot[x___,y__,z___],rhs2_]]]/;(Length[List[y]]>Length[List[p]]):=
Equation[CenterDot[x,matrixInvert[CenterDot[p]],z],rhs2 rhs1^-1];
substEq[eq1_Equation,eq2_Equation]:=Nothing;

replaceMEqIntoMEq[eq1:HoldPattern[Equation[CenterDot[x1__],rhs1_]],eq2:HoldPattern[Equation[CenterDot[x2__],rhs2_]]]:= 
  Module[{newEq1,newEq2,newEq,lhs2},
    newEq1=substEq[Equation[RotateLeft[eq1[[1]],#],rhs1],eq2]&/@Range[1,Length[eq1[[1]]]];
    lhs2=matrixInvert[eq1[[1]]];
    newEq2=substEq[Equation[RotateLeft[lhs2,#],rhs1],eq2]&/@Range[1,Length[eq1[[1]]]];
    newEq=Join[newEq1,newEq2];
    If[Length[newEq]!= 0,
      newEq[[1]],
      eq2
    ]
  ];
replaceMEqIntoMEq[eq1_,eq2_]:=eq2 ;


replaceMEqIntoAllMEqs[eqSet_,eqNo_]:=
  Module[{newEqSet},
    newEqSet=replaceMEqIntoMEq[eqSet[[eqNo]],#]&/@eqSet;
    newEqSet[[eqNo]]=eqSet[[eqNo]];
    newEqSet
  ];

replaceAllMEqsIntoAllMEqs[eqSet_]:=Fold[replaceMEqIntoAllMEqs,eqSet,Range[1,Length[eqSet]]];


CancelInversesEq[HoldPattern[Equation[CenterDot[SU2[x_],y___,SU2[Inv[x_]]],rhs_] ]]:= Equation[CenterDot[y],rhs];
CancelInversesEq[HoldPattern[Equation[CenterDot[SU2[Inv[x_]],y___,SU2[x_]],rhs_] ]]:= Equation[CenterDot[y],rhs];
CancelInversesEq[x_]:=x;
CancelInverses[eqSet_]:= CancelInversesEq[#]&/@ eqSet

End[]
EndPackage[]
