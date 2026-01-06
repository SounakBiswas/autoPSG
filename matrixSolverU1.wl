(* ::Package:: *)

BeginPackage["autoPSG`matrixSolverU1`"]

Remove["autoPSG`matrixSolverU1`*"]
Needs["autoPSG`definitions`"] 
Needs["autoPSG`symmetryG`"] 
Needs["autoPSG`z2Utils`"] 
Needs["autoPSG`paulis`"] 
Needs["autoPSG`phaseSolverU1`"] 

(*ifSlatGaugeSet; *)
mSolverIterateU1::usage = "iteratively reduce sets of U1 space-independent phases"



Begin["Private`"]
mSolverIterateU1[rels0_]:=Module[{rels,rels2},
  (*Print[Values[MAssoc]];*)
  rels = replaceAllMEqsIntoAllMEqsU1[rels0]//DeleteTrivialEquations;
  rels = reducePhis[rels];
  rels = performMSubstitutionsU1[rels]/.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]} // DeleteTrivialEquations;
  rels = FixedPoint[reducePhis,rels]/.{HoldPattern[EquationU1[lhs_,rhs_]]:> EquationU1[lhs,ExpandAll[rhs]]}//DeleteTrivialEquations;

  If[rels==rels0, 
  rels, 
       mSolverIterateU1[rels]
  ]
]

ifSlatGaugeSet=Association@@((#->False)&/@slatList);



getMSubstitutorU1[HoldPattern[EquationU1[Plus[(k_:1)\[ScriptM][A_][s_],y___],rhs_]]]/;FreeQ[List[y],\[ScriptM][A][s]] := 
  Module[{subRule},
    npidx=npidx+1;
    subRule=\[ScriptM][A][s]-> u12pibyk[k,npidx] +ExpandAll[rhs]/k -ExpandAll[Plus[y]]/k;
(*    Print["rule: ",subRule, "k= ",k,", mat=  ", \[ScriptM][A][s],", rhs= ", -y+rhs];*)
    MAssoc[{A,s }]=subRule;
    subRule
  ];
getMSubstitutorU1[HoldPattern[EquationU1[(k_:1)\[ScriptM][A_][s_],rhs_]]] := 
  Module[{subRule},
    npidx=npidx+1;
    subRule=\[ScriptM][A][s]-> u12pibyk[k,npidx] +ExpandAll[rhs]/k;
    MAssoc[{A,s }]=subRule;
    (*Print["rule: ",subRule, "k= ",k,", mat=  ", \[ScriptM][A][s], ", rhs=",rhs];*)
    subRule
  ];


getMSubstitutorU1[eq_EquationU1]=Nothing;



updateMAssocU1[A_,s_,subRule_]:=
  Module[{newRHS,oldRule},
    oldRule=MAssoc[{A,s}];
    If[Not[MatchQ[oldRule,Null]],
      (newRHS=(oldRule[[2]]//ExpandAll)//.{subRule};
       MAssoc[{A,s}]=Rule[oldRule[[1]],newRHS];)
    ]
  ];

substMU1[eqSet_,eqno_]:=
  Module[{eq,subRule,newEqSet},
    eq= eqSet[[eqno]];
    subRule= getMSubstitutorU1[eq];
    If[Not[MatchQ[subRule,Nothing]],
       (newEqSet=eqSet//.{subRule};
       (updateMAssocU1[#1,#2,subRule]&)@@@ Distribute[{symGenSet,slatList},List];
        newEqSet),
      eqSet
    ]
  ];



performMSubstitutionsU1[eqSet_]:= Fold[substMU1,eqSet,Range[1,Length[eqSet]]];

substEqU1[HoldPattern[eq1:EquationU1[Plus[p___,y__],rhs1_]], eq2:HoldPattern[EquationU1[Plus[x___,y__,z___],rhs2_]]]/;(Length[List[y]]>Length[List[p]]):=
((*Print["succ:",eq1,","eq2,",",EquationU1[Plus[x,z]-Plus[p],rhs2 -rhs1]];*)EquationU1[Plus[x,z]-Plus[p],rhs2 -rhs1]);
substEqU1[eq1_EquationU1,eq2_EquationU1]:=Nothing;

replaceMEqIntoMEqU1[eq1:HoldPattern[EquationU1[Plus[x1__],rhs1_]],eq2:HoldPattern[EquationU1[Plus[x2__],rhs2_]]]:= 
  Module[{newEq1,newEq2,newEq,lhs2,rhs1m},
    newEq1=substEqU1[EquationU1[RotateLeft[eq1[[1]],#],rhs1],eq2]&/@Range[1,Length[eq1[[1]]]];
    lhs2=-eq1[[1]];
    rhs1m=-rhs1;
    newEq2=substEqU1[EquationU1[RotateLeft[lhs2,#],rhs1m],eq2]&/@Range[1,Length[eq1[[1]]]];
    newEq=Join[newEq1,newEq2];
    If[Length[newEq]!= 0,
      newEq[[1]],
      eq2
    ]
  ];
replaceMEqIntoMEqU1[eq1_,eq2_]:=eq2 ;


replaceMEqIntoAllMEqsU1[eqSet_,eqNo_]:=
  Module[{newEqSet},
    newEqSet=replaceMEqIntoMEqU1[eqSet[[eqNo]],#]&/@eqSet;
    newEqSet[[eqNo]]=eqSet[[eqNo]];
    newEqSet
  ];

replaceAllMEqsIntoAllMEqsU1[eqSet_]:=Fold[replaceMEqIntoAllMEqsU1,eqSet,Range[1,Length[eqSet]]];



End[]
EndPackage[]
