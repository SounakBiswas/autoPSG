(* ::Package:: *)

BeginPackage["autoPSG`matrixSolver`"]

Remove["autoPSG`matrixSolver`*"]
Needs["autoPSG`definitions`"] 
Needs["autoPSG`symmetryG`"] 
Needs["autoPSG`z2Utils`"] 
Needs["autoPSG`paulis`"] 
Needs["autoPSG`phaseSolverZ2`"] 

sol\[Alpha]Assoc;
sol\[Beta]Assoc;
sol\[Theta]Assoc;
sol\[Eta]Assoc;
mlist::usage="list of terms in coupled SU2 eqs"
elist::usage="list of etas in coupled SU2 eqs"
etaRedefinitions;
initSolAssocs::usage="initialise associations for SU2-equation solutions"
setSlatGauges::usage = "initial setting of sublattice dependent gauges"
matrixSolverIterate::usage = "iteratively reduce sets of SU2 matrix equations"
CancelInversesEq::usage="might help, M exp M-1--> exp"
simplifyPowersSU2::usage="write SU2 equation in terms of powers"
setSlatDependentGauges::usage="set sublattice dependent gauges"
solveSU2::usage="solve coupled SU2 matrix eqs"

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
       If[gendoc,
           Print["eliminate with ", subRule//z2Simplify, "from ", eq//z2Simplify];
           ];
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
      If[gendoc and eq1 !=eq2,
          Print[" Replace", eq1, " in ", eq2];
          Print["To get ", newEq[[1]]];
    ];
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

(*Write in terms of powers*)
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[z_],SU2[z_],y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x, SU2[z]^2,y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[z_]^m_,SU2[z_]^n_,y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(m+n),y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[z_],SU2[z_]^n_,y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(1+n),y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[z_]^m_,SU2[z_],y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(1+m),y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[Inv[z_]],SU2[z_]^m_,y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(m-1),y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[z_]^m_,SU2[Inv[z_]],y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(m-1),y],rhs]];

simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[Inv[z_]],SU2[z_]^m_ y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(m-1),y],rhs]];

simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[Inv[z_]]^m_,SU2[z_],y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(1-m),y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[z_],SU2[Inv[z_]]^m_,y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(1-m),y],rhs]];
simplifyPowersSU2[HoldPattern[Equation[CenterDot[x___,SU2[Inv[z_]]^n_,SU2[z_]^m_,y___],rhs_]]]:=simplifyPowersSU2[Equation[CenterDot[x,SU2[z]^(m-n),y],rhs]];

setSlatDependentGauges[rels_]:=
Module[{edges,mark,setSlatGauge,rules,seed0},
    edges={};
    (AppendTo[edges,{#[[2]],ExpandAll[ (Inv[#[[1]]][{0,0,0,#[[2]]}])[[4]]],#[[1]]}];)&/@(Distribute[{Complement[symGenSet,{T1,T2,T3}],slatList},List]);
    mark=<||>;
    Scan[AssociateTo[mark,#->"canBeSet"]&,slatList];
    AssociateTo[mark,slatList[[1]]->"canNotBeSet"];
    rules={};
    setSlatGauge[seeds_]:=
    Module[{tmp,e,snew},
        If[Length[seeds]==0,
            {Nothing},

            tmp=Select[edges,(#[[1]]==seeds[[1]] &&mark[#[[2]]]=="canBeSet" &)];
            snew=Drop[seeds,1];
            If[tmp=={},
                setSlatGauge[snew]
                ,
                e=tmp[[1]];
                AssociateTo[mark,e[[2]]->"canNotBeSet"];
                AppendTo[snew,e[[2]]];
                AssociateTo[MAssoc,{e[[3]],e[[1]]}->(SU2[M[e[[3]]][e[[1]]]]->SU2[\[Tau]0])];
                Join[{SU2[M[e[[3]]][e[[1]]]]->SU2[\[Tau]0]},
                setSlatGauge[snew]]
            ]
        ]
    ];
    seed0={slatList[[1]]};
    rules=setSlatGauge[seed0];
    rels//.rules
];



relabelEtas[rel_,nt_]:=Module[{new},If[MatchQ[rel[[2]],Verbatim[Times][x__?((NumberQ[#] || MatchQ[#,\[Eta][p_]])&)]],
nt=nt+1;
AppendTo[etaRedefinitions,Equation[1,\[Eta][nt]rel[[2]]]];
Equation[rel[[1]],\[Eta][nt]],
rel]
];
powerSolvable[Equation[SU2[x_]^m_,k_ ]]/; k==1 || k==-1:=True;
powerSolvable[Equation[SU2[x_],k_]]/; k==1 || k==-1:=True;
powerSolutions[eq:Equation[SU2[Inv[M[g_][s_]]]^m_,k_:1]]/; k==1 || k==-1:=powerSolutions[Equation[SU2[M[g][s]]^m,k]];
mSolutions[HoldPattern[Equation[lhs_,rhs_]]]:=
Module[{c0,c1,c2,c3,expanded,reds,sol,alphas,betas,vars,alpha,beta,rhsvar},
    expanded=lhs;
    expanded=ExpandAll[expanded];
    alphas=Cases[lhs,\[Alpha][x_]->x,Infinity];
    betas=Cases[lhs,\[Beta][x_]->x,Infinity];
    vars=Join[alphas,betas]//DeleteDuplicates;
    vars=vars[[1]];
    rhsvar=rhs;
    expanded=expanded//.{\[Alpha][x_]->alpha,\[Beta][x_]->beta};
    rhsvar=rhsvar//.{\[Alpha][x_]->alpha,\[Beta][x_]->beta};
    
    c1=Coefficient[expanded,paulis[[2]]];
    c2=Coefficient[expanded,paulis[[3]]];
    c3=Coefficient[expanded,paulis[[4]]];
    c0=((expanded-c1 paulis[[2]]-c2 paulis[[3]]-c3 paulis[[4]])//ComplexExpand//FullSimplify);

    (*c0=c0//.{\[Alpha][x_]->alpha};
    c1=c1//.{\[Alpha][x_]->alpha};
    c2=c2//.{\[Alpha][x_]->alpha};
    c3=c2//.{\[Alpha][x_]->alpha};
    c0=c0//.{\[beta][x_]->beta};
    c1=c1//.{\[Beta][x_]->beta};
    c2=c2//.{\[Beta][x_]->beta};
    c3=c2//.{\[Beta][x_]->beta};*)
    reds := Reduce[ {c0==rhsvar,c1==0, c2==0, c3==0,0<=beta<Pi}, {alpha, beta}]//Simplify;

    sol=Solve[reds];
    (*(sol[[#]][[1]][[1]]=\[Beta][vars])&/@Range[Length[sol]];*)
    sol=sol/.{beta->\[Beta][vars],alpha->\[Alpha][vars]};
    (*Print["reds= ",reds];
    Print["now",sol];*)
    sol
];
powerSolvable[x_]:=False
powerSolutions[Equation[SU2[M[g_][s_]]^m_,k_]]/; k==1 || k==-1:=
Module[{\[Theta]tab},
\[Theta]tab=If[k==1,
If[EvenQ[m],Table[2* Pi n/m,{n,0,Quotient[m,2]-1}],
Table[2* Pi n/m,{n,0,Quotient[m-1,2]}]],
If[EvenQ[m],Table[ Pi (2 n+1)/m,{n,0,Quotient[m,2]-1}],Table[(2n+1)* Pi /m,{n,0,Quotient[m-1,2]}]]
];
(({g,s}->#)&)/@\[Theta]tab
];
ifSolvableForM[eq_]:=
Module[{alphas,betas},
alphas=Cases[eq[[1]],\[Alpha][x_]->\[Alpha][x],Infinity]//DeleteDuplicates;
betas=Cases[eq[[1]],\[Beta][x_]->\[Beta][x],Infinity]//DeleteDuplicates;
If[FreeQ[eq,M] && Not[NumericQ[eq[[1]]]]&&Length[alphas] <=1 && Length[betas]<=1,True,False]
];
updateEtaAssoc2[etaRules_]:=Module[{frep},
    frep[assoc_,key_,ruleSet_]:= Fold[ReplaceAll,assoc[key],ruleSet];
    If[Length[etaRules]!=0,
    (If[Not[KeyExistsQ[etaAssoc,#[[1]]]], AssociateTo[etaAssoc,#[[1]] -> #[[2]] ];Nothing]&)/@etaRules;,
     Nothing
     ];
    If[(Length[etaRules])!=0,
        (etaAssoc[#]=frep[etaAssoc,#,etaRules])&/@Keys[etaAssoc]];
      Nothing 
]

genSU2Form=Cos[\[Theta]]paulis[[1]] +I Sin[\[Theta]] (Cos[\[Beta]]paulis[[2]]+Sin[\[Beta]]Cos[\[Alpha]]paulis[[3]]+Sin[\[Beta]]Sin[\[Alpha]]paulis[[4]]);

getMFromAssoc[gspair_]:=
Module[{rule,rhs,rhs2,su2Form},
    rules={sol\[Theta]Assoc[gspair],sol\[Beta]Assoc[gspair], sol\[Alpha]Assoc[gspair]};
    su2Form=Cos[\[Theta][gspair]]paulis[[1]] +I Sin[\[Theta][gspair]] (Cos[\[Beta][gspair]]paulis[[2]]+Sin[\[Beta][gspair]]Cos[\[Alpha][gspair]]paulis[[3]]+Sin[\[Beta][gspair]]Sin[\[Alpha][gspair]]paulis[[4]]);
    rhs=su2Form//.{sol\[Theta]Assoc[gspair],sol\[Beta]Assoc[gspair],sol\[Alpha]Assoc[gspair]};
    rhs2=(su2Form/.{\[Theta][gspair]-> -\[Theta][gspair]})//.{sol\[Theta]Assoc[gspair],sol\[Beta]Assoc[gspair],sol\[Alpha]Assoc[gspair]};
;
    rule={SU2[M[gspair[[1]]][gspair[[2]]]]->rhs,SU2[Inv[M[gspair[[1]]][gspair[[2]]]]]->rhs2};
    rule
]
necessaryFalsehood[HoldPattern[Equation[lhs_,rhs_]]]:= If[NumericQ[lhs]&&NumericQ[rhs]&& (rhs!=lhs),True,False];
solveSU2[rels_,gauge_]:=
Module[{pSolvable,mSolvable,etaUnset,
        sols,rels2,unfixedGauge,func,\[Eta]subrules,
        \[Eta]constrs,mUnset,b\[Eta]Assoc,b\[Theta]Assoc,
        falsehood,b\[Alpha]Assoc,b\[Beta]Assoc,gspair},
	pSolvable=((If[powerSolvable[#],#,Nothing]&)/@rels);
	mSolvable=((If[ifSolvableForM[#],#,Nothing]&)/@rels);
	unfixedGauge=gauge;
	If[Length[rels]==0,
		Print["Solution Found:"];
		Print["etas: ",Values[sol\[Eta]Assoc], " Ms: ",getMFromAssoc[#][[1]]&/@mlist, "unfixed=",unfixedGauge];
                ,
		etaUnset=((If[sol\[Eta]Assoc[#]===Nothing,#,Nothing])&)/@ elist;
		mUnset=(With[{tmp=getMFromAssoc[#]},If[FreeQ[tmp,\[Theta]] && FreeQ[tmp,\[Alpha]]&&FreeQ[tmp,\[Beta]],tmp,Nothing]])&/@mlist;
	(*Else If*)
	If[Length[etaUnset]==0 && Length[mUnset]==0,
		Print["no sol bad luck"];, 
		
	(*Else If*)			
	If[Length[pSolvable]!=0,
		sols=powerSolutions[pSolvable[[1]]];
	     b\[Eta]Assoc=sol\[Eta]Assoc; b\[Theta]Assoc=sol\[Theta]Assoc; b\[Beta]Assoc=sol\[Beta]Assoc; b\[Alpha]Assoc=sol\[Alpha]Assoc;
		Scan[(
			AssociateTo[sol\[Theta]Assoc,#[[1]]->(\[Theta][#[[1]]]->#[[2]])];
			If[unfixedGauge=="SU2" && #[[2]]!=0,
							AssociateTo[sol\[Beta]Assoc,#[[1]]->(\[Beta][#[[1]]]->0)];
							unfixedGauge="U1";];
			rels2=rels//.{Power[SU2[n_],m_]:>CenterDot@@ConstantArray[SU2[n],m]}//.getMFromAssoc[#[[1]]];
			 rels2=rels2//ComplexExpand//FullSimplify;
			 Scan[Function[x,rels2[[x]][[1]]=ExpandAll[rels2[[x]][[1]]]], Range[Length[rels2]]];
	         rels2=rels2//DeleteTrivialEquations;
			\[Eta]constrs=z2Simplify[Join@@FindRelationConstraints/@rels2];
			 \[Eta]subrules=Join@@RelationConstraintRule/@\[Eta]constrs;
			rels2=rels2//.\[Eta]subrules//z2Simplify//DeleteTrivialEquations;
			falsehood=Map[necessaryFalsehood, rels2];
			falsehood=Or@@falsehood;
	         Map[Function[var,Scan[AssociateTo[sol\[Eta]Assoc,var[[1]]->var]]],  \[Eta]subrules];
			rels2=Delete[#,0]&/@(simplifyPowersSU2/@rels2);
	         If[falsehood, Null,
	 
			solveSU2[rels2,unfixedGauge];];
	         sol\[Eta]Assoc=b\[Eta]Assoc; sol\[Theta]Assoc=b\[Theta]Assoc; sol\[Beta]Assoc=b\[Beta]Assoc; sol\[Alpha]Assoc=b\[Alpha]Assoc;
	         unfixedGauge=gauge;
			
		)&,sols];
		,
	(*Else If*)	
	If[Length[mSolvable]!=0,
	 b\[Eta]Assoc=sol\[Eta]Assoc; b\[Theta]Assoc=sol\[Theta]Assoc; b\[Beta]Assoc=sol\[Beta]Assoc; b\[Alpha]Assoc=sol\[Alpha]Assoc;
		sols=mSolutions[mSolvable[[1]]];
		gspair=Join[Cases[mSolvable[[1]],\[Beta][x_]->x,Infinity],Cases[mSolvable[[1]],\[Alpha][x_]->x,Infinity]];
		gspair=gspair[[1]];
                If[Length[sols]==0,Null
                    ,
		Scan[(
			(associate\[Beta]and\[Alpha]FromSol/@#);
			If[sol\[Alpha]Assoc[gspair]===Nothing && sol\[Beta]Assoc[gspair][[2]]!=0 && unfixedGauge=="U1",
			AssociateTo[sol\[Alpha]Assoc,gspair->(\[Alpha][gspair]->0)];
                        unfixedGauge="Z2";
			];
			rels2=rels//.#;
			rels2=rels2//ComplexExpand//FullSimplify;
			rels2=rels2//DeleteTrivialEquations;
			\[Eta]constrs=z2Simplify[Join@@FindRelationConstraints/@rels2];
			 \[Eta]subrules=Join@@RelationConstraintRule/@\[Eta]constrs;
			rels2=rels2//.\[Eta]subrules//z2Simplify//DeleteTrivialEquations;
			falsehood=Map[necessaryFalsehood, rels2];
			falsehood=Or@@falsehood;
			Map[Function[var,Scan[AssociateTo[sol\[Eta]Assoc,var[[1]]->var]]],  \[Eta]subrules];
			rels2=Delete[#,0]&/@(simplifyPowersSU2/@rels2);
	         If[falsehood,Null 
	             ,
	            solveSU2[rels2,unfixedGauge];Nothing];
	         sol\[Eta]Assoc=b\[Eta]Assoc; sol\[Theta]Assoc=b\[Theta]Assoc; sol\[Beta]Assoc=b\[Beta]Assoc; sol\[Alpha]Assoc=b\[Alpha]Assoc;
	         unfixedGauge=gauge;  
		)& /@ sols];]
		,
		etaUnset=((If[sol\[Eta]Assoc[#]===Nothing,#,Nothing])&)/@ elist;
		If[Length[etaUnset]!=0,
	          b\[Eta]Assoc=sol\[Eta]Assoc;
			Scan[(
				AssociateTo[sol\[Eta]Assoc, etaUnset[[1]]->(etaUnset[[1]]->#)];
				rels2=rels//.{etaUnset[[1]]->#}//z2Simplify//DeleteTrivialEquations;
				rels2=Delete[#,0]&/@(simplifyPowersSU2/@rels2);
				solveSU2[rels2,unfixedGauge];
	             sol\[Eta]Assoc=b\[Eta]Assoc;
			)&,{1,-1}];
	     ]
	]]]]
];
associate\[Beta]and\[Alpha]FromSol[Rule[\[Alpha][x_],val_]]:=AssociateTo[sol\[Alpha]Assoc,x->(\[Alpha][x]->val)];
associate\[Beta]and\[Alpha]FromSol[Rule[\[Beta][x_],val_]]:=AssociateTo[sol\[Beta]Assoc,x->(\[Beta][x]->val)];

initSolAssocs[rels_]:=
Module[{nte,relsr},
	etaRedefinitions={};
	nte=0;
	relsr=relabelEtas[#,Unevaluated[nte]]&/@rels;
	mlist=Cases[relsr,SU2[M[x_][y_]]->{x,y},Infinity]//DeleteDuplicates;
	elist=Cases[relsr,\[Eta][x_]->\[Eta][x],Infinity]//DeleteDuplicates;
	sol\[Eta]Assoc=Association[{#->Nothing}&/@elist];
	sol\[Theta]Assoc=Association[{#->Nothing}&/@mlist];
	sol\[Beta]Assoc=Association[{#->Nothing}&/@mlist];
	sol\[Alpha]Assoc=Association[{#->Nothing}&/@mlist];
	relsr
];



End[]

EndPackage[]
