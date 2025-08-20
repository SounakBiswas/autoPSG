(* ::Package:: *)

BeginPackage["psgSolver`phaseSolverU1`"]
Remove["psgSolver`phaseSolverU1`*"]
Needs["psgSolver`definitions`"] 
Needs["psgSolver`symmetryG`"] 
Needs["psgSolver`z2Utils`"] 
Needs["psgSolver`paulis`"] 

initPSGSolverU1::usage ="initiate solver, basic associations"
decomposeGtoFMU1::usage = "decompose matrices into phase part and matrix for U1"
moveTauOnes::usage = "move tau1s to the left"
seperateMinusIotas;
simplifyNs;
performNSubstitutions::usage = "simplify Ns"

Begin["Private`"]

(****************************************)
initPSGSolverU1[]:=(
   FSubstAssoc=Association@@((#->{})&/@symGenSet);

   ifIGGSet=Association@@(#->False&/@symGenSet);

   FAssoc = Association @@ (({#1, #2} ->Null) &) @@@ (Distribute[{symGenSet, slatList}, List]) ;
   MAssoc = Association @@ (({#1, #2} ->Null) &) @@@ (Distribute[{symGenSet, slatList}, List]);
   NAssoc=Association@@(#->(Null)&/@symGenSet);




   (MAssoc[{Tx,#}]=(SU2[M[Tx][#]]->SU2[\[Tau]0]);&)/@slatList; 
   (MAssoc[{Ty,#}]=(SU2[M[Ty][#]]->SU2[\[Tau]0]);&)/@slatList; 
   If[Not[twoDim],
     (MAssoc[{Tz,#}]=(SU2[M[Tz][#]]->SU2[\[Tau]0]);&)/@slatList; 
   ]
   If[twoDim,
      ( ( FAssoc[{Tx,#}]=(F[Tx][{x_,y_,None,#}]->1); &)/@slatList;
        ( FAssoc[{Ty,#}]=(F[Ty][{x_,y_,None,#}]-> \[Eta][1]^x ); &)/@slatList;
       ),
   
      ( (  FAssoc[{Tx,#}]=(F[Tx][{x_,y_,z_,#}]->1); &)/@slatList;
        (  FAssoc[{Ty,#}]=(F[Ty][{x_,y_,z_,#}]-> \[Eta][1]^x); &)/@slatList;
        (  FAssoc[{Tz,#}]=(F[Tz][{x_,y_,z_,#}]-> \[Eta][2]^y \[Eta][3]^x); &)/@slatList;
       )
   ]
)

nrel=Length[SGset];
(****************************************)
decomposeGtoFMU1[expr_]:= expr/.{SU2[G[A_]][{x_,y_,z_,s_}]-> CenterDot[(I SU2[\[Tau]1])^(n[A]),Exp[ I SU2[\[Tau]3] \[Theta][A][{x,y,z,s}] ] , Exp[I SU2[\[Tau]3] m[A][s] ]],SU2[Inv[G[A_]]][{x_,y_,z_,s_}]-> CenterDot[(-I SU2[\[Tau]1])^(n[A]),Exp[-I SU2[\[Tau]3] \[Theta][A][{x,y,z,s}]], Exp[-I SU2[\[Tau]3] m[A][s] ]]};


moveTauOnes= HoldPattern[
   CenterDot[a___,
    Power[E, Complex[0, x_] m_ SU2[\[Tau]3]], (SU2[\[Tau]1])^(k_),
    b___]] :> CenterDot[a, ( SU2[\[Tau]1])^k,
   Exp[Complex[0, x] (-1)^k m SU2[\[Tau]3]], b]

SeparatePowersTau =
With[{VPower=Verbatim[Power],VPlus=Verbatim[Plus],VTimes=Verbatim[Times]},
{ VPower[a__,VPlus[b__]]:>Inactive[Times]@@((Power[a,#]&)/@List[b])}]

killEvenPowers={Power[SU2[\[Tau]1],k_?EvenQ n[A_]] -> 1,Power[SU2[\[Tau]1],k_?OddQ n[A_]] -> Power[SU2[\[Tau]1], n[A]]};

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

getNSubstitutor[HoldPattern[Equation[CenterDot[Power[SU2[\[Tau]1],Plus[n[A_],x_:0]],others___],rhs_]]]:= Module[{subRule},subRule=(n[A] -> -x); NAssoc[A]=subRule;subRule]

getNSubstitutor[HoldPattern[Equation[CenterDot[Power[SU2[\[Tau]1],Plus[-n[A_],x_:0]],others___],rhs_]]]:= Module[{subRule},subRule=(n[A] -> x); NAssoc[A]=subRule;subRule]
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

End[]

EndPackage[]
