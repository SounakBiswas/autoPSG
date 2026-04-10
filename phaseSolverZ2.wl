(* ::Package:: *)

BeginPackage["autoPSG`phaseSolverZ2`"]
Remove["autoPSG`phaseSolverZ2`*"]
Needs["autoPSG`definitions`"] 
Needs["autoPSG`symmetryG`"] 
Needs["autoPSG`z2Utils`"] 
Needs["autoPSG`paulis`"] 

initPSGSolverZ2::usage="initiate solver, basic associations"
decomposeGtoFMZ2::usage = "decompose matrices into phase part and matrix"
phaseSolverIterate::usage = "solve for phase parts recursively"
setIGGrules::usage = "setIGG rules"
nrel;
ApplyRules;
freds;



phaseSolverIterate[rels0_]:=Module[
{rels1,rules0,rels2,elementaryFReductions,composedFReductions,FCompositionConstraints, etaRelationConstraints,FSubstRules},
  rules0 = DeleteCases[Join[Values[FAssoc],Values[MAssoc]],Null];
(*rules0 = DeleteCases[Join[freds,Values[MAssoc]],Null];*)
  rels1=ApplyRules[rels0,rules0];
  rels1=Join@@(SplitEqMF/@rels1);
  rels1 = Join @@ (SplitFxy /@ rels1);
  rels1=relabelIndices /@ rels1;
  elementaryFReductions = Join@@(ReduceF/@rels1);
  composedFReductions= FReductions[elementaryFReductions];
  (*Print["Reductions:"];
  Print[Values[composedFReductions]//Column];*)
  Scan[(AssociateTo[FAssoc,#->composedFReductions[#]]&),Keys[composedFReductions]];
  (*Print["Vals"];
  Print[Values[FAssoc]//Column];*)

  rels1=reduceEtas[rels1];
  (*Print["after reducing etas"];
  Print[Column[rels1]];
  Print[Values[FAssoc]//Column];*)
  If[  MatchQ[rels1,rels0],
     If[  IfFSolved[rels1],
        rels1,
        (
        (*rels2=substAllMsIntoAllEqs[rels2]//z2Simplify;*)
        FSubstRules= Join@@getFSubstitutors/@rels2;
        FSubstAssoc= Association@@ ((#->{}&)/@symGenSet);
        addToFSubstAssoc[FSubstAssoc,#]&/@FSubstRules;
        rels2=Join[rels2,solveByFSubstitutions[FSubstAssoc,#]&/@rels2//z2Simplify];


        rels2 = Join @@ (SplitFxy /@ rels2);
        rels2=relabelIndices /@ rels2;
        elementaryFReductions = Join@@(ReduceF/@rels2);
        composedFReductions= FReductions[elementaryFReductions];
        Scan[(AssociateTo[FAssoc,#->composedFReductions[#]]&),Keys[composedFReductions]];
        rules0 = DeleteCases[Join[Values[FAssoc],Values[MAssoc]],Null];
        rels2=ApplyRules[rels2,rules0];
        rels2=reduceEtas[rels2];
        If[MatchQ[rels1,rels2],
        "Failed",
        phaseSolverIterate[rels2]
        ]
        )
     ],
    phaseSolverIterate[rels1]
    ]
];
updateEtaAssoc[etaRules_]:=Module[{frep},
frep[assoc_,key_,ruleSet_]:= Fold[ReplaceAll,assoc[key],ruleSet];
If[Length[etaRules]!=0,
(If[Not[KeyExistsQ[etaAssoc,#[[1]]]], AssociateTo[etaAssoc,#[[1]] -> #[[2]] ];Nothing]&)/@etaRules;,
Nothing
];
If[(Length[etaRules])!=0,(etaAssoc[#]=frep[etaAssoc,#,etaRules])&/@Keys[etaAssoc]];
Nothing 
]
reduceEtas[rels_] := Module[{etaSubRules, etaConstraintEqs, newRels},
(*Print["reducing etas from:"]
   Print[rels//Column];*)
   etaConstraintEqs =
    z2Simplify[Join @@ FindRelationConstraints /@ rels];
   etaSubRules = Join @@ RelationConstraintRule /@ etaConstraintEqs;
   (*Print["eta sub rules"];
   Print[etaSubRules];*)
   updateEtaAssoc[etaSubRules];
   newRels = rels //. etaSubRules // z2Simplify;
   (FAssoc[#] =
       FAssoc[#] //. etaSubRules // z2Simplify) & /@ Keys[FAssoc];
   (MAssoc[#] =
       MAssoc[#] //. etaSubRules // z2Simplify) & /@ Keys[MAssoc];
   DeleteTrivialEquations[newRels]
];
(****************************************)
initPSGSolverZ2[]:=(
   FAssoc=Association@@(#->(Null)&/@symGenSet);
   FSubstAssoc=Association@@((#->{})&/@symGenSet);
   MAssoc=Association@@(#->(Null)&/@symGenSet);
   ifIGGSet=Association@@(#->False&/@symGenSet);

   FAssoc = Association @@ (({#1, #2} ->Null) &) @@@ (Distribute[{symGenSet, slatList}, List]) ;
   (*FAssoc = Association @@ (({#1, #2} ->(F[#1][{defaultCoordsPattern},#2]->F[#1][{defaultCoords},#2]) &) @@@ (Distribute[{symGenSet, slatList}, List]) ;*)
   MAssoc = Association @@ (({#1, #2} ->Null) &) @@@ (Distribute[{symGenSet, slatList}, List]);
   unfixedCoordsAssoc = Association @@ (({#1, #2} ->coords) &) @@@ (Distribute[{symGenSet, slatList}, List]);
   etaAssoc=Association[];



   (MAssoc[{T1,#}]=(SU2[M[T1][#]]->SU2[\[Tau]0]);&)/@slatList; 
   (MAssoc[{T2,#}]=(SU2[M[T2][#]]->SU2[\[Tau]0]);&)/@slatList; 
   If[Not[twoDim],
     (MAssoc[{T3,#}]=(SU2[M[T3][#]]->SU2[\[Tau]0]);&)/@slatList; 
   ]
   If[twoDim,
      ( ( FAssoc[{T1,#}]=(F[T1][{x_,y_,None,#}]->\[Eta][1]^y); &)/@slatList;
        ( FAssoc[{T2,#}]=(F[T2][{x_,y_,None,#}]-> 1 ); &)/@slatList;
       ),
   
      ( (  FAssoc[{T1,#}]=(F[T1][{x_,y_,z_,#}]->1); &)/@slatList;
        (  FAssoc[{T2,#}]=(F[T2][{x_,y_,z_,#}]-> \[Eta][1]^x); &)/@slatList;
        (  FAssoc[{T3,#}]=(F[T3][{x_,y_,z_,#}]-> \[Eta][2]^y \[Eta][3]^x); &)/@slatList;
       )
   ];
   freds=DeleteCases[Values[FAssoc],Null];
   nrel=Length[symGenSet];
)

(****************************************)
decomposeGtoFMZ2[expr_]:= expr/.{SU2[G[A_]][{x_,y_,z_,s_}]-> F[A][{x,y,z,s}]SU2[M[A][s]],SU2[Inv[G[A_]]][{x_,y_,z_,s_}]-> Inv[F[A]][{x,y,z,s}] SU2[Inv[M[A][s]]]};
(****************************************)
ApplyRules[relations_,subrules_]:= Module[{temp}, 
                                    temp =relations/.SubstFormInvF/.SubstFormInvM; 
                                    temp=Fold[ReplaceAll, temp,subrules];
                                    (temp/.DispFormInvF/.DispFormInvM)//z2Simplify//DeleteTrivialEquations];

(******************************************)
(*Check if an equation o form F.F=rhs is a valid first order difference equation that can be solved*)

IfFirstOrderDEq2D[HoldPattern[Equation[Times[ Inv[F[B_]][{x1_,y1_,z1_,s1_}], F[A_][{x2_,y2_,z2_,s2_}]],rhs_]]]:=
Module[{k1,k2,k3,l1,l2,c1,c2,c3,c4},
    k1=x2-x1; k2=y2-y1; k3=z2-z1;
    l1=Level[{x1,y1,z1},{-1}]//DeleteCases[x_Integer];
    l2=Level[{x2,y2,z2},{-1}]//DeleteCases[x_Integer];
    c1=(NumericQ[k1]&&Abs[k1]<=1) && (NumericQ[k2] && Abs[k2]<= 1 )&& (NumericQ[k3] && Abs[k3]<= 1 ) &&(Abs[k1]+Abs[k2]+Abs[k3]==1);
    c2=SameQ[A,B]&&SameQ[s1,s2];
    c3=DuplicateFreeQ[l1] && DuplicateFreeQ[l2];
    c4=Not[NumericQ[x1] Or NumericQ[y1]];

    
    If[c1 && c2 && c3, 
        True,
        False
    ]
];
IfFirstOrderDEq2D[expr_]:=False;

(*assume solvable*)
(* helper functions to expand exp(log a + log b) *)
SetAttributes[expExpand, HoldAllComplete];
texp[Times[a_, x_Plus]] := Times @@ texp /@ (Times[a, #] & /@ x);
texp[Times[x_Plus]] := Times @@ texp /@ x;
(*expExpand[ex_]:=ReleaseHold[Hold[ex]/.Exp[x_]:>texp[x]];*)
expExpand[ex_] := ex /. Exp[x_] :> texp[x] /. {texp -> Exp};

(*FirstOrderDEqSolve2D[
   HoldPattern[
    Equation[Inv[F[A_]][{x1_, y1_, z1_, s_}] F[A_][{x2_, y2_, z2_, s_}],
      p_]]] := 
  Module[{k1 = x2 - x1, k2 = y2 - y1, k3 = z2 - z1, expr, a, b, c, 
    rules, rules2, at, bt, ct, range, coeffs, powers, newrhs, sol}, 
   rules = {};
   (If[MemberQ[x1, #, {0, Infinity}], 
        AppendTo[rules, # -> at];]; &) /@ {x, y, z};
   (If[MemberQ[y1, #, {0, Infinity}], 
        AppendTo[rules, # -> bt];]; &) /@ {x, y, z}; 
   (If[MemberQ[z1, #, {0, Infinity}], 
        AppendTo[rules, # -> ct];]; &) /@ {x, y, z};
   c1 = extractCoeffs[x1]; c = extractCoeffs[z1];
   c2 = extractCoeffs[y1];
   range = Range[0, 5];
   expr = p //. rules;
   If[Abs[k1] == 1,
    expr = expr //. {bt -> (1/c2[[2]]) b - c2[[3]], at -> a};
    sol = 
     RSolve[{Z[(x2 /. rules)] - Z[x1 /. rules] == Log[expr], 
       Z[0] == 0}, Z[a], a];,
    If[Abs[k2] == 1,
     expr = expr //. {at -> (1/c1[[1]]) a - c1[[3]], bt -> b}; 
     sol = RSolve[{Z[(y2 /. rules)] - Z[y1 /. rules] == Log[expr], 
        Z[0] == 0}, Z[b], b];, 
     If[Abs[k3] == 1, 
      sol = RSolve[{Z[(z2 /. rules)] - Z[z1 /. rules] == Log[expr], 
          Z[0] == 0}, Z[c], c];]]];
   (*Rsolve seems to return things in a weird {{x->y}} format*)
   newrhs = Exp[sol[[1]][[1]][[2]]];
   If[Abs[k1] == 
     1, {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{0, b, c, s}] newrhs}}, 
    If[Abs[k2] == 
      1, {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, 0, c, s}] newrhs}},
      If[Abs[k3] == 
       1, {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, b, 0, s}] newrhs}}]]]];
*)

(*FirstOrderDEqSolve2D[
   HoldPattern[
    Equation[Inv[F[A_]][{x1_, y1_, z1_, s_}] F[A_][{x2_, y2_, z2_, s_}],
      p_]]] := 
  Module[{k1 = x2 - x1, k2 = y2 - y1, k3 = z2 - z1, expr, a, b, c, 
    rules, rules2, at, bt, ct, range, coeffs, powers, newrhs, sol, c1,
     c2, c3, tmp, ca, cb}, rules = {};
   (If[MemberQ[x1, #, {0, Infinity}], 
        AppendTo[rules, # -> at];]; &) /@ {x, y, z};
   (If[MemberQ[y1, #, {0, Infinity}], 
        AppendTo[rules, # -> bt];]; &) /@ {x, y, z}; 
   (If[MemberQ[z1, #, {0, Infinity}], 
        AppendTo[rules, # -> ct];]; &) /@ {x, y, z};
   c1 = x1 /. {rules};
   c2 = y1 /. {rules};
   ca = Cases[c1, (a_ : 1) at + (c_:0) -> Sequence[a, c], {0, 1}];
   cb = Cases[c2, (a_ : 1) bt + (c_:0) -> Sequence[a, c], {0, 1}];
   expr = p //. rules;
   If[Abs[k1] == 1,
    expr = expr //. {bt -> (1/cb[[1]]) b - cb[[2]], at -> a};
    sol = 
     RSolve[{Z[(x2 /. rules /. {at -> a})] - 
         Z[x1 /. rules /. {at -> a}] == Log[expr], Z[0] == 0}, Z[a], 
      a];,
    If[Abs[k2] == 1,
     expr = expr //. {at -> (1/ca[[1]]) a - ca[[2]], bt -> b};
     sol = 
      RSolve[{Z[(y2 /. rules /. {bt -> b})] - 
          Z[y1 /. rules /. {bt -> b}] == Log[expr], Z[0] == 0}, Z[b], 
       b];, If[Abs[k3] == 1, 
      sol = RSolve[{Z[(z2 /. rules)] - Z[z1 /. rules] == Log[expr], 
          Z[0] == 0}, Z[c], c];]]];
   (*Rsolve seems to return things in a weird {{x->y}} format*)
   newrhs = Exp[sol[[1]][[1]][[2]]];
   If[Abs[k1] == 
     1, {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{0, b, c, s}] newrhs}}, 
    If[Abs[k2] == 
      1, {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, 0, c, s}] newrhs}},
      If[Abs[k3] == 
       1, {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, b, 0, s}] newrhs}}]]]];
*)
FirstOrderDEqSolve2D[
  HoldPattern[
   Equation[Inv[F[A_]][{x1_, y1_, z1_, s_}] F[A_][{x2_, y2_, z2_, s_}],
     p_]]] := 
 Module[{k1 = x2 - x1, k2 = y2 - y1, k3 = z2 - z1, expr, a, b, c, 
   rules, rules2, at, bt, ct, range, coeffs, powers, newrhs, sol, c1, 
   c2, c3, tmp, ca, cb}, rules = {};
  (If[MemberQ[x1, #, {0, Infinity}], 
       AppendTo[rules, # -> at];]; &) /@ {x, y, z};
  (If[MemberQ[y1, #, {0, Infinity}], 
       AppendTo[rules, # -> bt];]; &) /@ {x, y, z}; 
  (If[MemberQ[z1, #, {0, Infinity}], 
       AppendTo[rules, # -> ct];]; &) /@ {x, y, z};
  c1 = x1 /. {rules};
  c2 = y1 /. {rules};
  ca = Cases[c1, (a_ : 1) at + (c_ : 0) -> Sequence[a, c], {0, 1}];
  cb = Cases[c2, (a_ : 1) bt + (c_ : 0) -> Sequence[a, c], {0, 1}];
  expr = p //. rules;
  If[Abs[k1] == 1,
   expr = expr //. {at -> a};
   If[Not[FreeQ[c2, bt]],
    expr = expr //. {bt -> (1/cb[[1]]) b - cb[[2]]};
    ];
   sol = 
    RSolve[{Z[(x2 /. rules /. {at -> a})] - 
        Z[x1 /. rules /. {at -> a}] == Log[expr], Z[0] == 0}, Z[a], a];
   newrhs = Exp[sol[[1]][[1]][[2]]];
   
   If[Not[FreeQ[c2, bt]],
    {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{0, b, c, s}] newrhs}},
    
    {Rule @@ {F[A][{a_, y1, c_, s}], F[A][{0, y2, c, s}] newrhs}}
    ],
   If[Abs[k2] == 1,
    expr = expr //. {bt -> b};
    If[Not[FreeQ[c1, at]],
     expr = expr //. {at -> (1/ca[[1]]) a - ca[[2]]};
     ];
    sol = 
     RSolve[{Z[(y2 /. rules /. {bt -> b})] - 
         Z[y1 /. rules /. {bt -> b}] == Log[expr], Z[0] == 0}, Z[b], 
      b];
    newrhs = Exp[sol[[1]][[1]][[2]]];
    
    If[Not[FreeQ[c1, at]],
     {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, 0, c, s}] newrhs}},
     {Rule @@ {F[A][{x1, b_, c_, s}], F[A][{x2, 0, c, s}] newrhs}}
     ]
    ]
   ](*Rsolve seems to return things in a weird {{x->y}} format*)
  ]

       (*FirstOrderDEqSolve2Dalt[ HoldPattern[Equation[Inv[F[A_]][{x1_, y1_, z1_, s_}] F[A_][{x2_, y2_, z2_, s_}],p_]]] := 
    Module[{k1 = x2 - x1, k2 = y2 - y1, k3 = z2 - z1, expr, a, b, c, 
         rules, rules2, range, coeffs, powers, newrhs, sol}, rules = {};
         (If[MemberQ[x1, #, {0, Infinity}], 
              AppendTo[rules, # -> a];]; 
         &) /@ {x, y, z};
         (If[MemberQ[y1, #, {0, Infinity}], 
              AppendTo[rules, # -> b];]; 
         &) /@ {x, y, z};
         (If[MemberQ[z1, #, {0, Infinity}], 
              AppendTo[rules, # -> c];]; 
         &) /@ {x, y, z};
         
         range = Range[0, 5];
         expr = p //. rules;
         If[Abs[k1] == 1,
              sol = RSolve[{Z[(x2 /. rules)] - Z[x1 /. rules] == Log[expr], Z[0] == 0}, Z[a], a];,

              If[Abs[k2] == 1,
                   sol = RSolve[{Z[(y2 /. rules)] - Z[y1 /. rules] == Log[expr], Z[0] == 0}, Z[b], b];,
                   If[Abs[k3] == 1,
                        sol =  RSolve[{Z[(z2 /. rules)] - Z[z1 /. rules] == Log[expr], Z[0] == 0}, Z[c], c];
                        ]
                   ]
              ];
         (*Rsolve seems to return things in a weird {{x->y}} format*)
         newrhs = Exp[sol[[1]][[1]][[2]]];
         If[Abs[k1] == 1, 
             {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{0, b, c, s}] newrhs}}, 
             If[Abs[k2] == 1, 
                 {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, 0, c, s}] newrhs}},
                 If[Abs[k3] == 1, 
                     {Rule @@ {F[A][{a_, b_, c_, s}], F[A][{a, b, 0, s}] newrhs}}
                 ]
             ]
         ]
    ];

*)

ReduceF[HoldPattern[x_Equation]]:= 
   If[IfFirstOrderDEq2D[x],
        FirstOrderDEqSolve2D[x],
        If[AlreadySolved[x],
            RuleFromSolved[x],
            Nothing
        ]
   ]

(*First Order solutions*)
FilterReductions[F[A_],s_,reductions_]:=Cases[reductions,HoldPattern[Rule[F[A][{coord__,s}],x___]]];

FReductionsOld[reductions_]:=Module[{tempList},
tempList=
(With[{reds=FilterReductions[F[#1], #2,reductions]}, 
If[Length[reds]!=0, 
  If[FreeQ[Fold[ReplaceAll,F[#1][{defaultCoords,#2}],reds],F[#1][coord_/;(MemberQ[coord,x|y|z])]],
    {#1,#2}->(F[#1][{defaultCoordsPattern,#2}]->Fold[ReplaceAll,F[#1][{defaultCoords,#2}],reds]),
   Nothing
  ],
Nothing]]& )@@@ (Distribute[{symGenSet,slatList},List]);
tempList = tempList//.{F[A_][{0,0,0,s_}]->1,F[A_][{0,0,None,s_}]->1};
Association[tempList]
]

FReductions[reductions_]:=
Module[{tempList,rel,pred},
    tempList=
    (With[{reds=FilterReductions[F[#1], #2,reductions]}, 
    If[Length[reds]!=0, 
         pred = If[FAssoc[{#1,#2}] === Null, 

                     F[#1][{defaultCoords,#2}],
         (**Else**)
                     FAssoc[{#1,#2}][[2]]
         ];
         rel=Fold[ReplaceAll,pred,reds];
         {#1,#2}->(F[#1][{defaultCoordsPattern,#2}]->rel),

          Nothing
    ]]& )@@@ (Distribute[{symGenSet,slatList},List]);
    tempList = tempList//.{F[A_][{0,0,0,s_}]->1,F[A_][{0,0,None,s_}]->1};
    Association[tempList]
]

(* Eta Relations*)

IsolateRelationExponent[expr_,a_]:=Module[
{cases,cond},
cases= Cases[expr,(Power[__,a]|Power[__,HoldPattern[Plus[___,a,___]]]),{0,1}];
cond = Times@@cases/.{Power[b_,__]->b};
If[Length[cases]!=0,
Equation[cond,1],
Nothing]
]
FindRelationConstraints[HoldPattern[Equation[lhs_,rhs_]]]:= 
If[ FreeQ[lhs,x]&&FreeQ[lhs,y]&& FreeQ[lhs,z] && Not[FreeQ[rhs,x] && FreeQ[rhs,y] &&FreeQ[rhs,z]],
     {IsolateRelationExponent[rhs,x],
     IsolateRelationExponent[rhs,y],
     IsolateRelationExponent[rhs,x y],
     If[Not[twoDim],
        Unevaluated[Sequence[ 
          IsolateRelationExponent[rhs,z],
          IsolateRelationExponent[rhs,z x],
          IsolateRelationExponent[rhs,z y],
          IsolateRelationExponent[rhs,x y z]
      ]],
      Nothing
     ]
     },
   If[SameQ[lhs,1],
      {Equation[1,rhs]},

   (*Else*)
      Nothing
   ]
]

setIGGrules[rels_]:=
Module[ {iggAssoc, setIGGGen,ifSettable,blockGenerators, blockedGen},
iggAssoc=Association[{}];
blockedGen = {};
ifSettable[lhs_]:=Module[
{alreadySet},
(*alreadySet= (If[ifIGGSet[#]==True,#,Nothing]&)/@symGenSet;
Print[alreadySet];
And @@ Join[(EvenQ[Count[lhs,G[#],{0,Infinity}, Heads->True]]& /@alreadySet),{True}]*)
True
];

blockGenerators[lhs_,A_]:=
(If[ OddQ[Length[Cases[lhs,G[#],{0,Infinity}, Heads->True]]]&& Not[MatchQ[A,#]], AppendTo[blockedGen,#],Nothing ]&)/@symGenSet;

setIGGGen[A_,HoldPattern[Equation[lhs_,rhs_]]]:= 
If[ ifIGGSet[A]==False 
&&Not[KeyExistsQ[iggAssoc,rhs]]
&& OddQ[Count[lhs,G[A],{0,Infinity}, Heads->True]]
&& Not[MemberQ[blockedGen,A]]
&& ifSettable[lhs],
(ifIGGSet[A]=True;
iggAssoc[rhs]=True;
blockGenerators[lhs,A];
Print["Setting:",A, ", rhs:",rhs,", blocked: ",blockedGen];
Print[lhs];
rhs:>1),
Nothing];
Join@@Function[x, setIGGGen[x,#]&/@rels]/@symGenSet
]


(*RelationConstraintRule[HoldPattern[Equation[1,Times[x_,y__]]]]:=Module[{min},min= First[Last[List[y]]]; {min->Times[y*Power[min,-1]]}];*)
RelationConstraintRule[HoldPattern[Equation[1,x_]]] := {x->1};
RelationConstraintRule[HoldPattern[Equation[1,Times[y__]]]]:=Module[{min},min= Last[List[y]]; {min->Times[y*Power[min,-1]]}];


(*****Further substitutions by FM separation***)

(*SplitEqMF[HoldPattern[Equation[Verbatim[Times][x___, Verbatim[CenterDot][y__] ,z___],lhs_]]]:= (Print["nrel=",nrel];nrel=nrel+1;List[Equation[Times[x,z],\[Eta][nrel] lhs],Equation[ CenterDot[y],\[Eta][nrel]]]);
SplitEqMF[HoldPattern[Equation[lhs_,rhs_]]]:= List[Equation[lhs,rhs]];*)
SplitEqMF[ HoldPattern[Equation[Verbatim[Times][a___, Verbatim[CenterDot][b__], c___], 
              Times[lhs1_, lhs2_] /; (FreeQ[lhs1, x | y | z])]]] := 
    (List[Equation[Times[a, c], lhs2], Equation[CenterDot[b], lhs1]]);

SplitEqMF[HoldPattern[Equation[lhs_, rhs_]]] := List[Equation[lhs, rhs]];


substMIntoEq[HoldPattern[Equation[Verbatim[CenterDot][x__],rhs1_]],HoldPattern[Equation[Verbatim[CenterDot][y___,x__,z___],rhs2_]]]:= Equation[rhs1 CenterDot[y,z],rhs2]; 
substMIntoEq[HoldPattern[Equation[lhs_,rhs_]],HoldPattern[Equation[lhs2_,rhs2_]]]:=Equation[lhs2,rhs2]
substMIntoAllEqs[rels_,relNum_]:=Module[{newRels},
newRels= substMIntoEq[rels[[relNum]],#]&/@rels; 
newRels[[relNum]]=rels[[relNum]];
newRels];
substAllMsIntoAllEqs[rels_]:= Fold[substMIntoAllEqs[#1,#2]&,rels,Range[Length[rels]]];


SetAttributes[addToFSubstAssoc,HoldFirst];
addToFSubstAssoc[substAssoc_,rule:Rule[F[A_][coord_],rhs_]]:=(AppendTo[substAssoc[A],rule];)

ExtractExponent[expr_, a_] := 
 Module[{cases, cond}, 
     cases = Cases[expr, (Power[__, a] | Power[__, HoldPattern[Plus[___, a, ___]]]), {0, 1}];
     cond = Times @@ cases /. {Power[b_, x__] -> b^a};
     If[Length[cases] != 0, 
         cond, 
         1
     ]
 ]
SeparateExponents[rhs_] := 
 Association @@ ((# -> ExtractExponent[rhs, #]) & /@ {x,y})


(*This is now only for 2D unfortunately*)
SplitFxy[HoldPattern[Equation[lhs_, rhs_] /; (FreeQ[lhs, CenterDot, Heads -> True])]] :=
     Module[ {pat, compsLhs, rels1, rels2, assoc},
          pat = Longest[a__] b__ /; (FreeQ[Times[a], y] && FreeQ[Times[a], z]);
          compsLhs = 
           Cases[lhs, pat :> Sequence[Times[a], Times[b]], {0, 1}];
          If [Length[compsLhs]>1 && FreeQ[Times[compsLhs[[2]]], x] ,
              assoc = SeparateExponents[rhs];
              rels1 = Equation[Times[compsLhs[[1]]], assoc[x]];
              rels2 = Equation[Times[compsLhs[[2]]], assoc[y]];
              List[rels1, rels2],
           
              {Equation[lhs, rhs]}
          ]
     ]
SplitFxy[x_] := {x}


(* relabel terms like F(x,0)F(x+y,0) to F(x,0)F(y,0)*)
extractCoeffs[rp_] := 
  Module[{xp, cxp, ax, ay, az, ak}, xp = ExpandAll[rp];
      cxp = Cases[xp, (Verbatim[Plus][a___] | Times[a__] | x_?AtomQ) -> a, {0}];
      ax = Cases[cxp, Times[(p_ : 1), x] -> p, {1}];
      ay = Cases[cxp, Times[(p_ : 1), y] -> p, {1}];
      az = Cases[cxp, Times[(p_ : 1), z] -> p, {1}];
      If[ax === {}, ax = 0, ax = ax[[1]]];
      If[ay === {}, ay = 0, ay = ay[[1]]];
      If[az === {}, az = 0, az = az[[1]]];
      ak = rp - ax x - ay y - az z;
      {ax, ay, ak}
  ];
(*2dimensional only so far*)
getInvRules[newcoords_] := 
  Module[{coord1, coord2, func, rpp}, coord1 = {x, y};
      coord2 = newcoords;
      func[{xp_, yp_}] := 
      Module[{m, mI, rp, a, b, c}, rp = {Null, Null, Null};
          a = extractCoeffs[xp];
          b = extractCoeffs[yp];
          m = {Take[a, 2], Take[b, 2]};
          mI = Inverse[m];
          rp = mI . {x - a[[3]], y - b[[3]]};
          rp
      ];
      rpp = func[coord2];
      {x -> rpp[[1]], y -> rpp[[2]]}
  ];
(*delete duplicates upto a minus sign*)
uniques[{x_}] := {x};
uniques[{}] := Nothing;
uniques[syms_] := 
    Join[{syms[[1]]}, If[ syms[[1]] === -#, Nothing, #] & /@ uniques[Drop[syms, 1]]];

relabelIndices[eq_Equation] := Module[{labels, uLabels, rules},
    (*collect arguments x,y,x+y etc appearing in equations*)
    labels = (eq[[1]] // Cases[x_ -> x] // 
      Cases[F[A_][{x__}] -> x]) //. {x__Integer + y___ :> Plus[y]} // 
        DeleteDuplicates // DeleteCases[x_Integer] // DeleteCases[None];
    uLabels = uniques[labels];
    If[Length[labels]==0,uLabels={},uLabels=Complement[uniques[labels],slatList]];
    If[Length[uLabels] == nDim  && Length[Complement[{x, y}, uLabels]] != 0, 
     eq2=eq /. getInvRules[uLabels];eq2, 
     eq
    ]
                       
]

RuleFromSolved[HoldPattern[Equation[(t1_?IfFOrInvF)[{x1_, y1_, z1_, s1_}], rhs_]]] := 
    Module[{x1n, y1n, x2n, y2n, rule1, rule2, rule3, rule4, svar, subrules, PattFunc},
         svar[0] = 0;
         svar[Plus[Times[x, m_ : 1], k_ : 0]] := a;
         svar[Plus[Times[y, m_ : 1], k_ : 0]] := b;
         svar[Plus[Times[z, m_ : 1], k_ : 0]] := c;
         svar[m_] := m;
         subrules[Plus[Times[x, m_ : 1], k_ : 0]] := x -> m^-1 (a - k);
         subrules[Plus[Times[y, m_ : 1], k_ : 0]] := y -> m^-1 (b - k);
         subrules[Plus[Times[z, m_ : 1], k_ : 0]] := y -> m^-1 (c - k);
         subrules[0] = Nothing;
         subrules[x_Integer] = Nothing;
         subrules[None] := Nothing;
         PattFunc[None] := None;
         PattFunc[0] := 0;
         PattFunc[m_ /; MemberQ[slatList, m]] := m;
         PattFunc[x_] := Pattern[x, _];
         If[ MatchQ[t1, Inv[A_]], 
             rule1 = Inv[t1][PattFunc /@ {svar[x1], svar[y1], svar[z1], 
                  s1}] -> ((rhs^-1) /. {subrules[x1], subrules[y1], subrules[z1]}),
             rule1 = t1[PattFunc /@ {svar[x1], svar[y1], svar[z1], 
                  s1}] -> (rhs /. {subrules[x1], subrules[y1], subrules[z1]})
         ];
         
         List[rule1]
    ]

AlreadySolved[HoldPattern[Equation[(t1_?IfFOrInvF)[{x_, y_, z_,slat_}], rhs_]]] := True
AlreadySolved[x_] := False

(*Remove redudant phases--- setting the IGG-- must think about U(1) generalisation*)

removableEtas[]:=
Module[{gauge,etaGauges,etas,checks},
    gauge[{x_, y_, z_, s_}] = \[Eta][X]^x \[Eta][Y]^y \[Eta][X + Y]^(x + y);
    etaGauges = {\[Eta][X], \[Eta][Y], \[Eta][X + Y]};
    etas = Cases[FAssoc, \[Eta][x_] -> \[Eta][x], {0, Infinity}] // DeleteDuplicates;
    checks=Module[{tmat1,tmat2,tmp,mtmp,f},
        f=Function[p,
        ((FAssoc[p][[2]] gauge[{x, y, None, None}] gauge[Inv[p[[1]]][{x, y, None, p[[2]]}]]) // z2Simplify) ];
        tmp = f/@ Distribute[{symGenSet, slatList}, List];
        mtmp = tmp /. {\[Eta][x_] -> Exp[\[Eta][x]]} // PowerExpand;
        mtmp = Cases[mtmp, Exp[x_] -> x];
        t1 = Table[Coefficient[mtmp[[j]], etas[[i]]], {i, 1, Length[etas]}, {j, 1, Length[mtmp]}];
        t2 = Table[Coefficient[mtmp[[j]], etaGauges[[i]]], {i, 1, Length[etaGauges]}, {j, 1, Length[mtmp]}];
        tmat = t1[[ConstantArray[#, Length[etaGauges]]]];
        tmat2 = t2 - tmat;
        Or @@ Table[And @@ Table[FreeQ[tmat2[[j]], i], {i, {defaultCoords}}], {j, 1, Length[etas]}]
    ]& /@ Range[Length[etas]];
    If[checks[[#]],etas[[#]]-> 1,Nothing]&/@Range[Length[etas]]
] 

(*substitute F equations into others to get solvable equations*)

IfFOrInvF[a_]:=MatchQ[a,F[A_]] || MatchQ[a,Inv[F[A_]]];
(*Again assume that the symmetries don't take a site at [x,y] to [x+y,x-y]*)
(*Unreasonable assumption, see triangular lattice, changes req*)
(* One could try more general substitutors from full F equations*)
getFSubstitutors[HoldPattern[Equation[Times[(t1_?IfFOrInvF)[{x1_,y1_,z1_,s1_}],(t2_?IfFOrInvF)[{x2_,y2_,z2_,s2_}]] ,rhs_]]]:= 
Module[{x1n,y1n,x2n,y2n,rule1,rule2,rule3,rule4,svar,subrules,PattFunc},
       svar[Plus[Times[x, m_:1],k_:0]]:=a;
       svar[Plus[Times[y, m_:1],k_:0]]:=b;
       svar[Plus[Times[z, m_:1],k_:0]]:=c;
       svar[m_]:=m;
       subrules[Plus[Times[x, m_:1],k_:0]]:= x->m^-1 (a-k);
       subrules[Plus[Times[y, m_:1],k_:0]]:= y->m^-1 (b-k);
       subrules[Plus[Times[z, m_:1],k_:0]]:= y->m^-1 (c-k);
       subrules[None]:=Nothing;
       x2n=x2/.{subrules[x1],subrules[y1],subrules[z1]};
       y2n=y2/.{subrules[x1],subrules[y1],subrules[z1]};
       z2n=z2/.{subrules[x1],subrules[y1],subrules[z1]};

       x1n=x1/.{subrules[x2],subrules[y2],subrules[z2]};
       y1n=y1/.{subrules[x2],subrules[y2],subrules[z2]};
       z1n=z1/.{subrules[x2],subrules[y2],subrules[z2]};

       PattFunc[None]:=None;
       PattFunc[m_/;MemberQ[slatList,m]]:=m;
       PattFunc[x_] := Pattern[x,_];

       If[MatchQ[t1,Inv[A_]],
            rule1=Inv[ t1][ PattFunc/@{svar[x1],svar[y1],svar[z1],s1} ]-> ( t2[{#1 ,#2,#3,#4}]rhs^-1)&[x2n,y2n,z2n,s2],

            rule1=t1[PattFunc/@{svar[x1],svar[y1],svar[z1],s1}]-> ( Inv[t2][{#1 ,#2,#3,#4}]rhs)&[x2n,y2n,z2n,s2]
       ];
       If[MatchQ[t2,Inv[A_]],
            rule2=Inv[ t2][ PattFunc/@{svar[x2],svar[y2],svar[z2],s2} ]-> ( t1[{#1 ,#2,#3,#4}]rhs^-1)&[x1n,y1n,z1n,s1],

            rule2=t2[PattFunc/@{svar[x2],svar[y2],svar[z2],s2}]-> ( Inv[t1][{#1 ,#2,#3,#4}]rhs)&[x1n,y1n,z1n,s1]
       ];
       ;
       List[rule1,rule2]
]

getFSubstitutors[HoldPattern[x__Equation]]:=Nothing
substituteFRule[F1_,F2_,rhs_,rule_,subpart_]:=
    Module[{newF,newEq},
         Which[
             subpart==1,
                 (newF=F1//.SubstFormInvF/.rule//.DispFormInvF;
                 newEq=Equation[Times[newF,F2],rhs];),
             subpart==2,
                 (newF=F2//.SubstFormInvF/.rule//.DispFormInvF;
                 newEq=Equation[Times[F1,newF],rhs];)
         ];
         If[IfFirstOrderDEq2D[newEq],
             newEq,
             Nothing
         ]
    ]

solveByFSubstitutions[FSubstAssoc_,HoldPattern[eq:Equation[Times[(F1:F[A_][coord1_]|Inv[F[A_]][coord1_]),(F2:F[B_][coord2_]|Inv[F[B_]][coord2_])],rhs_]]]:=
Module[{newList},
  newList=((substituteFRule[F1,F2,rhs,#,1]&)/@FSubstAssoc[A]);
  If[Length[newList]!=0,
    First[newList],
    If[Not[SameQ[A,B]],
      (newList=(substituteFRule[F1,F2,rhs,#,2]&)/@FSubstAssoc[B];
      If[Length[newList]!=0 && Not[SameQ[A,B]],
         First[newList],
         Nothing
      ]),
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

Begin["Private`"]

End[]

EndPackage[]
