BeginPackage["psgSolver`z2Utils`"]
Remove["psgSolver`z2Utils`*"]
\[Eta]::usage = "Z2 phases"
\[Phi]::usage = "U1 phases"
z2Simplify::usage = "simplify expressions by reudcing phases eta[x]"

Begin["Private`"]
SeparatePowers =
With[{VPower=Verbatim[Power],VPlus=Verbatim[Plus],VTimes=Verbatim[Times]},
{VPower[VTimes[a__],b_]:> Inactive[Times]@@((Power[#,b]&)/@(List[a])),
 VPower[VPower[a_,b_],c_]:> Power[a,Times[b,c]], 
VPower[a__,VPlus[b__]]:>Inactive[Times]@@((Power[a,#]&)/@List[b]), 
VPower[a_,VTimes[c__/;MemberQ[List[c],VPlus,{2},Heads->True]]]:>  Power[a,Distribute[Times[c]]],
VPower[a_,VPlus[VTimes[c__/;MemberQ[List[c],VPlus,{2},Heads->True]],b__]]:> Power[a,Map[Distribute,Plus[b,Times[c]],Infinity]]}];  

z2rules={\[Eta][x_]^Times[j_?Negative,k_]-> \[Eta][x]^(-k j), 
\[Eta][x_]^Times[j_?EvenQ ,m_:1]->1,
\[Eta][x_]^Times[j_?OddQ  ,m_:1]->\[Eta][x],
\[Eta][x_]^Power[j_,n_]-> \[Eta][x]^ j
};
SeparateAndApplyZ2[expr_]:= (expr//.SeparatePowers//.z2rules//.{Inactive[Times]->Times});             
z2Simplify[expr_]:=FixedPoint[SeparateAndApplyZ2,expr];                                                                                                                           
End[]
EndPackage[]
