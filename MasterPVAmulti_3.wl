(* ::Package:: *)

BeginPackage["MasterPVAmulti`"];

Print["MasterPVAmulti: a Mathematica package for computing the lambda bracket of a Poisson Vertex Algebra of arbitrary rank"];
Print["Third version (2023). M. Casati & D. Valeri"];

Clear["MasterPVAmulti`*"];
Clear["MasterPVAmulti`Private`*"];



(*Explain meaning of the functions*)
SetN::usage="It sets the number of generators of the PVA. Default=1";
GetN::usage="It gives the number of generators of the PVA. Default=1";
SetD::usage="It sets the number of derivations of the PVA. Default=1";
GetD::usage="It gives the number of derivations of the PVA. Default=1";
SetMaxO::usage="It sets the max order of derivatives to which to compute the bracket. Default=5";
GetMaxO::usage="It gives the max order of derivatives to which to compute the bracket. Default=5";
gen::usage="gen is the array of the generators";
var::usage="var is the array of the independent variables";
SetGenName::usage="It sets the standard name for the generators of PVA. Default=u";
GetGenName::usage="It gives the name for the generators of the PVA. Default=u";
SetVarName::usage="It sets the name for the independent variable. Default=x";
GetVarName::usage="It gives the name for the independent variable. Default=x";
LambdaB::usage="LambdaB[f,g,P,{\[Lambda]}] is the function which computes the lambda bracket of the functions f and g with respect to the structure P, written as a polynomial in the indeterminate \[Beta], with respect to the indeterminate \[Lambda]";
Integr::usage="Integr[expression,{{\[Lambda]},{\[Mu]},{\[Nu]},{\[Rho]},...}] maps polynomials in the formal variables \[Lambda],...,\[Psi],\[Omega] in polynomials replacing \[Omega] with -\[Lambda]-\[Mu]-...-\[PartialD]";
SetFormalParameter::usage="It sets the formal variable used in the definition of the bracket. Default=\[Beta]";
GetFormalParameter::usage="It gives the formal variable used in the definition of the bracket. Default=\[Beta]";
PVASkew::usage="PVASkew computes the condition of skewsymmetry for a lambda bracket and returns a matrix";
PrintPVASkew::usage="PrintPVASkew computes the condition of skewsymmetry for a lambda bracket and returns a table with the list of result for the single generators. Useful for checking the properties of a generic bracket";
JacobiCheck::usage="Jacobi check computes the terms of the PVA-Jacobi identity for all the triples of generators and returns an array of results";
PrintJacobiCheck::usage="PrintJacobiCheck computes the terms of PVA-Jacobi identity and returns a table with the values of the (i,j,k) entries of the Jacobiator";
EvVField::usage="Apply the evolutionary vector field of given characteristic to a function ";
CompatCheck::usage="Compute the Schouten bracket between two structures (P and Q are the bivectors)";


var:=If[$r==1,{$varname},Array[Subscript[$varname, #]&,$r]];
gen:=If[$d==1,{$genname[Sequence@@var]},Array[Subscript[$genname, #][Sequence@@var]&,$d]];


Begin["`Private`"];
$d=1;
$r=1;
$parname=\[Beta];
$genname=u;
$varname=x;
$\[Beta]\[Beta]:=If[$r==1,{$parname},Array[Subscript[$parname, #]&,$r]];
$maxO=5;

SetN[newd_Integer]:=Module[{},$d=newd];
GetN[]:=$d;
SetD[newr_Integer]:=Module[{},$r=newr];
GetD[]:=$r;
SetMaxO[newmaxo_Integer]:=Module[{},$maxO=newmaxo];
GetMaxO[]:=$maxO;
SetGenName[newname_]:=Module[{},$genname=newname];
GetGenName[]:=$genname;
SetVarName[newname_]:=Module[{},$varname=newname];
GetVarName[]:=$varname;
SetFormalParameter[newname_]:=Module[{},$parname=newname];
GetFormalParameter[]:=$parname;



myD[{arg_,MInd_},j_]:={Nest[D[#,var[[j]]]&,arg,MInd[[j]]],MInd};
MultiD[arg_,MInd_]:=Fold[myD,{arg,MInd},Range[$r]][[1]];
DLambda[{arg_,\[Lambda]_,MInd_},j_]:={Nest[\[Lambda][[j]] #+D[#,var[[j]]]&,arg,MInd[[j]]],\[Lambda],MInd};
DLambdamin[{arg_,\[Lambda]_,MInd_},j_]:={Nest[-\[Lambda][[j]] *#-D[#,var[[j]]]&,arg,MInd[[j]]],\[Lambda],MInd};
MultiDLambda[arg_,\[Lambda]_,MInd_]:=Fold[DLambda,{arg,\[Lambda],MInd},Range[$r]][[1]];
MultiDLambdamin[arg_,\[Lambda]_,MInd_]:=Fold[DLambdamin,{arg,\[Lambda],MInd},Range[$r]][[1]];
Integr[expr_,paramlist_List]:=Module[{lastpar,l,dummy,parlist},If[$r==1,parlist=Map[List,paramlist],parlist=paramlist];lastpar=Last[parlist];l=Length[parlist]-1;dummy=Collect[expr,lastpar];For[k=0,k<$r,k++,dummy=dummy/.{Times[lastpar[[k+1]]^n_, e_] :>Nest[-Sum[parlist[[i,k+1]],{i,l}]*#-D[#,var[[k+1]]]&,e,n],Times[lastpar[[k+1]],e_]:>Times[-Sum[parlist[[i,k+1]],{i,l}],e]-D[e,var[[k+1]]],lastpar[[k+1]]:>-Sum[parlist[[i,k+1]],{i,l}]}];Simplify[dummy]];


Term3D[f_,MInd_,i_,\[Alpha]_]:=MultiDLambdamin[D[f,MultiD[gen[[i]],MInd]],\[Alpha],MInd];
Term2D[f_,P_,i_,j_,\[Alpha]_]:=Module[{ListIndex=CoefficientRules[P[[j,i]],$\[Beta]\[Beta]]/.Rule->List},If[ListIndex=={{}},0,Total[Table[ListIndex[[k,2]]*MultiDLambda[f,\[Alpha],ListIndex[[k,1]]],{k,Length[ListIndex]}]]]];
Term1D[f_,MInd_,g_,j_,\[Alpha]_]:=D[g,MultiD[gen[[j]],MInd]]*MultiDLambda[f,\[Alpha],MInd];
Lambdamnij[f_,g_,Multi1_,Multi2_,i_,j_,P_,\[Alpha]_]:=Term1D[Term2D[Term3D[f,Multi1,i,\[Alpha]],P,i,j,\[Alpha]],Multi2,g,j,\[Alpha]];
ListaMultiIndici:=Module[{IndexFamily=Array[Subscript[i, #]&,$r],Mi=Table[0,{l,$r}]},Flatten[Table[For[k=0,k<$r,k++,Mi[[k+1]]=IndexFamily[[k+1]]];Mi,##]&@@({IndexFamily[[#]],0,$maxO} &/@Range[$r]),$r-1]];
LambdaB[f_,g_,P_,\[Alpha]_]:=Module[{\[Gamma]},If[$r==1,\[Gamma]={\[Alpha]},\[Gamma]=\[Alpha]];Sum[Lambdamnij[f,g,ListaMultiIndici[[m]],ListaMultiIndici[[n]],i,j,P,\[Gamma]],{m,1,($maxO+1)^$r},{n,1,($maxO+1)^$r},{i,1,$d},{j,1,$d}]];
EvVField[X_,f_]:=Sum[MultiD[X[[i]],ListaMultiIndici[[m]]]D[f,MultiD[gen[[i]],ListaMultiIndici[[m]]]],{m,1,($maxO+1)^$r},{i,$d}];


(*Skewsymmetry*)
Skew[P_,i_,j_]:=Module[{dummy=P[[j,i]]},For[k=0,k<$r,k++,dummy=dummy/.{Times[$\[Beta]\[Beta][[k+1]]^n_, e_] :>Nest[-$\[Beta]\[Beta][[k+1]]*#-D[#,var[[k+1]]]&,e,n],Times[$\[Beta]\[Beta][[k+1]],e_]:>Times[-$\[Beta]\[Beta][[k+1]],e]-D[e,var[[k+1]]],$\[Beta]\[Beta][[k+1]]:>-$\[Beta]\[Beta][[k+1]]}];dummy];
PVASkew[P_]:=Table[Simplify[P[[i,j]]+Skew[P,i,j]],{i,$d},{j,$d}];
PrintPVASkew[P_]:=TableForm[Partition[Flatten[Table[{HoldForm[i]==i,HoldForm[j]==j,Simplify[P[[i,j]]+Skew[P,j,i]]},{j,1,$d},{i,1,$j}]],3],TableSpacing->{2,2}];


(*Jacobi identity*)
Jacobi[i_,j_,k_,P_]:=Module[{\[Lambda]\[Lambda],\[Mu]\[Mu],\[Nu]\[Nu]},If[$r==1,\[Lambda]\[Lambda]={\[Lambda]};\[Mu]\[Mu]={\[Mu]};\[Nu]\[Nu]={\[Nu]},\[Lambda]\[Lambda]=Array[Subscript[\[Lambda], #]&,$r];\[Mu]\[Mu]=Array[Subscript[\[Mu], #]&,$r];\[Nu]\[Nu]=Array[Subscript[\[Nu],#]&,$r]];LambdaB[gen[[i]],LambdaB[gen[[j]],gen[[k]],P,\[Mu]\[Mu]],P,\[Lambda]\[Lambda]]-LambdaB[gen[[j]],LambdaB[gen[[i]],gen[[k]],P,\[Lambda]\[Lambda]],P,\[Mu]\[Mu]]+Integr[LambdaB[gen[[k]],LambdaB[gen[[i]],gen[[j]],P,\[Lambda]\[Lambda]],P,\[Nu]\[Nu]],{\[Lambda]\[Lambda],\[Mu]\[Mu],\[Nu]\[Nu]}]];
JacobiCheck[P_]:=Table[Simplify[Jacobi[i,j,k,P]],{i,1,$d},{j,1,$d},{k,1,$d}];
PrintJacobiCheck[P_]:=TableForm[Partition[Flatten[Table[{HoldForm[i]==i,HoldForm[j]==j,HoldForm[k]==k,Simplify[Jacobi[i,j,k,P]]},{k,1,$d},{j,1,$d},{i,1,$d}]],4],TableSpacing->{2,2}];


(*Compatibility*)
SchLL[Ploc_,Qloc_,i_,j_,k_,\[Lambda]_,\[Mu]_]:=Module[{dummy},dummy=If[$r==1,Qloc//.$parname->\[Mu],Qloc//.$parname->\[Mu][[1,1]]];LambdaB[gen[[i]],dummy[[k,j]],Ploc,\[Lambda]]];
SchBracket[P_,Q_,i_,j_,k_,\[Lambda]_,\[Mu]_,\[Nu]_]:=SchLL[P,Q,i,j,k,\[Lambda],\[Mu]]+SchLL[Q,P,i,j,k,\[Lambda],\[Mu]]-(SchLL[P,Q,j,i,k,\[Mu],\[Lambda]]+SchLL[Q,P,j,i,k,\[Mu],\[Lambda]])+SchLL[P,Q,k,i,j,\[Nu],\[Lambda]]+SchLL[Q,P,k,i,j,\[Nu],\[Lambda]];
CompB[PFull_,QFull_,i_,j_,k_,param_List]:=Module[{dummy},dummy=SchBracket[PFull,QFull,i,j,k,param[[1]],param[[2]],param[[3]]];dummy=Integr[dummy,param];Return[dummy]];
CompatCheck[PFull_,QFull_,param_List]:=Module[{i=1,j=1,k=1,listJacobi={},dummyentr},For[i=1,i<=$d,i++,For[j=i,j<=$d,j++,For[k=j,k<=$d,k++,dummyentr=CompB[PFull,QFull,i,j,k,param];AppendTo[listJacobi,dummyentr=Simplify[dummyentr]];Print[{i,j,k},dummyentr]]]];Return[listJacobi]];


End[ ];
EndPackage[];
