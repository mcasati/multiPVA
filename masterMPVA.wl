(* ::Package:: *)

BeginPackage["masterMPVA`"];

Print["Multiplicative PVA: a Mathematica package for working with multiplicative Poisson Vertex Algebras"];
Print["Second version (2025). M. Casati (inherits from MC, D. Valeri 2021)"];
Print["NOTE: Preliminary version, the multidimensional case does not work well"];

Clear["masterMPVA`*"];
Clear["masterMPVA`Private`*"];



(*Explain meaning of the functions*)
SetN::usage="It sets the number of generators of the PVA. Default=1";
SetD::usage="It sets the dimension of the lattice. Default=1";
GetN::usage="It gives the number of generators of the PVA. Default=1";
GetD::usage="It gives th dimensions of the lattice. Default=1";
SetMaxO::usage="It sets the max order of shifts to which to compute the bracket. Default=5";
GetMaxO::usage="It gives the max order of shifts to which to compute the bracket. Default=5";
gen::usage="gen is the array of the generators";
S::usage="shift operator";
SetGenName::usage="It sets the standard name for the generators of PVA. Default=u";
GetGenName::usage="It gives the name for the generators of PVA. Default=u";
CompB::usage="It computes the compatibility condition between two lambda brackets evaluated on a triple of generators (equivalent to the Schouten bracket between the corresponding bivectors)";
SetFormalParameter::usage="It sets the formal variable used in the definition of the bracket. Default=\[Beta]";
GetFormalParameter::usage="It gives the formal variable used in the definition of the bracket. Default=\[Beta]";
SkewCheck::usage="PVASkew computes the condition of (skew)symmetry [optional parameter for symmetry] for a lambda bracket and returns a matrix";
CompatCheck::usage="Computes the compatibility condition between two brackets and gives the list of its independent entries. It is equivalent to the PVA-Jacobi identity if computed between two copies on the same bracket";
mLambdaB::usage="Computes the multiplicative lambda bracket (for compatibility)";


gen:=If[$d==1&&$r==1,{$genname[0]},If[$r==1,Array[Subscript[$genname, #][0]&,$d],If[$d==1,{$genname[Table[0,{ind,$r}]]},Array[Subscript[$genname, #][Table[0,{ind,$r}]]&,$d]]]];
S[a_,d_,p_]:=If[$r!=1,If[$d==1,a/.$genname[n_List]:>$genname[n+Table[p KroneckerDelta[d,ind],{ind,$r}]],a/.Subscript[$genname,r_][n_List]:>Subscript[$genname,r][n+Table[p,KroneckerDelta[d,ind],{ind,$r}]]]];
S[a_,p_]:=If[$r==1,If[$d==1,a/.$genname[n_]:>$genname[n+p],a/.Subscript[$genname,r_][n_]:>Subscript[$genname,r][n+p]]];
MS[arg_,MInd_List]:=Fold[S[#1,#2[[1]],#2[[2]]]&,arg,ConvMInd[MInd]];


Begin["`Private`"];
$d=1;
$ltail=1;
$maxO=5;
$genname=u;
$parname=\[Beta];
$\[Beta]\[Beta]:=If[$r==1,{$parname},Array[Subscript[$parname,#]&,$r]];
SetN[newd_Integer]:=Module[{},$d=newd];
SetD[newd_Integer]:=Module[{},$r=newd];
GetN[]:=$d;
SetD[]:=$r;
SetMaxO[new_Integer]:=Module[{},$maxO=new];
GetMaxO[]:=$maxO;
SetGenName[newname_]:=Module[{},$genname=newname];
GetGenName[]:=$genname;
SetFormalParameter[newname_]:=Module[{},$parname=newname];
GetFormalParameter[]:=$parname;
ConvMInd[MInd_List]:=Table[{i,MInd[[i]]},{i,$r}];


LaurentCoeff[arg_,var_List]:=Module[{e,mod,coeflist},e=Table[Exponent[arg,var[[s]],Min],{s,Length[var]}];mod=Expand[Product[var[[s]]^(-e[[s]]),{s,Length[var]}]arg];coeflist=CoefficientRules[mod,var];Table[{coeflist[[i,1]]+e,coeflist[[i,2]]},{i,Length[coeflist]}]];
Term3D[f_,m_List,i_,\[Alpha]_List]:=Product[\[Alpha][[ind]]^(-m[[ind]]),{ind,$r}] MS[D[f,MS[gen[[i]],m]],-m];
Term2D[f_,P_,i_,j_,\[Alpha]_,\[Lambda]_]:=Module[{ListIndex},If[$r==1,ListIndex=LaurentCoeff[P[[j,i]],{\[Lambda]}],ListIndex=LaurentCoeff[P[[j,i]],Table[Subscript[\[Lambda],jnd],{jnd,$r}]]];If[ListIndex=={},0,Total[Table[ListIndex[[k,2]]*Product[\[Alpha][[\[ScriptI]]]^ListIndex[[k,1,\[ScriptI]]],{\[ScriptI],$r}]*MS[f,ListIndex[[k,1]]],{k,Length[ListIndex]}]]]];
Term1D[f_,m_,g_,j_,\[Alpha]_]:=D[g,MS[gen[[j]],m]]*Product[\[Alpha][[ind]]^m[[ind]],{ind,$r}]*MS[f,m];
ListaMultiIndici:=Module[{IndexFamily=Array[Subscript[i, #]&,$r],Mi=Table[0,{l,$r}]},Flatten[Table[For[k=0,k<$r,k++,Mi[[k+1]]=IndexFamily[[k+1]]];Mi,##]&@@({IndexFamily[[#]],-$maxO,$maxO} &/@Range[$r]),$r-1]];
Lambdamnij[f_,g_,m_,n_,i_,j_,P_,\[Alpha]_]:=Term1D[Term2D[Term3D[f,m,i,\[Alpha]],P,i,j,\[Alpha],$parname],n,g,j,\[Alpha]];
mLambdaB[f_,g_,P_,\[Alpha]_]:=Module[{\[Gamma]},If[$r==1,\[Gamma]={\[Alpha]},\[Gamma]=\[Alpha]];Sum[Lambdamnij[f,g,ListaMultiIndici[[m]],ListaMultiIndici[[n]],i,j,P,\[Gamma]],{m,1,(2*$maxO+1)^$r},{n,1,(2*$maxO+1)^$r},{i,1,$d},{j,1,$d}]];


(*Skewsymmetry*)
SkewLoc[Ploc_,i_,j_,\[Lambda]_]:=If[$r==1,Simplify[Expand[Ploc[[i,j]]]/.{Times[\[Lambda]^n_, e_] :>\[Lambda]^(-n)S[e,-n],Times[\[Lambda],e_]:>\[Lambda]^(-1)S[e,-1],\[Lambda]^n_:>\[Lambda]^(-n),\[Lambda]:>\[Lambda]^(-1)}],Simplify[Expand[Ploc[[i,j]]]/.{Times[Subscript[\[Lambda], t_]^n_, e_] :>Subscript[\[Lambda], t]^(-n)S[e,t,-n],Times[Subscript[\[Lambda], t_],e_]:>Subscript[\[Lambda], t]^(-1)S[e,t,-1],Subscript[\[Lambda], t_]^n_:>Subscript[\[Lambda], t]^(-n),Subscript[\[Lambda], t_]:>Subscript[\[Lambda], t]^(-1)}]];
SkewCheck[P_,par_,s_:0]:=Table[Simplify[P[[i,j]]+(-1)^s SkewLoc[P,j,i,par]],{i,$d},{j,$d}];


Integr[expr_,param_List]:=Module[{lastpar=Last[param],l=Length[param]-1,dummy},dummy=Collect[expr,lastpar];dummy=Collect[dummy/.{Times[lastpar^n_, e_] :>Product[param[[i]]^(-n),{i,l}]S[e,-n],Times[lastpar,e_]:>Product[param[[i]]^(-1),{i,l}]*S[e,-1],lastpar:>Product[param[[i]]^(-1),{i,l}]},lastpar];dummy];


(*Schouten bracket auxiliary*)
SchLL[Ploc_,Qloc_,i_,j_,k_,\[Lambda]_,\[Mu]_]:=Module[{dummy},dummy=Qloc//.$parname->\[Mu];mLambdaB[gen[[i]],dummy[[k,j]],Ploc,\[Lambda]]];
SchBracket[P_,Q_,i_,j_,k_,\[Lambda]_,\[Mu]_,\[Nu]_]:=SchLL[P,Q,i,j,k,\[Lambda],\[Mu]]+SchLL[Q,P,i,j,k,\[Lambda],\[Mu]]-(SchLL[P,Q,j,i,k,\[Mu],\[Lambda]]+SchLL[Q,P,j,i,k,\[Mu],\[Lambda]])+SchLL[P,Q,k,i,j,\[Nu],\[Lambda]]+SchLL[Q,P,k,i,j,\[Nu],\[Lambda]];


CompB[PFull_,QFull_,i_,j_,k_,param_List]:=Module[{dummy},dummy=SchBracket[PFull,QFull,i,j,k,param[[1]],param[[2]],param[[3]]];dummy=Integr[dummy,param];Return[dummy]];
CompatCheck[PFull_,QFull_,param_List]:=Module[{listJacobi={},dummyentr},For[i=1,i<=$d,i++,For[j=i,j<=$d,j++,For[k=j,k<=$d,k++,dummyentr=CompB[PFull,QFull,i,j,k,param];AppendTo[listJacobi,dummyentr=Simplify[dummyentr]];Print[dummyentr]]]];Return[listJacobi]];


End[ ];
EndPackage[];
