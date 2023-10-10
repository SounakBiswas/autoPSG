
slatList={\[Alpha],\[Beta], \[Gamma], \[Delta]}
twoDim=False
noBasis=False

(*symGenSet={Tx, Ty, Tz,ga,gb,gc};*)
symGenSet={Tx, Ty, Tz,ga,gb,gc,T};
inputRelators = {
   {Tx - 1, Ty - 1, Tx, Ty},
   {Ty - 1, Tz - 1, Ty, Tz},
   {Tz - 1, Tx-1, Tz, Tx},
   {gc, gc, gc},
   {Tz - 1, ga, ga},
   {Ty - 1, gb, gb},
   {ga - 1, Tx, ga, Tx},
   {ga - 1, Ty, ga, Ty},
   {ga - 1, Tz - 1, ga, Tz},
   {gb - 1, Tx, gb, Tx},
   {gb - 1, Ty - 1, gb, Ty},
   {gb - 1, Tz, gb, Tz},
   {gc - 1, Ty - 1, gc, Tx},
   {gc - 1, Tz - 1, gc, Ty},
   {gc - 1, Tx - 1, gc, Tz},
   {ga - 1, gc - 1, gb - 1, Tx - 1, Ty, ga, gc},
   {gb - 1, ga - 1, Tx, Ty - 1, Tz, gb, ga},
   {gc - 1, gb - 1, Tx - 1, Ty, ga, gb, gc, gb}
   ,{T-1, Tx-1,T,Tx},
   {T-1, Ty-1,T,Ty},
   {T-1, Tz-1,T,Tz},
   {T-1, ga-1,T,ga},
   {T-1, gb-1,T,gb},
   {T-1, gc-1,T,gc},
   {T,T}
   };

Tx[{x_,y_,z_,s_}]={x+1,y,z,s}
Ty[{x_,y_,z_,s_}]={x,y+1,z,s}
Tz[{x_,y_,z_,s_}]={x,y,z+1,s}
ga[{x_,y_,z_,\[Alpha]}]={-x,-y-1,z,\[Delta]}
ga[{x_,y_,z_,\[Beta]}]={-x-1,-y-1,z+1,\[Gamma]}
ga[{x_,y_,z_,\[Gamma]}]= {-x-1, -y-1,z,\[Beta]}
ga[{x_,y_,z_,\[Delta]}]={-x,-y-1,z+1,\[Alpha]}

gb[{x_,y_,z_,\[Alpha]}]={-x-1,y,-z,\[Gamma]}
gb[{x_,y_,z_,\[Beta]}]={-x-1,y,-z-1,\[Delta]}
gb[{x_,y_,z_,\[Gamma]}]={-x-1,y+1,-z,\[Alpha]}
gb[{x_,y_,z_,\[Delta]}]={-x-1,y+1,-z-1,\[Beta]}

gc[{x_,y_,z_,\[Alpha]}]={z,x,y,\[Alpha]}
gc[{x_,y_,z_,\[Beta]}]= {z,x,y,\[Gamma]}
gc[{x_,y_,z_,\[Gamma]}]= {z,x,y,\[Delta]}
gc[{x_,y_,z_,\[Delta]}]={z,x,y,\[Beta]}

T[{x_,y_,z_,s_}]={x,y,z,s}
