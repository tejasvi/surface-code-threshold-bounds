import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12576 = true := by
  decide +kernel

theorem tot12576 : totK PD2M8K2 D2M8K2.t12576 = [0, 171971992294, 443129345526, 269103494910, 28322588794, 0, 0, 0] := by
  decide +kernel

theorem rows12577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12577 = true := by
  decide +kernel

theorem tot12577 : totK PD2M8K2 D2M8K2.t12577 = [0, 154721659294, 448450562432, 270604860213, 20564670296, 0, 0, 0] := by
  decide +kernel

theorem rows12578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12578 = true := by
  decide +kernel

theorem tot12578 : totK PD2M8K2 D2M8K2.t12578 = [0, 0, 204156955302, 483125481210, 180366354049, 9587713104, 0, 0] := by
  decide +kernel

theorem rows12579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12579 = true := by
  decide +kernel

theorem tot12579 : totK PD2M8K2 D2M8K2.t12579 = [0, 85190975889, 320127949695, 375770053594, 95619724506, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
