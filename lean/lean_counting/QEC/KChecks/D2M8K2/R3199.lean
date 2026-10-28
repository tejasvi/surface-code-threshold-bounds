import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12796 = true := by
  decide +kernel

theorem tot12796 : totK PD2M8K2 D2M8K2.t12796 = [0, 0, 206492901346, 493772554116, 195229240221, 5430665091, 0, 0] := by
  decide +kernel

theorem rows12797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12797 = true := by
  decide +kernel

theorem tot12797 : totK PD2M8K2 D2M8K2.t12797 = [0, 155984292415, 368450041063, 264300663784, 102096616986, 6799735859, 0, 0] := by
  decide +kernel

theorem rows12798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12798 = true := by
  decide +kernel

theorem tot12798 : totK PD2M8K2 D2M8K2.t12798 = [0, 169991297642, 441560906435, 285762388680, 30437197709, 0, 0, 0] := by
  decide +kernel

theorem rows12799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12799 = true := by
  decide +kernel

theorem tot12799 : totK PD2M8K2 D2M8K2.t12799 = [0, 108912673344, 436565307616, 317364300009, 26960621353, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
