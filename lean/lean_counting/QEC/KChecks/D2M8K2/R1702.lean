import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6808 = true := by
  decide +kernel

theorem tot6808 : totK PD2M8K2 D2M8K2.t6808 = [0, 229024809022, 504146088067, 161495275047, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows6809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6809 = true := by
  decide +kernel

theorem tot6809 : totK PD2M8K2 D2M8K2.t6809 = [80968783094, 282304114184, 386977012561, 127290055855, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows6810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6810 = true := by
  decide +kernel

theorem tot6810 : totK PD2M8K2 D2M8K2.t6810 = [174267827696, 469332164027, 258184735283, 23089903725, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6811 = true := by
  decide +kernel

theorem tot6811 : totK PD2M8K2 D2M8K2.t6811 = [87802588610, 373319769267, 355652541908, 60305907411, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
