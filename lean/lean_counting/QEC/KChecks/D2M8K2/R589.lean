import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2356 = true := by
  decide +kernel

theorem tot2356 : totK PD2M8K2 D2M8K2.t2356 = [0, 0, 192485206056, 472140491460, 220732502724, 12835581599, 0, 0] := by
  decide +kernel

theorem rows2357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2357 = true := by
  decide +kernel

theorem tot2357 : totK PD2M8K2 D2M8K2.t2357 = [0, 0, 178724340094, 454578800889, 254341867695, 21455415392, 0, 0] := by
  decide +kernel

theorem rows2358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2358 = true := by
  decide +kernel

theorem tot2358 : totK PD2M8K2 D2M8K2.t2358 = [0, 0, 149747826631, 454902776259, 268599600831, 18850607798, 0, 0] := by
  decide +kernel

theorem rows2359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2359 = true := by
  decide +kernel

theorem tot2359 : totK PD2M8K2 D2M8K2.t2359 = [0, 0, 0, 236621615118, 475363584875, 147596685306, 5395128787, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
