import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3048 = true := by
  decide +kernel

theorem tot3048 : totK PA10K2 A10K2.t3048 = [0, 0, 552655315378, 1845597119232, 1832503389098, 468653537019, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows3049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3049 = true := by
  decide +kernel

theorem tot3049 : totK PA10K2 A10K2.t3049 = [0, 0, 110963681569, 1297532343023, 2324123411013, 840860140134, 49929027571, 0, 0, 0] := by
  decide +kernel

theorem rows3050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3050 = true := by
  decide +kernel

theorem tot3050 : totK PA10K2 A10K2.t3050 = [0, 406049746911, 1268848603326, 1282848074158, 909683105705, 688897881880, 164668396310, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3051 = true := by
  decide +kernel

theorem tot3051 : totK PA10K2 A10K2.t3051 = [0, 150572114276, 1024790628011, 2086661029391, 1411799824968, 287121150749, 12462147902, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
