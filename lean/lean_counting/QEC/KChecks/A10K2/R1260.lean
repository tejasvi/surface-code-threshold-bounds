import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5040 = true := by
  decide +kernel

theorem tot5040 : totK PA10K2 A10K2.t5040 = [0, 0, 963665215132, 2397566667829, 1204006322817, 106683496047, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5041 = true := by
  decide +kernel

theorem tot5041 : totK PA10K2 A10K2.t5041 = [0, 472601942740, 1479325532796, 1780003452261, 976564683624, 193827742749, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5042 = true := by
  decide +kernel

theorem tot5042 : totK PA10K2 A10K2.t5042 = [0, 153187210152, 1096796780703, 2084288428615, 1355386602532, 237362162091, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5043 = true := by
  decide +kernel

theorem tot5043 : totK PA10K2 A10K2.t5043 = [0, 0, 582012264508, 1940367577094, 1889798516558, 568035430231, 34004712665, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
