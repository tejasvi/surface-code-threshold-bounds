import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2316 = true := by
  decide +kernel

theorem tot2316 : totK PD2M8K2 D2M8K2.t2316 = [0, 0, 236265619919, 504386010474, 151708055497, 3340444656, 0, 0] := by
  decide +kernel

theorem rows2317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2317 = true := by
  decide +kernel

theorem tot2317 : totK PD2M8K2 D2M8K2.t2317 = [0, 0, 178607999480, 468578154713, 217171594765, 11611688723, 0, 0] := by
  decide +kernel

theorem rows2318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2318 = true := by
  decide +kernel

theorem tot2318 : totK PD2M8K2 D2M8K2.t2318 = [0, 0, 180666612665, 439719753811, 273663620098, 33384129928, 0, 0] := by
  decide +kernel

theorem rows2319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2319 = true := by
  decide +kernel

theorem tot2319 : totK PD2M8K2 D2M8K2.t2319 = [0, 0, 193226475484, 486609327372, 229073183267, 8259948215, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
