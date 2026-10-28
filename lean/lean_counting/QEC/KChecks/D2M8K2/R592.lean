import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2368 = true := by
  decide +kernel

theorem tot2368 : totK PD2M8K2 D2M8K2.t2368 = [0, 172237202119, 427712394766, 288628227974, 36397905299, 0, 0, 0] := by
  decide +kernel

theorem rows2369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2369 = true := by
  decide +kernel

theorem tot2369 : totK PD2M8K2 D2M8K2.t2369 = [0, 207957952371, 483038669399, 209009801990, 11310261785, 0, 0, 0] := by
  decide +kernel

theorem rows2370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2370 = true := by
  decide +kernel

theorem tot2370 : totK PD2M8K2 D2M8K2.t2370 = [0, 0, 254071024139, 433661085669, 192607182533, 19898621015, 0, 0] := by
  decide +kernel

theorem rows2371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2371 = true := by
  decide +kernel

theorem tot2371 : totK PD2M8K2 D2M8K2.t2371 = [0, 0, 187144980849, 488462176879, 224308747690, 6957791766, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
