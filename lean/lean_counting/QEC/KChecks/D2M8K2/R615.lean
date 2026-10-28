import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2460 = true := by
  decide +kernel

theorem tot2460 : totK PD2M8K2 D2M8K2.t2460 = [0, 79192507633, 319584823144, 360450377644, 148810011027, 17176948997, 0, 0] := by
  decide +kernel

theorem rows2461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2461 = true := by
  decide +kernel

theorem tot2461 : totK PD2M8K2 D2M8K2.t2461 = [0, 0, 203307870490, 468415781669, 208184617003, 11867500000, 0, 0] := by
  decide +kernel

theorem rows2462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2462 = true := by
  decide +kernel

theorem tot2462 : totK PD2M8K2 D2M8K2.t2462 = [0, 55495128339, 224803985179, 413090591605, 183862499443, 7877424857, 0, 0] := by
  decide +kernel

theorem rows2463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2463 = true := by
  decide +kernel

theorem tot2463 : totK PD2M8K2 D2M8K2.t2463 = [0, 189102075087, 469824356113, 244172410315, 22981891866, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
