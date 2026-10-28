import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5332 = true := by
  decide +kernel

theorem tot5332 : totK PD2M8K2 D2M8K2.t5332 = [0, 0, 195674237824, 454265911075, 257082083862, 25969295659, 0, 0] := by
  decide +kernel

theorem rows5333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5333 = true := by
  decide +kernel

theorem tot5333 : totK PD2M8K2 D2M8K2.t5333 = [0, 0, 167941586550, 489607055399, 242422545308, 12003991551, 0, 0] := by
  decide +kernel

theorem rows5334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5334 = true := by
  decide +kernel

theorem tot5334 : totK PD2M8K2 D2M8K2.t5334 = [0, 0, 172882538255, 452932842042, 246995504324, 23954454910, 0, 0] := by
  decide +kernel

theorem rows5335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5335 = true := by
  decide +kernel

theorem tot5335 : totK PD2M8K2 D2M8K2.t5335 = [0, 0, 175185964103, 462393277454, 245899881831, 16023006245, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
