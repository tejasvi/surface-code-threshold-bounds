import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16368 = true := by
  decide +kernel

theorem tot16368 : totK PD2M8K2 D2M8K2.t16368 = [0, 0, 0, 152631023430, 452566010030, 255081544518, 18742174887, 0] := by
  decide +kernel

theorem rows16369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16369 = true := by
  decide +kernel

theorem tot16369 : totK PD2M8K2 D2M8K2.t16369 = [0, 0, 0, 0, 278946421123, 466280640110, 84293637077, 1288491354] := by
  decide +kernel

theorem rows16370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16370 = true := by
  decide +kernel

theorem tot16370 : totK PD2M8K2 D2M8K2.t16370 = [0, 0, 0, 178149460656, 434462057364, 275719005545, 32344806501, 0] := by
  decide +kernel

theorem rows16371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16371 = true := by
  decide +kernel

theorem tot16371 : totK PD2M8K2 D2M8K2.t16371 = [0, 0, 0, 231002100607, 497940660614, 174618479641, 3566736190, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
