import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12560 = true := by
  decide +kernel

theorem tot12560 : totK PD2M8K2 D2M8K2.t12560 = [0, 0, 89770953565, 408622630284, 327385810710, 39738903260, 1171084559, 0] := by
  decide +kernel

theorem rows12561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12561 = true := by
  decide +kernel

theorem tot12561 : totK PD2M8K2 D2M8K2.t12561 = [0, 0, 0, 235944878608, 466799394248, 156661879545, 8462178015, 0] := by
  decide +kernel

theorem rows12562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12562 = true := by
  decide +kernel

theorem tot12562 : totK PD2M8K2 D2M8K2.t12562 = [0, 0, 135115130653, 375151495447, 282930333308, 70345659285, 3472187823, 0] := by
  decide +kernel

theorem rows12563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12563 = true := by
  decide +kernel

theorem tot12563 : totK PD2M8K2 D2M8K2.t12563 = [0, 0, 184647972411, 467149108659, 225971112016, 14442463006, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
