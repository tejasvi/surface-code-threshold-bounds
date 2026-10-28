import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2400 = true := by
  decide +kernel

theorem tot2400 : totK PD2M8K2 D2M8K2.t2400 = [0, 0, 273040617341, 512234411574, 109243167110, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2401 = true := by
  decide +kernel

theorem tot2401 : totK PD2M8K2 D2M8K2.t2401 = [0, 106371811407, 382348406264, 376848811229, 53150271748, 0, 0, 0] := by
  decide +kernel

theorem rows2402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2402 = true := by
  decide +kernel

theorem tot2402 : totK PD2M8K2 D2M8K2.t2402 = [0, 179608893499, 456744985861, 237706495206, 15877172327, 0, 0, 0] := by
  decide +kernel

theorem rows2403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2403 = true := by
  decide +kernel

theorem tot2403 : totK PD2M8K2 D2M8K2.t2403 = [0, 113563480266, 426373954477, 334284592036, 44851522470, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
