import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3744 = true := by
  decide +kernel

theorem tot3744 : totK PD2M8K2 D2M8K2.t3744 = [0, 186809123310, 458505691320, 238368957661, 16540840749, 0, 0, 0] := by
  decide +kernel

theorem rows3745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3745 = true := by
  decide +kernel

theorem tot3745 : totK PD2M8K2 D2M8K2.t3745 = [0, 71432936211, 402827626262, 391908487967, 43785204607, 0, 0, 0] := by
  decide +kernel

theorem rows3746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3746 = true := by
  decide +kernel

theorem tot3746 : totK PD2M8K2 D2M8K2.t3746 = [0, 0, 217289714604, 498811074665, 162218748171, 5159868635, 0, 0] := by
  decide +kernel

theorem rows3747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3747 = true := by
  decide +kernel

theorem tot3747 : totK PD2M8K2 D2M8K2.t3747 = [0, 191757145846, 456048219143, 238600976972, 25807658426, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
