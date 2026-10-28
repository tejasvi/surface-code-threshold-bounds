import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5488 = true := by
  decide +kernel

theorem tot5488 : totK PD2M8K2 D2M8K2.t5488 = [0, 0, 56835226932, 334320804031, 420098598737, 95846458993, 1268739303, 0] := by
  decide +kernel

theorem rows5489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5489 = true := by
  decide +kernel

theorem tot5489 : totK PD2M8K2 D2M8K2.t5489 = [0, 0, 0, 216654392376, 483745680432, 174821174109, 7442000727, 0] := by
  decide +kernel

theorem rows5490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5490 = true := by
  decide +kernel

theorem tot5490 : totK PD2M8K2 D2M8K2.t5490 = [0, 0, 0, 181480131382, 476459992659, 213361156285, 14707859566, 0] := by
  decide +kernel

theorem rows5491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5491 = true := by
  decide +kernel

theorem tot5491 : totK PD2M8K2 D2M8K2.t5491 = [0, 0, 0, 229902239099, 477423925730, 143849621488, 2335868043, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
