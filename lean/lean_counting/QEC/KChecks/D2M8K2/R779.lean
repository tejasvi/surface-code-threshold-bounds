import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3116 = true := by
  decide +kernel

theorem tot3116 : totK PD2M8K2 D2M8K2.t3116 = [0, 170439871730, 450317803856, 229337690382, 14021246527, 0, 0, 0] := by
  decide +kernel

theorem rows3117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3117 = true := by
  decide +kernel

theorem tot3117 : totK PD2M8K2 D2M8K2.t3117 = [0, 0, 282766687851, 464869931825, 108982390746, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3118 = true := by
  decide +kernel

theorem tot3118 : totK PD2M8K2 D2M8K2.t3118 = [0, 144590128346, 434946256522, 276663729267, 27324221443, 0, 0, 0] := by
  decide +kernel

theorem rows3119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3119 = true := by
  decide +kernel

theorem tot3119 : totK PD2M8K2 D2M8K2.t3119 = [0, 188301876826, 472816359920, 225715160848, 12679943201, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
