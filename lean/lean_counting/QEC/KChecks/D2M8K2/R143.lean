import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t572 = true := by
  decide +kernel

theorem tot572 : totK PD2M8K2 D2M8K2.t572 = [0, 174151762942, 489283397250, 239588613273, 12854363436, 0, 0, 0] := by
  decide +kernel

theorem rows573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t573 = true := by
  decide +kernel

theorem tot573 : totK PD2M8K2 D2M8K2.t573 = [0, 89410951224, 335563718927, 360936029717, 118371470838, 12669302371, 0, 0] := by
  decide +kernel

theorem rows574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t574 = true := by
  decide +kernel

theorem tot574 : totK PD2M8K2 D2M8K2.t574 = [0, 0, 189349635167, 460893947525, 233237039346, 10746672504, 0, 0] := by
  decide +kernel

theorem rows575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t575 = true := by
  decide +kernel

theorem tot575 : totK PD2M8K2 D2M8K2.t575 = [0, 84416218163, 269422875763, 369510171098, 161513643926, 8077291076, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
