import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8388 = true := by
  decide +kernel

theorem tot8388 : totK PD2M8K2 D2M8K2.t8388 = [0, 0, 280154878313, 507101255376, 110227060996, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8389 = true := by
  decide +kernel

theorem tot8389 : totK PD2M8K2 D2M8K2.t8389 = [0, 139053454770, 434286110184, 300782619404, 27063010557, 0, 0, 0] := by
  decide +kernel

theorem rows8390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8390 = true := by
  decide +kernel

theorem tot8390 : totK PD2M8K2 D2M8K2.t8390 = [0, 177235025095, 448626777289, 233729687783, 15312382876, 0, 0, 0] := by
  decide +kernel

theorem rows8391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8391 = true := by
  decide +kernel

theorem tot8391 : totK PD2M8K2 D2M8K2.t8391 = [0, 81560516956, 338372315163, 384110176046, 77631043591, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
