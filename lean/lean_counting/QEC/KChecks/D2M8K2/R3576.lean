import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14304 = true := by
  decide +kernel

theorem tot14304 : totK PD2M8K2 D2M8K2.t14304 = [0, 86124322534, 371360867531, 396817886632, 51540991583, 0, 0, 0] := by
  decide +kernel

theorem rows14305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14305 = true := by
  decide +kernel

theorem tot14305 : totK PD2M8K2 D2M8K2.t14305 = [0, 156574175771, 445211432456, 270002764768, 19744550143, 0, 0, 0] := by
  decide +kernel

theorem rows14306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14306 = true := by
  decide +kernel

theorem tot14306 : totK PD2M8K2 D2M8K2.t14306 = [0, 135002877226, 437546586048, 274331579985, 23490344790, 0, 0, 0] := by
  decide +kernel

theorem rows14307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14307 = true := by
  decide +kernel

theorem tot14307 : totK PD2M8K2 D2M8K2.t14307 = [0, 0, 277861449333, 510911480920, 94682729289, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
