import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3184 = true := by
  decide +kernel

theorem tot3184 : totK PD2M8K2 D2M8K2.t3184 = [0, 256974516159, 497585166801, 128032317038, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows3185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3185 = true := by
  decide +kernel

theorem tot3185 : totK PD2M8K2 D2M8K2.t3185 = [0, 180895693486, 471618675379, 221105097553, 11008703954, 0, 0, 0] := by
  decide +kernel

theorem rows3186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3186 = true := by
  decide +kernel

theorem tot3186 : totK PD2M8K2 D2M8K2.t3186 = [0, 205143843334, 467707350126, 192875411773, 12126792705, 0, 0, 0] := by
  decide +kernel

theorem rows3187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3187 = true := by
  decide +kernel

theorem tot3187 : totK PD2M8K2 D2M8K2.t3187 = [0, 186632534769, 464694903268, 210724112276, 12361325328, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
