import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8948 = true := by
  decide +kernel

theorem tot8948 : totK PD2M8K2 D2M8K2.t8948 = [166105465443, 441384578772, 268420905563, 22588851319, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8949 = true := by
  decide +kernel

theorem tot8949 : totK PD2M8K2 D2M8K2.t8949 = [158470454872, 456831971782, 277763042023, 29458744216, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8950 = true := by
  decide +kernel

theorem tot8950 : totK PD2M8K2 D2M8K2.t8950 = [0, 181337811209, 435824218940, 253553452633, 25358898171, 0, 0, 0] := by
  decide +kernel

theorem rows8951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8951 = true := by
  decide +kernel

theorem tot8951 : totK PD2M8K2 D2M8K2.t8951 = [0, 193232608873, 507945948819, 202273345996, 5430665091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
