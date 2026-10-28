import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8192 = true := by
  decide +kernel

theorem tot8192 : totK PD2M8K2 D2M8K2.t8192 = [0, 216342410831, 478375168687, 197348995627, 9551710210, 0, 0, 0] := by
  decide +kernel

theorem rows8193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8193 = true := by
  decide +kernel

theorem tot8193 : totK PD2M8K2 D2M8K2.t8193 = [0, 11859818758, 305713476275, 471543977366, 98028176029, 1198073392, 0, 0] := by
  decide +kernel

theorem rows8194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8194 = true := by
  decide +kernel

theorem tot8194 : totK PD2M8K2 D2M8K2.t8194 = [0, 0, 212837927674, 484463956959, 174786726772, 7715358911, 0, 0] := by
  decide +kernel

theorem rows8195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8195 = true := by
  decide +kernel

theorem tot8195 : totK PD2M8K2 D2M8K2.t8195 = [0, 190727951577, 462185409997, 248289972240, 23058897148, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
