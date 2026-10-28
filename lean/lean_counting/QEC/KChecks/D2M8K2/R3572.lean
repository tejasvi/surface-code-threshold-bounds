import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14288 = true := by
  decide +kernel

theorem tot14288 : totK PD2M8K2 D2M8K2.t14288 = [0, 0, 290172637937, 501416433476, 95860143739, 1107157161, 0, 0] := by
  decide +kernel

theorem rows14289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14289 = true := by
  decide +kernel

theorem tot14289 : totK PD2M8K2 D2M8K2.t14289 = [0, 134872346053, 369788882383, 298470676434, 81854573971, 3824247485, 0, 0] := by
  decide +kernel

theorem rows14290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14290 = true := by
  decide +kernel

theorem tot14290 : totK PD2M8K2 D2M8K2.t14290 = [0, 171915967495, 445901247488, 271274719147, 24998040052, 0, 0, 0] := by
  decide +kernel

theorem rows14291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14291 = true := by
  decide +kernel

theorem tot14291 : totK PD2M8K2 D2M8K2.t14291 = [0, 134665685961, 448275449094, 305893375818, 24082590401, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
