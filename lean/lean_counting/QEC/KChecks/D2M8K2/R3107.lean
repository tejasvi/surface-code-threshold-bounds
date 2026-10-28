import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12428 = true := by
  decide +kernel

theorem tot12428 : totK PD2M8K2 D2M8K2.t12428 = [0, 19168591844, 329761697046, 456292358954, 81483371908, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12429 = true := by
  decide +kernel

theorem tot12429 : totK PD2M8K2 D2M8K2.t12429 = [0, 49325832761, 285842164411, 441192836666, 120845967074, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12430 = true := by
  decide +kernel

theorem tot12430 : totK PD2M8K2 D2M8K2.t12430 = [0, 188693034156, 459386672040, 241975520077, 21099041006, 0, 0, 0] := by
  decide +kernel

theorem rows12431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12431 = true := by
  decide +kernel

theorem tot12431 : totK PD2M8K2 D2M8K2.t12431 = [0, 87565796449, 381310149205, 360401136025, 55185589388, 1210106048, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
