import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6476 = true := by
  decide +kernel

theorem tot6476 : totK PD2M8K2 D2M8K2.t6476 = [193164478355, 476564890658, 221765429738, 12346377983, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6477 = true := by
  decide +kernel

theorem tot6477 : totK PD2M8K2 D2M8K2.t6477 = [48649156504, 329464460731, 436245745747, 94065371476, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows6478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6478 = true := by
  decide +kernel

theorem tot6478 : totK PD2M8K2 D2M8K2.t6478 = [0, 204641601273, 473608474480, 182366295908, 11873025674, 0, 0, 0] := by
  decide +kernel

theorem rows6479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6479 = true := by
  decide +kernel

theorem tot6479 : totK PD2M8K2 D2M8K2.t6479 = [150444073011, 418234311763, 310255104165, 41311759846, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
