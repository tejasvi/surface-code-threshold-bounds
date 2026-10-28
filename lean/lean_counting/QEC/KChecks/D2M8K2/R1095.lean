import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4380 = true := by
  decide +kernel

theorem tot4380 : totK PD2M8K2 D2M8K2.t4380 = [0, 0, 295751342312, 497796826492, 107702005337, 1268739303, 0, 0] := by
  decide +kernel

theorem rows4381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4381 = true := by
  decide +kernel

theorem tot4381 : totK PD2M8K2 D2M8K2.t4381 = [0, 0, 211261882139, 491218830575, 180978771966, 7428547934, 0, 0] := by
  decide +kernel

theorem rows4382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4382 = true := by
  decide +kernel

theorem tot4382 : totK PD2M8K2 D2M8K2.t4382 = [0, 0, 192801504120, 466717283089, 213365088545, 14863079690, 0, 0] := by
  decide +kernel

theorem rows4383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4383 = true := by
  decide +kernel

theorem tot4383 : totK PD2M8K2 D2M8K2.t4383 = [0, 0, 207894737842, 488446418364, 166638880568, 5000353977, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
