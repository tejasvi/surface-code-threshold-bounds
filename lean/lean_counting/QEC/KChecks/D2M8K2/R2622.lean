import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10488 = true := by
  decide +kernel

theorem tot10488 : totK PD2M8K2 D2M8K2.t10488 = [0, 0, 0, 235775479652, 475920401814, 191086232444, 12054718719, 0] := by
  decide +kernel

theorem rows10489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10489 = true := by
  decide +kernel

theorem tot10489 : totK PD2M8K2 D2M8K2.t10489 = [0, 0, 79678872252, 312791437650, 379865714834, 122969535698, 4239164426, 0] := by
  decide +kernel

theorem rows10490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10490 = true := by
  decide +kernel

theorem tot10490 : totK PD2M8K2 D2M8K2.t10490 = [0, 0, 241108874605, 485062849288, 194897795740, 18289493937, 0, 0] := by
  decide +kernel

theorem rows10491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10491 = true := by
  decide +kernel

theorem tot10491 : totK PD2M8K2 D2M8K2.t10491 = [0, 0, 171998358375, 478657227563, 234658143812, 14950598637, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
