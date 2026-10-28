import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5612 = true := by
  decide +kernel

theorem tot5612 : totK PD2M8K2 D2M8K2.t5612 = [156854759878, 455096074302, 274902973969, 19859170588, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5613 = true := by
  decide +kernel

theorem tot5613 : totK PD2M8K2 D2M8K2.t5613 = [0, 217659653547, 491657538642, 167226132529, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows5614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5614 = true := by
  decide +kernel

theorem tot5614 : totK PD2M8K2 D2M8K2.t5614 = [84296133020, 303298025070, 369744763077, 117718737294, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows5615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5615 = true := by
  decide +kernel

theorem tot5615 : totK PD2M8K2 D2M8K2.t5615 = [155457879018, 448877130139, 272515990708, 25916662030, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
