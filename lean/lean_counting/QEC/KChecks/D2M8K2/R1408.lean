import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5632 = true := by
  decide +kernel

theorem tot5632 : totK PD2M8K2 D2M8K2.t5632 = [0, 169027001268, 455772393478, 249239726545, 18484640963, 0, 0, 0] := by
  decide +kernel

theorem rows5633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5633 = true := by
  decide +kernel

theorem tot5633 : totK PD2M8K2 D2M8K2.t5633 = [0, 182578213579, 444862503828, 226815152785, 16702988424, 0, 0, 0] := by
  decide +kernel

theorem rows5634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5634 = true := by
  decide +kernel

theorem tot5634 : totK PD2M8K2 D2M8K2.t5634 = [0, 81287500427, 363966551586, 354355245267, 69099362224, 1095107716, 0, 0] := by
  decide +kernel

theorem rows5635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5635 = true := by
  decide +kernel

theorem tot5635 : totK PD2M8K2 D2M8K2.t5635 = [0, 0, 284403259776, 482317318893, 103865969135, 1067409660, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
