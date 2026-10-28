import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3672 = true := by
  decide +kernel

theorem tot3672 : totK PD2M8K2 D2M8K2.t3672 = [0, 0, 283221406800, 495963026194, 98941717479, 1162740214, 0, 0] := by
  decide +kernel

theorem rows3673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3673 = true := by
  decide +kernel

theorem tot3673 : totK PD2M8K2 D2M8K2.t3673 = [0, 18530029189, 202643092344, 461180847504, 176160822166, 11947333746, 0, 0] := by
  decide +kernel

theorem rows3674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3674 = true := by
  decide +kernel

theorem tot3674 : totK PD2M8K2 D2M8K2.t3674 = [0, 182082252244, 466722372759, 246219816635, 22592168133, 0, 0, 0] := by
  decide +kernel

theorem rows3675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3675 = true := by
  decide +kernel

theorem tot3675 : totK PD2M8K2 D2M8K2.t3675 = [0, 183619436447, 467071737411, 240377136087, 17104814242, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
