import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5124 = true := by
  decide +kernel

theorem tot5124 : totK PD2M8K2 D2M8K2.t5124 = [0, 0, 133534160926, 344749839839, 291602171813, 128506586342, 8104085798, 0] := by
  decide +kernel

theorem rows5125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5125 = true := by
  decide +kernel

theorem tot5125 : totK PD2M8K2 D2M8K2.t5125 = [0, 0, 166713567426, 437270122180, 280958606744, 30484327524, 0, 0] := by
  decide +kernel

theorem rows5126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5126 = true := by
  decide +kernel

theorem tot5126 : totK PD2M8K2 D2M8K2.t5126 = [0, 0, 113361519492, 443719987059, 324266866819, 24218634357, 0, 0] := by
  decide +kernel

theorem rows5127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5127 = true := by
  decide +kernel

theorem tot5127 : totK PD2M8K2 D2M8K2.t5127 = [0, 0, 0, 245977199097, 495933648976, 148906062408, 6821150176, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
