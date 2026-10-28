import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1024 = true := by
  decide +kernel

theorem tot1024 : totK PD2M8K2 D2M8K2.t1024 = [0, 0, 301133334573, 474622857259, 78109469395, 1053411165, 0, 0] := by
  decide +kernel

theorem rows1025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1025 = true := by
  decide +kernel

theorem tot1025 : totK PD2M8K2 D2M8K2.t1025 = [0, 108040638948, 340587438183, 330501356711, 81900468729, 3667207281, 0, 0] := by
  decide +kernel

theorem rows1026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1026 = true := by
  decide +kernel

theorem tot1026 : totK PD2M8K2 D2M8K2.t1026 = [0, 185386317696, 449600920463, 252484169358, 26670933089, 0, 0, 0] := by
  decide +kernel

theorem rows1027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1027 = true := by
  decide +kernel

theorem tot1027 : totK PD2M8K2 D2M8K2.t1027 = [159850119204, 368412435085, 246705431199, 124882601388, 13552128683, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
