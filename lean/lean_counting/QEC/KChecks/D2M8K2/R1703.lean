import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6812 = true := by
  decide +kernel

theorem tot6812 : totK PD2M8K2 D2M8K2.t6812 = [3757402556, 261216019890, 507158028992, 137911943381, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows6813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6813 = true := by
  decide +kernel

theorem tot6813 : totK PD2M8K2 D2M8K2.t6813 = [183807753329, 459182069918, 245421264127, 23050312993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6814 = true := by
  decide +kernel

theorem tot6814 : totK PD2M8K2 D2M8K2.t6814 = [199200422743, 481301709728, 224148201156, 13838124055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6815 = true := by
  decide +kernel

theorem tot6815 : totK PD2M8K2 D2M8K2.t6815 = [37514313847, 311987363014, 442261156184, 100861237546, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
