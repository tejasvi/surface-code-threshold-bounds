import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5824 = true := by
  decide +kernel

theorem tot5824 : totK PD2M8K2 D2M8K2.t5824 = [88183717169, 399446077733, 375959066591, 55126634818, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5825 = true := by
  decide +kernel

theorem tot5825 : totK PD2M8K2 D2M8K2.t5825 = [0, 161695690272, 447145263646, 271057689572, 25368447013, 0, 0, 0] := by
  decide +kernel

theorem rows5826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5826 = true := by
  decide +kernel

theorem tot5826 : totK PD2M8K2 D2M8K2.t5826 = [0, 174232524196, 473992834805, 232729135106, 8931382700, 0, 0, 0] := by
  decide +kernel

theorem rows5827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5827 = true := by
  decide +kernel

theorem tot5827 : totK PD2M8K2 D2M8K2.t5827 = [190501719738, 457159357960, 244322960555, 27061298859, 3297287104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
