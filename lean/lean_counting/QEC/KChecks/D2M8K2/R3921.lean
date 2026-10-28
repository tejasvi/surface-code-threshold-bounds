import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15684 = true := by
  decide +kernel

theorem tot15684 : totK PD2M8K2 D2M8K2.t15684 = [0, 0, 42222873657, 300054420548, 468070158634, 82731272098, 1198073392, 0] := by
  decide +kernel

theorem rows15685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15685 = true := by
  decide +kernel

theorem tot15685 : totK PD2M8K2 D2M8K2.t15685 = [0, 0, 181743943276, 468958350501, 225726445190, 9920246228, 0, 0] := by
  decide +kernel

theorem rows15686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15686 = true := by
  decide +kernel

theorem tot15686 : totK PD2M8K2 D2M8K2.t15686 = [0, 0, 151655187399, 452087407404, 248775656248, 14990901482, 0, 0] := by
  decide +kernel

theorem rows15687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15687 = true := by
  decide +kernel

theorem tot15687 : totK PD2M8K2 D2M8K2.t15687 = [0, 0, 0, 299367675995, 498059973834, 73049004412, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
