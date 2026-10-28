import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5508 = true := by
  decide +kernel

theorem tot5508 : totK PD2M8K2 D2M8K2.t5508 = [0, 309133710608, 523319313287, 80167633007, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5509 = true := by
  decide +kernel

theorem tot5509 : totK PD2M8K2 D2M8K2.t5509 = [170667201217, 444427197447, 274706031895, 28697506532, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5510 = true := by
  decide +kernel

theorem tot5510 : totK PD2M8K2 D2M8K2.t5510 = [188743155994, 475830906025, 219917378176, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5511 = true := by
  decide +kernel

theorem tot5511 : totK PD2M8K2 D2M8K2.t5511 = [58771690895, 329733986286, 423980109517, 87168333906, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
