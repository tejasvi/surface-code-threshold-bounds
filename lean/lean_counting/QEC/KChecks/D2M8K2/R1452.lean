import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5808 = true := by
  decide +kernel

theorem tot5808 : totK PD2M8K2 D2M8K2.t5808 = [0, 161523503757, 449176973633, 281877326673, 30339117390, 0, 0, 0] := by
  decide +kernel

theorem rows5809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5809 = true := by
  decide +kernel

theorem tot5809 : totK PD2M8K2 D2M8K2.t5809 = [0, 170325749094, 457783946349, 241959363781, 15214870593, 0, 0, 0] := by
  decide +kernel

theorem rows5810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5810 = true := by
  decide +kernel

theorem tot5810 : totK PD2M8K2 D2M8K2.t5810 = [0, 0, 267500803432, 484528739959, 130968528802, 4031931762, 0, 0] := by
  decide +kernel

theorem rows5811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5811 = true := by
  decide +kernel

theorem tot5811 : totK PD2M8K2 D2M8K2.t5811 = [0, 131009799203, 357596327939, 313143824864, 71670903423, 1186940923, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
