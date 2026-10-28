import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1060 = true := by
  decide +kernel

theorem tot1060 : totK PD2M8K2 D2M8K2.t1060 = [0, 75082883077, 363715358864, 365342509221, 69099362224, 1095107716, 0, 0] := by
  decide +kernel

theorem rows1061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1061 = true := by
  decide +kernel

theorem tot1061 : totK PD2M8K2 D2M8K2.t1061 = [0, 0, 290085943608, 482246401636, 104227570967, 1067409660, 0, 0] := by
  decide +kernel

theorem rows1062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1062 = true := by
  decide +kernel

theorem tot1062 : totK PD2M8K2 D2M8K2.t1062 = [0, 196677417037, 474302592331, 201140813459, 24992916924, 2814597007, 0, 0] := by
  decide +kernel

theorem rows1063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1063 = true := by
  decide +kernel

theorem tot1063 : totK PD2M8K2 D2M8K2.t1063 = [0, 195946614461, 470214598086, 218831984635, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
