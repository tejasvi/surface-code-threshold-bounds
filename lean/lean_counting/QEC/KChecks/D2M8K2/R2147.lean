import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8588 = true := by
  decide +kernel

theorem tot8588 : totK PD2M8K2 D2M8K2.t8588 = [0, 88232718943, 343514003859, 371009545246, 80827615511, 1171084559, 0, 0] := by
  decide +kernel

theorem rows8589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8589 = true := by
  decide +kernel

theorem tot8589 : totK PD2M8K2 D2M8K2.t8589 = [0, 0, 225272784276, 470176896183, 160672412504, 9444064503, 0, 0] := by
  decide +kernel

theorem rows8590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8590 = true := by
  decide +kernel

theorem tot8590 : totK PD2M8K2 D2M8K2.t8590 = [0, 165404781481, 433972932397, 249686228424, 46160186902, 2490301335, 0, 0] := by
  decide +kernel

theorem rows8591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8591 = true := by
  decide +kernel

theorem tot8591 : totK PD2M8K2 D2M8K2.t8591 = [0, 154607598465, 454591829228, 267266143194, 19320941496, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
