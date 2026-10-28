import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8868 = true := by
  decide +kernel

theorem tot8868 : totK PD2M8K2 D2M8K2.t8868 = [195143075606, 486020042636, 224142211898, 12148140469, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8869 = true := by
  decide +kernel

theorem tot8869 : totK PD2M8K2 D2M8K2.t8869 = [0, 251174998224, 451502760117, 193765996363, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows8870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8870 = true := by
  decide +kernel

theorem tot8870 : totK PD2M8K2 D2M8K2.t8870 = [0, 194084820281, 485081463203, 210114337869, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows8871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8871 = true := by
  decide +kernel

theorem tot8871 : totK PD2M8K2 D2M8K2.t8871 = [89930224278, 270507039451, 370826890077, 179122980107, 8214505460, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
