import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7736 = true := by
  decide +kernel

theorem tot7736 : totK PD2M8K2 D2M8K2.t7736 = [0, 0, 165708488945, 438224285862, 278815277785, 27353690030, 0, 0] := by
  decide +kernel

theorem rows7737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7737 = true := by
  decide +kernel

theorem tot7737 : totK PD2M8K2 D2M8K2.t7737 = [0, 0, 182742455273, 505466350576, 226072345213, 7721315565, 0, 0] := by
  decide +kernel

theorem rows7738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7738 = true := by
  decide +kernel

theorem tot7738 : totK PD2M8K2 D2M8K2.t7738 = [0, 0, 0, 202519387313, 472669331407, 208482613072, 13604428459, 0] := by
  decide +kernel

theorem rows7739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7739 = true := by
  decide +kernel

theorem tot7739 : totK PD2M8K2 D2M8K2.t7739 = [0, 0, 84126500797, 336893032858, 390381013020, 95084501066, 1409560813, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
