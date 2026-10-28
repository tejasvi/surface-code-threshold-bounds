import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15220 = true := by
  decide +kernel

theorem tot15220 : totK PD2M8K2 D2M8K2.t15220 = [0, 0, 115791746952, 411076227165, 308458078285, 47848931317, 2754314106, 0] := by
  decide +kernel

theorem rows15221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15221 = true := by
  decide +kernel

theorem tot15221 : totK PD2M8K2 D2M8K2.t15221 = [0, 0, 183133735991, 450951360176, 260794384858, 21215360344, 0, 0] := by
  decide +kernel

theorem rows15222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15222 = true := by
  decide +kernel

theorem tot15222 : totK PD2M8K2 D2M8K2.t15222 = [0, 0, 112464439539, 422019068800, 319369214825, 28869012147, 0, 0] := by
  decide +kernel

theorem rows15223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15223 = true := by
  decide +kernel

theorem tot15223 : totK PD2M8K2 D2M8K2.t15223 = [0, 0, 0, 263554581372, 462896634197, 127719475491, 4931404646, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
