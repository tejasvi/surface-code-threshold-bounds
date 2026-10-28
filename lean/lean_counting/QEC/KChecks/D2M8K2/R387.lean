import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1548 = true := by
  decide +kernel

theorem tot1548 : totK PD2M8K2 D2M8K2.t1548 = [0, 162784770147, 429199084307, 256610997954, 45949829913, 2481160468, 0, 0] := by
  decide +kernel

theorem rows1549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1549 = true := by
  decide +kernel

theorem tot1549 : totK PD2M8K2 D2M8K2.t1549 = [0, 155564105264, 428768550620, 274923902600, 29521857540, 0, 0, 0] := by
  decide +kernel

theorem rows1550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1550 = true := by
  decide +kernel

theorem tot1550 : totK PD2M8K2 D2M8K2.t1550 = [0, 90852006335, 357983275412, 360612138176, 67007126021, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1551 = true := by
  decide +kernel

theorem tot1551 : totK PD2M8K2 D2M8K2.t1551 = [0, 0, 312608419432, 506151151453, 80999617585, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
