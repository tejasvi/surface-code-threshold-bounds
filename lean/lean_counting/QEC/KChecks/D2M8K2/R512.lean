import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2048 = true := by
  decide +kernel

theorem tot2048 : totK PD2M8K2 D2M8K2.t2048 = [0, 87654302015, 354639888701, 360523679724, 77262053951, 1164319620, 0, 0] := by
  decide +kernel

theorem rows2049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2049 = true := by
  decide +kernel

theorem tot2049 : totK PD2M8K2 D2M8K2.t2049 = [0, 0, 222643802613, 480679648066, 162961336104, 9404247146, 0, 0] := by
  decide +kernel

theorem rows2050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2050 = true := by
  decide +kernel

theorem tot2050 : totK PD2M8K2 D2M8K2.t2050 = [0, 171098521580, 435142369201, 241219918298, 42251293269, 2481160468, 0, 0] := by
  decide +kernel

theorem rows2051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2051 = true := by
  decide +kernel

theorem tot2051 : totK PD2M8K2 D2M8K2.t2051 = [0, 187211683970, 462681564686, 241558449194, 16326303737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
