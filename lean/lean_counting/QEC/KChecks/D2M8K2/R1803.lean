import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7212 = true := by
  decide +kernel

theorem tot7212 : totK PD2M8K2 D2M8K2.t7212 = [0, 0, 188816770458, 475767853912, 219748221456, 12534051746, 0, 0] := by
  decide +kernel

theorem rows7213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7213 = true := by
  decide +kernel

theorem tot7213 : totK PD2M8K2 D2M8K2.t7213 = [0, 0, 0, 285667958123, 496192124369, 106806023179, 1369150432, 0] := by
  decide +kernel

theorem rows7214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7214 = true := by
  decide +kernel

theorem tot7214 : totK PD2M8K2 D2M8K2.t7214 = [0, 0, 87964691079, 380570761674, 394541861883, 46623143016, 0, 0] := by
  decide +kernel

theorem rows7215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7215 = true := by
  decide +kernel

theorem tot7215 : totK PD2M8K2 D2M8K2.t7215 = [0, 0, 158770714090, 455821767583, 264824086684, 17022412725, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
