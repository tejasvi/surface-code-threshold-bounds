import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1528 = true := by
  decide +kernel

theorem tot1528 : totK PD2M8K2 D2M8K2.t1528 = [0, 0, 178063496421, 491121523760, 217504168898, 6614204793, 0, 0] := by
  decide +kernel

theorem rows1529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1529 = true := by
  decide +kernel

theorem tot1529 : totK PD2M8K2 D2M8K2.t1529 = [0, 0, 172166272003, 454306906472, 229744438367, 14936878817, 0, 0] := by
  decide +kernel

theorem rows1530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1530 = true := by
  decide +kernel

theorem tot1530 : totK PD2M8K2 D2M8K2.t1530 = [0, 0, 206777413744, 474979837616, 203998250329, 10480478597, 0, 0] := by
  decide +kernel

theorem rows1531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1531 = true := by
  decide +kernel

theorem tot1531 : totK PD2M8K2 D2M8K2.t1531 = [0, 0, 186450219946, 467810616563, 213032037663, 12319708528, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
