import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9016 = true := by
  decide +kernel

theorem tot9016 : totK PD2M8K2 D2M8K2.t9016 = [0, 173729721164, 461921194748, 247612768456, 14293244700, 0, 0, 0] := by
  decide +kernel

theorem rows9017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9017 = true := by
  decide +kernel

theorem tot9017 : totK PD2M8K2 D2M8K2.t9017 = [0, 0, 275359601820, 505084921541, 112914437675, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9018 = true := by
  decide +kernel

theorem tot9018 : totK PD2M8K2 D2M8K2.t9018 = [0, 123344006346, 421518086827, 328557277279, 32229476596, 0, 0, 0] := by
  decide +kernel

theorem rows9019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9019 = true := by
  decide +kernel

theorem tot9019 : totK PD2M8K2 D2M8K2.t9019 = [0, 197775571000, 458533559503, 201882300773, 12310507219, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
