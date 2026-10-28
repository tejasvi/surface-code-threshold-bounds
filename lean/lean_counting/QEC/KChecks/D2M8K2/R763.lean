import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3052 = true := by
  decide +kernel

theorem tot3052 : totK PD2M8K2 D2M8K2.t3052 = [0, 160799030670, 441365569585, 283255750092, 30465585733, 0, 0, 0] := by
  decide +kernel

theorem rows3053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3053 = true := by
  decide +kernel

theorem tot3053 : totK PD2M8K2 D2M8K2.t3053 = [0, 169358516215, 490091060012, 247830509406, 12790453980, 0, 0, 0] := by
  decide +kernel

theorem rows3054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3054 = true := by
  decide +kernel

theorem tot3054 : totK PD2M8K2 D2M8K2.t3054 = [0, 0, 202071600439, 479291246604, 217163417232, 12492052887, 0, 0] := by
  decide +kernel

theorem rows3055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3055 = true := by
  decide +kernel

theorem tot3055 : totK PD2M8K2 D2M8K2.t3055 = [0, 33121773576, 272860404453, 479244158658, 136952588127, 1409560813, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
