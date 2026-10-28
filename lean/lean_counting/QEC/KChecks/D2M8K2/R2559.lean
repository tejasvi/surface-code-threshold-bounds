import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10236 = true := by
  decide +kernel

theorem tot10236 : totK PD2M8K2 D2M8K2.t10236 = [0, 167527440431, 453269635162, 269241691443, 26854164282, 0, 0, 0] := by
  decide +kernel

theorem rows10237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10237 = true := by
  decide +kernel

theorem tot10237 : totK PD2M8K2 D2M8K2.t10237 = [0, 177753752293, 479073774509, 232792662293, 12123267984, 0, 0, 0] := by
  decide +kernel

theorem rows10238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10238 = true := by
  decide +kernel

theorem tot10238 : totK PD2M8K2 D2M8K2.t10238 = [0, 0, 289457699386, 511749860915, 97046526257, 1096156699, 0, 0] := by
  decide +kernel

theorem rows10239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10239 = true := by
  decide +kernel

theorem tot10239 : totK PD2M8K2 D2M8K2.t10239 = [0, 98420485883, 334104705058, 363610149048, 99793039490, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
