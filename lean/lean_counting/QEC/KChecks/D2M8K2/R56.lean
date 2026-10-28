import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t224 = true := by
  decide +kernel

theorem tot224 : totK PD2M8K2 D2M8K2.t224 = [0, 0, 271215364516, 511101425702, 116625343393, 1232398321, 0, 0] := by
  decide +kernel

theorem rows225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t225 = true := by
  decide +kernel

theorem tot225 : totK PD2M8K2 D2M8K2.t225 = [0, 46925177816, 217982047497, 422438225911, 184081523820, 12451903996, 0, 0] := by
  decide +kernel

theorem rows226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t226 = true := by
  decide +kernel

theorem tot226 : totK PD2M8K2 D2M8K2.t226 = [0, 202911178838, 484194074127, 195771064901, 9727964516, 0, 0, 0] := by
  decide +kernel

theorem rows227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t227 = true := by
  decide +kernel

theorem tot227 : totK PD2M8K2 D2M8K2.t227 = [0, 170559465631, 461053003239, 245724798216, 13795945806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
