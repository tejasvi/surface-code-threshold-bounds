import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2892 = true := by
  decide +kernel

theorem tot2892 : totK PD2M8K2 D2M8K2.t2892 = [0, 189280850374, 460417548012, 242270997080, 18252358503, 0, 0, 0] := by
  decide +kernel

theorem rows2893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2893 = true := by
  decide +kernel

theorem tot2893 : totK PD2M8K2 D2M8K2.t2893 = [0, 123330964861, 440517340005, 278874871622, 18620566365, 0, 0, 0] := by
  decide +kernel

theorem rows2894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2894 = true := by
  decide +kernel

theorem tot2894 : totK PD2M8K2 D2M8K2.t2894 = [0, 0, 308780007876, 464335946213, 79226056930, 1021600638, 0, 0] := by
  decide +kernel

theorem rows2895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2895 = true := by
  decide +kernel

theorem tot2895 : totK PD2M8K2 D2M8K2.t2895 = [0, 170979490969, 388552671051, 240862303743, 69449327136, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
