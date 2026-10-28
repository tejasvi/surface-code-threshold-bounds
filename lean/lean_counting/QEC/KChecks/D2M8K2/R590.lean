import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2360 = true := by
  decide +kernel

theorem tot2360 : totK PD2M8K2 D2M8K2.t2360 = [0, 0, 150804793376, 451008045004, 269618106871, 23945983865, 0, 0] := by
  decide +kernel

theorem rows2361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2361 = true := by
  decide +kernel

theorem tot2361 : totK PD2M8K2 D2M8K2.t2361 = [0, 0, 174159352931, 461288762430, 237386025215, 13826250344, 0, 0] := by
  decide +kernel

theorem rows2362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2362 = true := by
  decide +kernel

theorem tot2362 : totK PD2M8K2 D2M8K2.t2362 = [0, 0, 171600511582, 461780382882, 239877734311, 14204525510, 0, 0] := by
  decide +kernel

theorem rows2363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2363 = true := by
  decide +kernel

theorem tot2363 : totK PD2M8K2 D2M8K2.t2363 = [0, 0, 197293157492, 473372716840, 226305062496, 14023439837, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
