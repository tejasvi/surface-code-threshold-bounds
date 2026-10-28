import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10404 = true := by
  decide +kernel

theorem tot10404 : totK PD2M8K2 D2M8K2.t10404 = [0, 0, 223866926299, 517842643381, 176277022135, 7379952709, 0, 0] := by
  decide +kernel

theorem rows10405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10405 = true := by
  decide +kernel

theorem tot10405 : totK PD2M8K2 D2M8K2.t10405 = [0, 0, 187978998616, 466057250971, 248707786402, 22965954259, 0, 0] := by
  decide +kernel

theorem rows10406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10406 = true := by
  decide +kernel

theorem tot10406 : totK PD2M8K2 D2M8K2.t10406 = [0, 0, 189788061565, 469543800540, 220855473381, 12426737048, 0, 0] := by
  decide +kernel

theorem rows10407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10407 = true := by
  decide +kernel

theorem tot10407 : totK PD2M8K2 D2M8K2.t10407 = [0, 0, 19374756099, 353249288225, 476586216730, 68342121404, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
