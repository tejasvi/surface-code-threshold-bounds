import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12864 = true := by
  decide +kernel

theorem tot12864 : totK PD2M8K2 D2M8K2.t12864 = [0, 87142410234, 351675354507, 379548652100, 81291889705, 1288020181, 0, 0] := by
  decide +kernel

theorem rows12865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12865 = true := by
  decide +kernel

theorem tot12865 : totK PD2M8K2 D2M8K2.t12865 = [0, 171145267459, 436847817598, 275660280266, 30419930744, 0, 0, 0] := by
  decide +kernel

theorem rows12866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12866 = true := by
  decide +kernel

theorem tot12866 : totK PD2M8K2 D2M8K2.t12866 = [0, 143158187961, 451385199372, 285173989115, 25375302040, 0, 0, 0] := by
  decide +kernel

theorem rows12867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12867 = true := by
  decide +kernel

theorem tot12867 : totK PD2M8K2 D2M8K2.t12867 = [0, 0, 214352268651, 482860887760, 184134356891, 8265692893, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
