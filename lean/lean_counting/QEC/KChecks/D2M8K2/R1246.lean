import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4984 = true := by
  decide +kernel

theorem tot4984 : totK PD2M8K2 D2M8K2.t4984 = [0, 0, 0, 174488586886, 452709262006, 248979091073, 25191558099, 0] := by
  decide +kernel

theorem rows4985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4985 = true := by
  decide +kernel

theorem tot4985 : totK PD2M8K2 D2M8K2.t4985 = [0, 0, 0, 209833033481, 494690173524, 179902306445, 5206224793, 0] := by
  decide +kernel

theorem rows4986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4986 = true := by
  decide +kernel

theorem tot4986 : totK PD2M8K2 D2M8K2.t4986 = [0, 0, 155134466269, 374428453447, 262271423757, 102616944585, 6524090962, 0] := by
  decide +kernel

theorem rows4987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4987 = true := by
  decide +kernel

theorem tot4987 : totK PD2M8K2 D2M8K2.t4987 = [0, 0, 177395887876, 452075244324, 251051693991, 18072729198, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
