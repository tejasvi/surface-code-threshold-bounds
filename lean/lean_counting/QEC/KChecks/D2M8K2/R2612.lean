import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10448 = true := by
  decide +kernel

theorem tot10448 : totK PD2M8K2 D2M8K2.t10448 = [0, 0, 0, 39511380414, 350625873522, 377538980287, 60172979559, 1032241984] := by
  decide +kernel

theorem rows10449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10449 = true := by
  decide +kernel

theorem tot10449 : totK PD2M8K2 D2M8K2.t10449 = [0, 0, 0, 79566085834, 301298870688, 360462144354, 91795793793, 3598673838] := by
  decide +kernel

theorem rows10450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10450 = true := by
  decide +kernel

theorem tot10450 : totK PD2M8K2 D2M8K2.t10450 = [0, 0, 0, 212097685379, 481545049177, 196559042766, 11367430297, 0] := by
  decide +kernel

theorem rows10451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10451 = true := by
  decide +kernel

theorem tot10451 : totK PD2M8K2 D2M8K2.t10451 = [0, 0, 72675911180, 229571367993, 388299292450, 204486989179, 13629764950, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
