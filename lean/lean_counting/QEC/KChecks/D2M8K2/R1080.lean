import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4320 = true := by
  decide +kernel

theorem tot4320 : totK PD2M8K2 D2M8K2.t4320 = [0, 0, 0, 293453470389, 535079939316, 91412119656, 0, 0] := by
  decide +kernel

theorem rows4321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4321 = true := by
  decide +kernel

theorem tot4321 : totK PD2M8K2 D2M8K2.t4321 = [0, 0, 0, 237976438925, 499775540178, 137542029247, 2586295899, 0] := by
  decide +kernel

theorem rows4322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4322 = true := by
  decide +kernel

theorem tot4322 : totK PD2M8K2 D2M8K2.t4322 = [0, 0, 0, 227200846062, 526245228153, 136926907920, 0, 0] := by
  decide +kernel

theorem rows4323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4323 = true := by
  decide +kernel

theorem tot4323 : totK PD2M8K2 D2M8K2.t4323 = [0, 0, 0, 173106462393, 439365132463, 264689917435, 28418235757, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
