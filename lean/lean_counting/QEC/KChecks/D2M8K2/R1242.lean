import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4968 = true := by
  decide +kernel

theorem tot4968 : totK PD2M8K2 D2M8K2.t4968 = [0, 0, 282255768007, 515094897383, 109735993124, 1163840124, 0, 0] := by
  decide +kernel

theorem rows4969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4969 = true := by
  decide +kernel

theorem tot4969 : totK PD2M8K2 D2M8K2.t4969 = [0, 38068349305, 220797214217, 424477352026, 179510842222, 11873025674, 0, 0] := by
  decide +kernel

theorem rows4970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4970 = true := by
  decide +kernel

theorem tot4970 : totK PD2M8K2 D2M8K2.t4970 = [0, 195258438674, 463249643047, 244324968099, 23379338899, 0, 0, 0] := by
  decide +kernel

theorem rows4971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4971 = true := by
  decide +kernel

theorem tot4971 : totK PD2M8K2 D2M8K2.t4971 = [0, 177719090463, 477652263799, 234224159037, 12491870267, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
