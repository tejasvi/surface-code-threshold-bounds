import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4596 = true := by
  decide +kernel

theorem tot4596 : totK PD2M8K2 D2M8K2.t4596 = [0, 0, 0, 194630814978, 471726558491, 212104801383, 12183533023, 0] := by
  decide +kernel

theorem rows4597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4597 = true := by
  decide +kernel

theorem tot4597 : totK PD2M8K2 D2M8K2.t4597 = [0, 0, 0, 4187750769, 365294851363, 460800361279, 58745732395, 0] := by
  decide +kernel

theorem rows4598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4598 = true := by
  decide +kernel

theorem tot4598 : totK PD2M8K2 D2M8K2.t4598 = [0, 0, 0, 60015990919, 250043006170, 393930391127, 141305349544, 5717851365] := by
  decide +kernel

theorem rows4599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4599 = true := by
  decide +kernel

theorem tot4599 : totK PD2M8K2 D2M8K2.t4599 = [0, 0, 0, 190099575007, 484772200648, 198507312515, 10905421912, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
