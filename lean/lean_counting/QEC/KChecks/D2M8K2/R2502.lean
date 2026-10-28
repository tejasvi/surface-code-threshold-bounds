import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10008 = true := by
  decide +kernel

theorem tot10008 : totK PD2M8K2 D2M8K2.t10008 = [0, 0, 182286884995, 470995996934, 254688857892, 20321671879, 0, 0] := by
  decide +kernel

theorem rows10009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10009 = true := by
  decide +kernel

theorem tot10009 : totK PD2M8K2 D2M8K2.t10009 = [0, 0, 203877402768, 477253636821, 219782337912, 13497756175, 0, 0] := by
  decide +kernel

theorem rows10010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10010 = true := by
  decide +kernel

theorem tot10010 : totK PD2M8K2 D2M8K2.t10010 = [0, 0, 191324996611, 452849637319, 238949875032, 18811479346, 0, 0] := by
  decide +kernel

theorem rows10011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10011 = true := by
  decide +kernel

theorem tot10011 : totK PD2M8K2 D2M8K2.t10011 = [0, 0, 187666087800, 468956874210, 242853326316, 18825657308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
