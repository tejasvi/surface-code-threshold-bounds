import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15392 = true := by
  decide +kernel

theorem tot15392 : totK PD2M8K2 D2M8K2.t15392 = [0, 0, 93421458046, 395503232469, 376437525387, 46578251111, 0, 0] := by
  decide +kernel

theorem rows15393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15393 = true := by
  decide +kernel

theorem tot15393 : totK PD2M8K2 D2M8K2.t15393 = [0, 0, 161704512989, 454884238175, 275185250143, 21426882695, 0, 0] := by
  decide +kernel

theorem rows15394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15394 = true := by
  decide +kernel

theorem tot15394 : totK PD2M8K2 D2M8K2.t15394 = [0, 0, 176307728821, 460036378522, 242846431947, 15306627970, 0, 0] := by
  decide +kernel

theorem rows15395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15395 = true := by
  decide +kernel

theorem tot15395 : totK PD2M8K2 D2M8K2.t15395 = [0, 0, 200090185068, 473979584443, 220586029730, 16104584588, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
