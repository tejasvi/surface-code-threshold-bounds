import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6564 = true := by
  decide +kernel

theorem tot6564 : totK PD2M8K2 D2M8K2.t6564 = [0, 30119930720, 334426042707, 458750737447, 55862963458, 0, 0, 0] := by
  decide +kernel

theorem rows6565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6565 = true := by
  decide +kernel

theorem tot6565 : totK PD2M8K2 D2M8K2.t6565 = [0, 184081199891, 453449406581, 258936616591, 25997048245, 0, 0, 0] := by
  decide +kernel

theorem rows6566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6566 = true := by
  decide +kernel

theorem tot6566 : totK PD2M8K2 D2M8K2.t6566 = [0, 191609687686, 487593457944, 218342215392, 11311631362, 0, 0, 0] := by
  decide +kernel

theorem rows6567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6567 = true := by
  decide +kernel

theorem tot6567 : totK PD2M8K2 D2M8K2.t6567 = [0, 171436711638, 456815148683, 240044860103, 22046266515, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
