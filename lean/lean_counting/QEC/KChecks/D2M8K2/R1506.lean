import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6024 = true := by
  decide +kernel

theorem tot6024 : totK PD2M8K2 D2M8K2.t6024 = [0, 0, 208903506476, 476863161411, 198249216397, 9721971944, 0, 0] := by
  decide +kernel

theorem rows6025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6025 = true := by
  decide +kernel

theorem tot6025 : totK PD2M8K2 D2M8K2.t6025 = [0, 0, 15600880210, 412351093771, 409384974578, 37042247584, 0, 0] := by
  decide +kernel

theorem rows6026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6026 = true := by
  decide +kernel

theorem tot6026 : totK PD2M8K2 D2M8K2.t6026 = [0, 0, 147814366811, 357093818902, 301501851573, 58501049344, 1225787871, 0] := by
  decide +kernel

theorem rows6027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6027 = true := by
  decide +kernel

theorem tot6027 : totK PD2M8K2 D2M8K2.t6027 = [0, 0, 174324943065, 446161589178, 262582110647, 24996295453, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
