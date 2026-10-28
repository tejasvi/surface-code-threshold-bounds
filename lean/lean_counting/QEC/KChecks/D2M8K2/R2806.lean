import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11224 = true := by
  decide +kernel

theorem tot11224 : totK PD2M8K2 D2M8K2.t11224 = [83129192267, 342213577452, 384110519222, 84812884053, 1190718505, 0, 0, 0] := by
  decide +kernel

theorem rows11225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11225 = true := by
  decide +kernel

theorem tot11225 : totK PD2M8K2 D2M8K2.t11225 = [0, 210526484708, 485027378139, 176783142453, 9437315879, 0, 0, 0] := by
  decide +kernel

theorem rows11226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11226 = true := by
  decide +kernel

theorem tot11226 : totK PD2M8K2 D2M8K2.t11226 = [157178716305, 426024024492, 269219350104, 55758590750, 2566665356, 0, 0, 0] := by
  decide +kernel

theorem rows11227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11227 = true := by
  decide +kernel

theorem tot11227 : totK PD2M8K2 D2M8K2.t11227 = [172641319454, 440560418566, 269919911598, 21201121382, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
