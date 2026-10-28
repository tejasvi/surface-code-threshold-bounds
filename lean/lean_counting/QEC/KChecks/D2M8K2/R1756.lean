import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7024 = true := by
  decide +kernel

theorem tot7024 : totK PD2M8K2 D2M8K2.t7024 = [0, 181504700283, 457730784083, 249143246077, 22625829262, 0, 0, 0] := by
  decide +kernel

theorem rows7025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7025 = true := by
  decide +kernel

theorem tot7025 : totK PD2M8K2 D2M8K2.t7025 = [0, 156402592020, 462656994626, 262831514685, 16088058026, 0, 0, 0] := by
  decide +kernel

theorem rows7026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7026 = true := by
  decide +kernel

theorem tot7026 : totK PD2M8K2 D2M8K2.t7026 = [0, 0, 278755863239, 496759074609, 108778229967, 1198073392, 0, 0] := by
  decide +kernel

theorem rows7027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7027 = true := by
  decide +kernel

theorem tot7027 : totK PD2M8K2 D2M8K2.t7027 = [0, 78906945190, 250509715892, 379764233737, 152944328249, 7458616031, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
