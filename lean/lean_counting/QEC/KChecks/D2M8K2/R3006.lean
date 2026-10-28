import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12024 = true := by
  decide +kernel

theorem tot12024 : totK PD2M8K2 D2M8K2.t12024 = [0, 92493905117, 388380980630, 385970997002, 44249133434, 0, 0, 0] := by
  decide +kernel

theorem rows12025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12025 = true := by
  decide +kernel

theorem tot12025 : totK PD2M8K2 D2M8K2.t12025 = [0, 201163910713, 463921456864, 236392515954, 16606260802, 0, 0, 0] := by
  decide +kernel

theorem rows12026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12026 = true := by
  decide +kernel

theorem tot12026 : totK PD2M8K2 D2M8K2.t12026 = [0, 197172116766, 478074314898, 216591190141, 14786210108, 0, 0, 0] := by
  decide +kernel

theorem rows12027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12027 = true := by
  decide +kernel

theorem tot12027 : totK PD2M8K2 D2M8K2.t12027 = [0, 179799603966, 463575096141, 247412896789, 20731568732, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
