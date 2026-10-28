import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4708 = true := by
  decide +kernel

theorem tot4708 : totK PD2M8K2 D2M8K2.t4708 = [0, 0, 0, 270299895739, 492561325621, 131516630677, 4031931762, 0] := by
  decide +kernel

theorem rows4709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4709 = true := by
  decide +kernel

theorem tot4709 : totK PD2M8K2 D2M8K2.t4709 = [0, 0, 131086254231, 361394603892, 314728555975, 70420918742, 1186940923, 0] := by
  decide +kernel

theorem rows4710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4710 = true := by
  decide +kernel

theorem tot4710 : totK PD2M8K2 D2M8K2.t4710 = [0, 0, 170525466099, 449941237843, 271840678928, 28727720614, 0, 0] := by
  decide +kernel

theorem rows4711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4711 = true := by
  decide +kernel

theorem tot4711 : totK PD2M8K2 D2M8K2.t4711 = [0, 0, 105483853045, 427767093095, 325660456507, 26792153874, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
