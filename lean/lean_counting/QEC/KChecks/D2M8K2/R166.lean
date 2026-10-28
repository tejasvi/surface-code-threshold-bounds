import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t664 = true := by
  decide +kernel

theorem tot664 : totK PD2M8K2 D2M8K2.t664 = [70504094640, 273320517513, 399840948836, 136341375953, 7481811052, 0, 0, 0] := by
  decide +kernel

theorem rows665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t665 = true := by
  decide +kernel

theorem tot665 : totK PD2M8K2 D2M8K2.t665 = [165127163482, 447890804535, 253224186369, 22530616956, 0, 0, 0, 0] := by
  decide +kernel

theorem rows666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t666 = true := by
  decide +kernel

theorem tot666 : totK PD2M8K2 D2M8K2.t666 = [180567783026, 457040107812, 245555050109, 18151193667, 0, 0, 0, 0] := by
  decide +kernel

theorem rows667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t667 = true := by
  decide +kernel

theorem tot667 : totK PD2M8K2 D2M8K2.t667 = [0, 293193833835, 485982020788, 96113016941, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
