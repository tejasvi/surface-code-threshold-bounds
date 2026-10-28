import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3192 = true := by
  decide +kernel

theorem tot3192 : totK PD2M8K2 D2M8K2.t3192 = [0, 185008984658, 468852972684, 246344309469, 19920018668, 0, 0, 0] := by
  decide +kernel

theorem rows3193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3193 = true := by
  decide +kernel

theorem tot3193 : totK PD2M8K2 D2M8K2.t3193 = [0, 189068351840, 478741719327, 220225227807, 12439805748, 0, 0, 0] := by
  decide +kernel

theorem rows3194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3194 = true := by
  decide +kernel

theorem tot3194 : totK PD2M8K2 D2M8K2.t3194 = [0, 11795538417, 314745500362, 459798832301, 89199916630, 1171084559, 0, 0] := by
  decide +kernel

theorem rows3195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3195 = true := by
  decide +kernel

theorem tot3195 : totK PD2M8K2 D2M8K2.t3195 = [0, 0, 202887372966, 453261106831, 187230465404, 11934365838, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
