import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12924 = true := by
  decide +kernel

theorem tot12924 : totK PD2M8K2 D2M8K2.t12924 = [0, 0, 283099954400, 505948044951, 110635319344, 1163840124, 0, 0] := by
  decide +kernel

theorem rows12925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12925 = true := by
  decide +kernel

theorem tot12925 : totK PD2M8K2 D2M8K2.t12925 = [0, 19810472444, 195233026176, 459162822306, 188020161296, 11873025674, 0, 0] := by
  decide +kernel

theorem rows12926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12926 = true := by
  decide +kernel

theorem tot12926 : totK PD2M8K2 D2M8K2.t12926 = [0, 175904044763, 450039846800, 266045091921, 29451677789, 0, 0, 0] := by
  decide +kernel

theorem rows12927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12927 = true := by
  decide +kernel

theorem tot12927 : totK PD2M8K2 D2M8K2.t12927 = [0, 135711510589, 450365079425, 308345511254, 30476059078, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
