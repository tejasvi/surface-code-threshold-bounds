import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3216 = true := by
  decide +kernel

theorem tot3216 : totK PD2M8K2 D2M8K2.t3216 = [0, 198773141303, 484384064272, 192126548281, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows3217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3217 = true := by
  decide +kernel

theorem tot3217 : totK PD2M8K2 D2M8K2.t3217 = [83604988011, 316302754238, 377816193107, 102231853300, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows3218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3218 = true := by
  decide +kernel

theorem tot3218 : totK PD2M8K2 D2M8K2.t3218 = [171119600999, 463068853627, 255024513330, 22885466195, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3219 = true := by
  decide +kernel

theorem tot3219 : totK PD2M8K2 D2M8K2.t3219 = [181015165609, 470030748773, 240257460990, 17034666133, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
