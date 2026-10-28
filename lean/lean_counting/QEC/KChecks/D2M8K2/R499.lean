import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1996 = true := by
  decide +kernel

theorem tot1996 : totK PD2M8K2 D2M8K2.t1996 = [0, 0, 128005003128, 369960677436, 320842298303, 66837369464, 1186940923, 0] := by
  decide +kernel

theorem rows1997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1997 = true := by
  decide +kernel

theorem tot1997 : totK PD2M8K2 D2M8K2.t1997 = [0, 0, 180907398874, 479570257411, 235093575525, 13816308382, 0, 0] := by
  decide +kernel

theorem rows1998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1998 = true := by
  decide +kernel

theorem tot1998 : totK PD2M8K2 D2M8K2.t1998 = [0, 0, 90363393300, 427281114809, 352010542434, 26802751803, 0, 0] := by
  decide +kernel

theorem rows1999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1999 = true := by
  decide +kernel

theorem tot1999 : totK PD2M8K2 D2M8K2.t1999 = [0, 0, 49001272151, 312708789779, 430272416204, 88081694626, 1415142070, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
