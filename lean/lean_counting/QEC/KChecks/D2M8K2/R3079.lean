import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12316 = true := by
  decide +kernel

theorem tot12316 : totK PD2M8K2 D2M8K2.t12316 = [175307437418, 486718476266, 242743907688, 12435483790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12317 = true := by
  decide +kernel

theorem tot12317 : totK PD2M8K2 D2M8K2.t12317 = [0, 218498563430, 459116733527, 207104391625, 21383112939, 0, 0, 0] := by
  decide +kernel

theorem rows12318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12318 = true := by
  decide +kernel

theorem tot12318 : totK PD2M8K2 D2M8K2.t12318 = [0, 175735370067, 491498667251, 221299491136, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows12319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12319 = true := by
  decide +kernel

theorem tot12319 : totK PD2M8K2 D2M8K2.t12319 = [127020531876, 345365411670, 290374417124, 129987921513, 7986795957, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
