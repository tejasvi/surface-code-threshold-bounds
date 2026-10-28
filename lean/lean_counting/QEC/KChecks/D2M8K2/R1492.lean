import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5968 = true := by
  decide +kernel

theorem tot5968 : totK PD2M8K2 D2M8K2.t5968 = [0, 178780247251, 457729419008, 234664197196, 16862812821, 0, 0, 0] := by
  decide +kernel

theorem rows5969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5969 = true := by
  decide +kernel

theorem tot5969 : totK PD2M8K2 D2M8K2.t5969 = [0, 37505423682, 343286293820, 438719077051, 73704544584, 0, 0, 0] := by
  decide +kernel

theorem rows5970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5970 = true := by
  decide +kernel

theorem tot5970 : totK PD2M8K2 D2M8K2.t5970 = [0, 47974210774, 286870583385, 437261410894, 115498560852, 2498823382, 0, 0] := by
  decide +kernel

theorem rows5971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5971 = true := by
  decide +kernel

theorem tot5971 : totK PD2M8K2 D2M8K2.t5971 = [0, 196626447943, 475044953856, 237500708893, 22016217787, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
