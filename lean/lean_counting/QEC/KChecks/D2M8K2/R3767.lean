import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15068 = true := by
  decide +kernel

theorem tot15068 : totK PD2M8K2 D2M8K2.t15068 = [0, 174605525350, 464777611968, 250916065294, 17567433490, 0, 0, 0] := by
  decide +kernel

theorem rows15069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15069 = true := by
  decide +kernel

theorem tot15069 : totK PD2M8K2 D2M8K2.t15069 = [0, 0, 276320920428, 517192539033, 108918146155, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15070 = true := by
  decide +kernel

theorem tot15070 : totK PD2M8K2 D2M8K2.t15070 = [0, 132924425514, 426862542039, 321407624914, 34088416877, 0, 0, 0] := by
  decide +kernel

theorem rows15071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15071 = true := by
  decide +kernel

theorem tot15071 : totK PD2M8K2 D2M8K2.t15071 = [0, 173923538610, 438435364438, 248574265297, 25546137855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
