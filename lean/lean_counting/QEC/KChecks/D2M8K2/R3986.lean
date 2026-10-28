import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15944 = true := by
  decide +kernel

theorem tot15944 : totK PD2M8K2 D2M8K2.t15944 = [0, 0, 172582919210, 459353734351, 257159644054, 27320705525, 0, 0] := by
  decide +kernel

theorem rows15945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15945 = true := by
  decide +kernel

theorem tot15945 : totK PD2M8K2 D2M8K2.t15945 = [0, 0, 162473131778, 447975403065, 258992112062, 19126771796, 0, 0] := by
  decide +kernel

theorem rows15946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15946 = true := by
  decide +kernel

theorem tot15946 : totK PD2M8K2 D2M8K2.t15946 = [0, 0, 89413136837, 351945069793, 374102015360, 71073685066, 1107157161, 0] := by
  decide +kernel

theorem rows15947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15947 = true := by
  decide +kernel

theorem tot15947 : totK PD2M8K2 D2M8K2.t15947 = [0, 0, 3757402556, 287710369878, 469579734819, 112378026623, 3824247485, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
