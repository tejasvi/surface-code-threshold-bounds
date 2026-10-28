import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15940 = true := by
  decide +kernel

theorem tot15940 : totK PD2M8K2 D2M8K2.t15940 = [0, 0, 165135038218, 459830618259, 270170368153, 20458103379, 0, 0] := by
  decide +kernel

theorem rows15941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15941 = true := by
  decide +kernel

theorem tot15941 : totK PD2M8K2 D2M8K2.t15941 = [0, 0, 191673853497, 467821380910, 234137563364, 19122002952, 0, 0] := by
  decide +kernel

theorem rows15942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15942 = true := by
  decide +kernel

theorem tot15942 : totK PD2M8K2 D2M8K2.t15942 = [0, 0, 141655997326, 446032910719, 301959818498, 24503300662, 0, 0] := by
  decide +kernel

theorem rows15943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15943 = true := by
  decide +kernel

theorem tot15943 : totK PD2M8K2 D2M8K2.t15943 = [0, 0, 0, 238669277971, 486470336969, 134790219247, 4879840392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
