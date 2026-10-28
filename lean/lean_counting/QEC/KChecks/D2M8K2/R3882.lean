import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15528 = true := by
  decide +kernel

theorem tot15528 : totK PD2M8K2 D2M8K2.t15528 = [0, 0, 180882642338, 481362802947, 223358962627, 11338727351, 0, 0] := by
  decide +kernel

theorem rows15529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15529 = true := by
  decide +kernel

theorem tot15529 : totK PD2M8K2 D2M8K2.t15529 = [0, 0, 169917934377, 475698344283, 232761130394, 12999488118, 0, 0] := by
  decide +kernel

theorem rows15530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15530 = true := by
  decide +kernel

theorem tot15530 : totK PD2M8K2 D2M8K2.t15530 = [0, 0, 206826228867, 486337215248, 187307325965, 3921178515, 0, 0] := by
  decide +kernel

theorem rows15531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15531 = true := by
  decide +kernel

theorem tot15531 : totK PD2M8K2 D2M8K2.t15531 = [0, 0, 177741486418, 466614820659, 209958067969, 12284330786, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
