import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6620 = true := by
  decide +kernel

theorem tot6620 : totK PD2M8K2 D2M8K2.t6620 = [0, 0, 225371690251, 480078470756, 160087567015, 8404294179, 0, 0] := by
  decide +kernel

theorem rows6621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6621 = true := by
  decide +kernel

theorem tot6621 : totK PD2M8K2 D2M8K2.t6621 = [0, 147341817518, 370517751517, 287684945585, 74119828145, 3581949829, 0, 0] := by
  decide +kernel

theorem rows6622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6622 = true := by
  decide +kernel

theorem tot6622 : totK PD2M8K2 D2M8K2.t6622 = [0, 180361365963, 440323069117, 244421933156, 23299516178, 0, 0, 0] := by
  decide +kernel

theorem rows6623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6623 = true := by
  decide +kernel

theorem tot6623 : totK PD2M8K2 D2M8K2.t6623 = [0, 91543030234, 402961814477, 340069748668, 46472177039, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
