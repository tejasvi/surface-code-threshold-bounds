import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9940 = true := by
  decide +kernel

theorem tot9940 : totK PD2M8K2 D2M8K2.t9940 = [0, 0, 167936392164, 466137592802, 246873123236, 10810644198, 0, 0] := by
  decide +kernel

theorem rows9941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9941 = true := by
  decide +kernel

theorem tot9941 : totK PD2M8K2 D2M8K2.t9941 = [0, 0, 91438162061, 353859108191, 374670491179, 73644494421, 1268739303, 0] := by
  decide +kernel

theorem rows9942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9942 = true := by
  decide +kernel

theorem tot9942 : totK PD2M8K2 D2M8K2.t9942 = [0, 0, 0, 285183257207, 478203597330, 111790934851, 3703146322, 0] := by
  decide +kernel

theorem rows9943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9943 = true := by
  decide +kernel

theorem tot9943 : totK PD2M8K2 D2M8K2.t9943 = [0, 0, 0, 201764129773, 486758343176, 187954887579, 10251481072, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
