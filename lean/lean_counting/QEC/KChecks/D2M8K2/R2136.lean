import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8544 = true := by
  decide +kernel

theorem tot8544 : totK PD2M8K2 D2M8K2.t8544 = [157078190040, 405601434799, 286289516025, 65860460563, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows8545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8545 = true := by
  decide +kernel

theorem tot8545 : totK PD2M8K2 D2M8K2.t8545 = [204430365094, 465298927939, 223674683314, 17465085447, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8546 = true := by
  decide +kernel

theorem tot8546 : totK PD2M8K2 D2M8K2.t8546 = [44268419162, 328129093908, 433328792473, 95656906893, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows8547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8547 = true := by
  decide +kernel

theorem tot8547 : totK PD2M8K2 D2M8K2.t8547 = [0, 210302903562, 480733062912, 188164972348, 7416187986, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
