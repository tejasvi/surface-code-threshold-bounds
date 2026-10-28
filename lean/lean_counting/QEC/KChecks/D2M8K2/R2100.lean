import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8400 = true := by
  decide +kernel

theorem tot8400 : totK PD2M8K2 D2M8K2.t8400 = [0, 0, 319711256551, 508633476970, 60148155503, 0, 0, 0] := by
  decide +kernel

theorem rows8401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8401 = true := by
  decide +kernel

theorem tot8401 : totK PD2M8K2 D2M8K2.t8401 = [0, 155397482314, 399859374047, 265335020615, 67761426756, 3838026431, 0, 0] := by
  decide +kernel

theorem rows8402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8402 = true := by
  decide +kernel

theorem tot8402 : totK PD2M8K2 D2M8K2.t8402 = [0, 177255273126, 438963053877, 239898817899, 21317478667, 0, 0, 0] := by
  decide +kernel

theorem rows8403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8403 = true := by
  decide +kernel

theorem tot8403 : totK PD2M8K2 D2M8K2.t8403 = [0, 81083826013, 341204703860, 389637403656, 87204859544, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
