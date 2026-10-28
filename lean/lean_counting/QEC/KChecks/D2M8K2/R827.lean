import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3308 = true := by
  decide +kernel

theorem tot3308 : totK PD2M8K2 D2M8K2.t3308 = [0, 0, 215787072224, 484191298306, 185708925517, 9642442870, 0, 0] := by
  decide +kernel

theorem rows3309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3309 = true := by
  decide +kernel

theorem tot3309 : totK PD2M8K2 D2M8K2.t3309 = [0, 84648349195, 318649440379, 367507826430, 100637070989, 3540641832, 0, 0] := by
  decide +kernel

theorem rows3310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3310 = true := by
  decide +kernel

theorem tot3310 : totK PD2M8K2 D2M8K2.t3310 = [0, 176514844497, 449591965286, 262187778979, 29320126623, 0, 0, 0] := by
  decide +kernel

theorem rows3311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3311 = true := by
  decide +kernel

theorem tot3311 : totK PD2M8K2 D2M8K2.t3311 = [0, 150347957763, 461041998841, 267045934235, 16271664442, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
