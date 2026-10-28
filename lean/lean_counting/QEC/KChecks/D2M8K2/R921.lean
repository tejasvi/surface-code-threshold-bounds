import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3684 = true := by
  decide +kernel

theorem tot3684 : totK PD2M8K2 D2M8K2.t3684 = [0, 0, 178670032154, 460971735926, 229746126940, 19062413642, 0, 0] := by
  decide +kernel

theorem rows3685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3685 = true := by
  decide +kernel

theorem tot3685 : totK PD2M8K2 D2M8K2.t3685 = [0, 0, 222299685463, 486604390480, 159657280683, 4059686398, 0, 0] := by
  decide +kernel

theorem rows3686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3686 = true := by
  decide +kernel

theorem tot3686 : totK PD2M8K2 D2M8K2.t3686 = [0, 0, 186420700856, 465207168993, 221213883985, 18069584445, 0, 0] := by
  decide +kernel

theorem rows3687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3687 = true := by
  decide +kernel

theorem tot3687 : totK PD2M8K2 D2M8K2.t3687 = [0, 0, 203966784828, 482886119982, 182510937582, 5187627908, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
