import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10676 = true := by
  decide +kernel

theorem tot10676 : totK PD2M8K2 D2M8K2.t10676 = [0, 0, 55761343512, 348887282455, 411144753614, 72384252442, 1096505104, 0] := by
  decide +kernel

theorem rows10677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10677 = true := by
  decide +kernel

theorem tot10677 : totK PD2M8K2 D2M8K2.t10677 = [0, 0, 18633565008, 270069396634, 475260813981, 112919988284, 3884009855, 0] := by
  decide +kernel

theorem rows10678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10678 = true := by
  decide +kernel

theorem tot10678 : totK PD2M8K2 D2M8K2.t10678 = [0, 0, 218756350106, 505869025129, 167024192457, 2519575154, 0, 0] := by
  decide +kernel

theorem rows10679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10679 = true := by
  decide +kernel

theorem tot10679 : totK PD2M8K2 D2M8K2.t10679 = [0, 0, 87591894987, 382158181018, 365549287611, 54414243430, 1268739303, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
