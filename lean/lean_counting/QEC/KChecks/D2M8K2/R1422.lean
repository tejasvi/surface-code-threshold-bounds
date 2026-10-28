import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5688 = true := by
  decide +kernel

theorem tot5688 : totK PD2M8K2 D2M8K2.t5688 = [0, 18633565008, 265851244301, 473490667631, 112100802569, 3838026431, 0, 0] := by
  decide +kernel

theorem rows5689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5689 = true := by
  decide +kernel

theorem tot5689 : totK PD2M8K2 D2M8K2.t5689 = [0, 199902590538, 473343195910, 220038965773, 13007015260, 0, 0, 0] := by
  decide +kernel

theorem rows5690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5690 = true := by
  decide +kernel

theorem tot5690 : totK PD2M8K2 D2M8K2.t5690 = [0, 179280412537, 455415449128, 232430811038, 16886077592, 0, 0, 0] := by
  decide +kernel

theorem rows5691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5691 = true := by
  decide +kernel

theorem tot5691 : totK PD2M8K2 D2M8K2.t5691 = [0, 19692840307, 305109468294, 479522109883, 97595874193, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
