import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7172 = true := by
  decide +kernel

theorem tot7172 : totK PD2M8K2 D2M8K2.t7172 = [0, 0, 204418298861, 479457712131, 204593904361, 11079121886, 0, 0] := by
  decide +kernel

theorem rows7173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7173 = true := by
  decide +kernel

theorem tot7173 : totK PD2M8K2 D2M8K2.t7173 = [0, 0, 179996739627, 449781968631, 221135283104, 16702988424, 0, 0] := by
  decide +kernel

theorem rows7174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7174 = true := by
  decide +kernel

theorem tot7174 : totK PD2M8K2 D2M8K2.t7174 = [0, 0, 44484974065, 351857832243, 392220155058, 69820475439, 1095107716, 0] := by
  decide +kernel

theorem rows7175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7175 = true := by
  decide +kernel

theorem tot7175 : totK PD2M8K2 D2M8K2.t7175 = [0, 55323524080, 78046813715, 240872265416, 390813573526, 104401777211, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
