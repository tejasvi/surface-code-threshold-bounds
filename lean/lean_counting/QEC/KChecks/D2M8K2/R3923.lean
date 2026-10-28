import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15692 = true := by
  decide +kernel

theorem tot15692 : totK PD2M8K2 D2M8K2.t15692 = [0, 0, 0, 178131578373, 475286783354, 216152048452, 13087881535, 0] := by
  decide +kernel

theorem rows15693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15693 = true := by
  decide +kernel

theorem tot15693 : totK PD2M8K2 D2M8K2.t15693 = [0, 0, 0, 226786914083, 489988163072, 136468260767, 2267390657, 0] := by
  decide +kernel

theorem rows15694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15694 = true := by
  decide +kernel

theorem tot15694 : totK PD2M8K2 D2M8K2.t15694 = [0, 0, 0, 19319729168, 332217646397, 421120177142, 70067724884, 1275377855] := by
  decide +kernel

theorem rows15695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15695 = true := by
  decide +kernel

theorem tot15695 : totK PD2M8K2 D2M8K2.t15695 = [0, 0, 0, 123420919501, 464377578983, 266088665785, 14156579939, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
