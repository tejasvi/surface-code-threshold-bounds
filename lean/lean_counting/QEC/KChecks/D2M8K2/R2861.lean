import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11444 = true := by
  decide +kernel

theorem tot11444 : totK PD2M8K2 D2M8K2.t11444 = [0, 112281440014, 423997255242, 305464694952, 37293483734, 1096505104, 0, 0] := by
  decide +kernel

theorem rows11445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11445 = true := by
  decide +kernel

theorem tot11445 : totK PD2M8K2 D2M8K2.t11445 = [0, 0, 299733617846, 520003325693, 93957643713, 0, 0, 0] := by
  decide +kernel

theorem rows11446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11446 = true := by
  decide +kernel

theorem tot11446 : totK PD2M8K2 D2M8K2.t11446 = [0, 152998322173, 372057098727, 282359605789, 89693139660, 3884009855, 0, 0] := by
  decide +kernel

theorem rows11447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11447 = true := by
  decide +kernel

theorem tot11447 : totK PD2M8K2 D2M8K2.t11447 = [0, 167654476840, 449861044450, 269671202395, 22419054225, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
