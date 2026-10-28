import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14544 = true := by
  decide +kernel

theorem tot14544 : totK PD2M8K2 D2M8K2.t14544 = [11292364526, 191327041818, 468964085943, 196397376461, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows14545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14545 = true := by
  decide +kernel

theorem tot14545 : totK PD2M8K2 D2M8K2.t14545 = [176982733231, 454137548822, 245980458308, 23013209429, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14546 = true := by
  decide +kernel

theorem tot14546 : totK PD2M8K2 D2M8K2.t14546 = [198229138187, 457754552227, 233154659722, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14547 = true := by
  decide +kernel

theorem tot14547 : totK PD2M8K2 D2M8K2.t14547 = [37683970795, 335726306657, 431473487756, 83545339936, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
