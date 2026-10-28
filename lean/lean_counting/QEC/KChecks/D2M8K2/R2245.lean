import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8980 = true := by
  decide +kernel

theorem tot8980 : totK PD2M8K2 D2M8K2.t8980 = [19983817196, 332177020540, 495736426112, 64524241544, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8981 = true := by
  decide +kernel

theorem tot8981 : totK PD2M8K2 D2M8K2.t8981 = [166391666423, 444836358145, 269009066953, 28762931361, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8982 = true := by
  decide +kernel

theorem tot8982 : totK PD2M8K2 D2M8K2.t8982 = [208984456772, 488429965722, 210255983266, 11111954526, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8983 = true := by
  decide +kernel

theorem tot8983 : totK PD2M8K2 D2M8K2.t8983 = [19519064759, 266563093355, 417555097828, 189341549181, 21379892652, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
