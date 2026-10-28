import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13616 = true := by
  decide +kernel

theorem tot13616 : totK PD2M8K2 D2M8K2.t13616 = [0, 211223132966, 492978126475, 174474862361, 7233348802, 0, 0, 0] := by
  decide +kernel

theorem rows13617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13617 = true := by
  decide +kernel

theorem tot13617 : totK PD2M8K2 D2M8K2.t13617 = [86654048599, 305518795123, 368901843119, 117732939151, 6017336459, 0, 0, 0] := by
  decide +kernel

theorem rows13618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13618 = true := by
  decide +kernel

theorem tot13618 : totK PD2M8K2 D2M8K2.t13618 = [158754904229, 450757956572, 268597651158, 24914371804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13619 = true := by
  decide +kernel

theorem tot13619 : totK PD2M8K2 D2M8K2.t13619 = [178159790803, 473543668807, 231378035610, 12169895203, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
