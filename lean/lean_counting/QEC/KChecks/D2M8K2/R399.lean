import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1596 = true := by
  decide +kernel

theorem tot1596 : totK PD2M8K2 D2M8K2.t1596 = [0, 0, 169911946685, 487660864532, 222934324414, 10828911703, 0, 0] := by
  decide +kernel

theorem rows1597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1597 = true := by
  decide +kernel

theorem tot1597 : totK PD2M8K2 D2M8K2.t1597 = [0, 0, 191276735549, 463097330527, 244193847036, 15910705641, 0, 0] := by
  decide +kernel

theorem rows1598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1598 = true := by
  decide +kernel

theorem tot1598 : totK PD2M8K2 D2M8K2.t1598 = [0, 0, 159898812404, 459431062343, 252334849837, 16322715397, 0, 0] := by
  decide +kernel

theorem rows1599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1599 = true := by
  decide +kernel

theorem tot1599 : totK PD2M8K2 D2M8K2.t1599 = [0, 0, 0, 227409017439, 464340968908, 158816790079, 8182138156, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
