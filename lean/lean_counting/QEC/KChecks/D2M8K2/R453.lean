import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1812 = true := by
  decide +kernel

theorem tot1812 : totK PD2M8K2 D2M8K2.t1812 = [0, 0, 216485983180, 484331493537, 191937081914, 5430665091, 0, 0] := by
  decide +kernel

theorem rows1813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1813 = true := by
  decide +kernel

theorem tot1813 : totK PD2M8K2 D2M8K2.t1813 = [0, 161348482468, 371355786981, 260728340053, 109004649862, 6804944647, 0, 0] := by
  decide +kernel

theorem rows1814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1814 = true := by
  decide +kernel

theorem tot1814 : totK PD2M8K2 D2M8K2.t1814 = [0, 177628207202, 451585311244, 259706780375, 19898758738, 0, 0, 0] := by
  decide +kernel

theorem rows1815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1815 = true := by
  decide +kernel

theorem tot1815 : totK PD2M8K2 D2M8K2.t1815 = [0, 87048265658, 363688013145, 362134271616, 68336713217, 1163840124, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
