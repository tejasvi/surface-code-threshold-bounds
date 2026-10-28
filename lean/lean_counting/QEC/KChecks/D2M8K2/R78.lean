import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t312 = true := by
  decide +kernel

theorem tot312 : totK PD2M8K2 D2M8K2.t312 = [0, 203114780168, 467618139389, 206278070485, 12403393969, 0, 0, 0] := by
  decide +kernel

theorem rows313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t313 = true := by
  decide +kernel

theorem tot313 : totK PD2M8K2 D2M8K2.t313 = [0, 177992482054, 475436866883, 232730768365, 9478852111, 0, 0, 0] := by
  decide +kernel

theorem rows314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t314 = true := by
  decide +kernel

theorem tot314 : totK PD2M8K2 D2M8K2.t314 = [0, 171584893284, 471395394136, 245664354099, 11616684087, 0, 0, 0] := by
  decide +kernel

theorem rows315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t315 = true := by
  decide +kernel

theorem tot315 : totK PD2M8K2 D2M8K2.t315 = [182913464330, 430875139593, 256621260178, 56812275683, 8621106361, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
