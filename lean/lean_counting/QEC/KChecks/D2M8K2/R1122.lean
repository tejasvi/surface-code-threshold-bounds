import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4488 = true := by
  decide +kernel

theorem tot4488 : totK PD2M8K2 D2M8K2.t4488 = [0, 0, 191622982787, 483978556415, 192167388004, 6406394852, 0, 0] := by
  decide +kernel

theorem rows4489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4489 = true := by
  decide +kernel

theorem tot4489 : totK PD2M8K2 D2M8K2.t4489 = [0, 0, 167782580109, 457342645779, 229547196673, 14851596150, 0, 0] := by
  decide +kernel

theorem rows4490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4490 = true := by
  decide +kernel

theorem tot4490 : totK PD2M8K2 D2M8K2.t4490 = [0, 0, 35626037306, 341406817191, 398206726126, 65948778244, 1138244013, 0] := by
  decide +kernel

theorem rows4491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4491 = true := by
  decide +kernel

theorem tot4491 : totK PD2M8K2 D2M8K2.t4491 = [0, 0, 111013743611, 397565313385, 351660351388, 40979683914, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
