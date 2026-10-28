import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5848 = true := by
  decide +kernel

theorem tot5848 : totK PD2M8K2 D2M8K2.t5848 = [0, 28691463541, 211639756286, 423412723719, 178408307873, 11853261585, 0, 0] := by
  decide +kernel

theorem rows5849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5849 = true := by
  decide +kernel

theorem tot5849 : totK PD2M8K2 D2M8K2.t5849 = [0, 199059243816, 480533764976, 218497711072, 11056080877, 0, 0, 0] := by
  decide +kernel

theorem rows5850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5850 = true := by
  decide +kernel

theorem tot5850 : totK PD2M8K2 D2M8K2.t5850 = [0, 179018588661, 467621161072, 221462992095, 13126448176, 0, 0, 0] := by
  decide +kernel

theorem rows5851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5851 = true := by
  decide +kernel

theorem tot5851 : totK PD2M8K2 D2M8K2.t5851 = [0, 0, 320708112466, 460687327307, 76387210362, 1021600638, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
