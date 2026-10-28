import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2832 = true := by
  decide +kernel

theorem tot2832 : totK PD2M8K2 D2M8K2.t2832 = [46923206314, 236298941515, 415619209668, 172627863342, 10770125763, 0, 0, 0] := by
  decide +kernel

theorem rows2833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2833 = true := by
  decide +kernel

theorem tot2833 : totK PD2M8K2 D2M8K2.t2833 = [194613480561, 462376921979, 242675750638, 23412915585, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2834 = true := by
  decide +kernel

theorem tot2834 : totK PD2M8K2 D2M8K2.t2834 = [170291197795, 452000161067, 254616896775, 17942593752, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2835 = true := by
  decide +kernel

theorem tot2835 : totK PD2M8K2 D2M8K2.t2835 = [0, 307806488793, 489445038564, 96047934117, 1096156699, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
