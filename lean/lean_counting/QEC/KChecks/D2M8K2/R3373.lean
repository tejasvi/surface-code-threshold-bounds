import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13492 = true := by
  decide +kernel

theorem tot13492 : totK PD2M8K2 D2M8K2.t13492 = [0, 0, 0, 0, 303243128537, 446497089981, 80061169291, 1138244013] := by
  decide +kernel

theorem rows13493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13493 = true := by
  decide +kernel

theorem tot13493 : totK PD2M8K2 D2M8K2.t13493 = [0, 0, 0, 176589460606, 463920486489, 228805740254, 19211107523, 0] := by
  decide +kernel

theorem rows13494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13494 = true := by
  decide +kernel

theorem tot13494 : totK PD2M8K2 D2M8K2.t13494 = [0, 0, 0, 197521541177, 487457268850, 202131664755, 7062972541, 0] := by
  decide +kernel

theorem rows13495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13495 = true := by
  decide +kernel

theorem tot13495 : totK PD2M8K2 D2M8K2.t13495 = [0, 0, 0, 210052783005, 469142898402, 179808071299, 10856745823, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
