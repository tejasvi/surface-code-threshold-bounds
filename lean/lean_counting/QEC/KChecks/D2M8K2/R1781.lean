import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7124 = true := by
  decide +kernel

theorem tot7124 : totK PD2M8K2 D2M8K2.t7124 = [0, 0, 232439857462, 506474245096, 156091363050, 3544300177, 0, 0] := by
  decide +kernel

theorem rows7125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7125 = true := by
  decide +kernel

theorem tot7125 : totK PD2M8K2 D2M8K2.t7125 = [0, 70826781172, 266681339281, 391612378144, 134759195987, 9706385084, 0, 0] := by
  decide +kernel

theorem rows7126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7126 = true := by
  decide +kernel

theorem tot7126 : totK PD2M8K2 D2M8K2.t7126 = [0, 149770661622, 455894601169, 266257317820, 18754971501, 0, 0, 0] := by
  decide +kernel

theorem rows7127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7127 = true := by
  decide +kernel

theorem tot7127 : totK PD2M8K2 D2M8K2.t7127 = [0, 177492465105, 462820663512, 237615704029, 14985674079, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
