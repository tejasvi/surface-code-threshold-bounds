import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3708 = true := by
  decide +kernel

theorem tot3708 : totK PD2M8K2 D2M8K2.t3708 = [0, 184694548526, 447725917073, 214727316031, 16632994142, 0, 0, 0] := by
  decide +kernel

theorem rows3709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3709 = true := by
  decide +kernel

theorem tot3709 : totK PD2M8K2 D2M8K2.t3709 = [0, 123760567405, 432892506750, 289565319795, 28000958262, 0, 0, 0] := by
  decide +kernel

theorem rows3710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3710 = true := by
  decide +kernel

theorem tot3710 : totK PD2M8K2 D2M8K2.t3710 = [0, 0, 278330432701, 465358935369, 106054577203, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3711 = true := by
  decide +kernel

theorem tot3711 : totK PD2M8K2 D2M8K2.t3711 = [0, 158177155286, 460562077933, 254832270286, 17873950257, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
