import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12820 = true := by
  decide +kernel

theorem tot12820 : totK PD2M8K2 D2M8K2.t12820 = [0, 0, 0, 321886147286, 468750729732, 78556400385, 1053411165, 0] := by
  decide +kernel

theorem rows12821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12821 = true := by
  decide +kernel

theorem tot12821 : totK PD2M8K2 D2M8K2.t12821 = [0, 0, 152604957350, 374283083647, 269126037042, 75045596992, 3667207281, 0] := by
  decide +kernel

theorem rows12822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12822 = true := by
  decide +kernel

theorem tot12822 : totK PD2M8K2 D2M8K2.t12822 = [0, 0, 142738857637, 434366738656, 303278117851, 29474268089, 0, 0] := by
  decide +kernel

theorem rows12823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12823 = true := by
  decide +kernel

theorem tot12823 : totK PD2M8K2 D2M8K2.t12823 = [0, 104114512826, 325496991520, 309189252883, 140615945224, 12108803665, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
