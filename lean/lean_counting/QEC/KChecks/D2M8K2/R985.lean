import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3940 = true := by
  decide +kernel

theorem tot3940 : totK PD2M8K2 D2M8K2.t3940 = [0, 0, 0, 261728202899, 471170378383, 112392691216, 2238410476, 0] := by
  decide +kernel

theorem rows3941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3941 = true := by
  decide +kernel

theorem tot3941 : totK PD2M8K2 D2M8K2.t3941 = [0, 0, 115255062804, 388787391995, 294384153874, 58018173044, 2896345377, 0] := by
  decide +kernel

theorem rows3942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3942 = true := by
  decide +kernel

theorem tot3942 : totK PD2M8K2 D2M8K2.t3942 = [0, 0, 221931050584, 472768834200, 165436349747, 7355951982, 0, 0] := by
  decide +kernel

theorem rows3943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3943 = true := by
  decide +kernel

theorem tot3943 : totK PD2M8K2 D2M8K2.t3943 = [0, 0, 205481428732, 476341638377, 200521555101, 11448224421, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
