import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7432 = true := by
  decide +kernel

theorem tot7432 : totK PD2M8K2 D2M8K2.t7432 = [0, 0, 193183971621, 472092040613, 223052076008, 12370590376, 0, 0] := by
  decide +kernel

theorem rows7433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7433 = true := by
  decide +kernel

theorem tot7433 : totK PD2M8K2 D2M8K2.t7433 = [0, 0, 207027080074, 496916864770, 193795835686, 9402789072, 0, 0] := by
  decide +kernel

theorem rows7434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7434 = true := by
  decide +kernel

theorem tot7434 : totK PD2M8K2 D2M8K2.t7434 = [0, 0, 176753784983, 457330149521, 242155596860, 13908012088, 0, 0] := by
  decide +kernel

theorem rows7435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7435 = true := by
  decide +kernel

theorem tot7435 : totK PD2M8K2 D2M8K2.t7435 = [0, 0, 201978653671, 490229993850, 200109373796, 5469571244, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
