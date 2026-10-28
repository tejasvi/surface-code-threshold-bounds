import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7372 = true := by
  decide +kernel

theorem tot7372 : totK PD2M8K2 D2M8K2.t7372 = [0, 0, 0, 230458847208, 463421270142, 161317360737, 9389920916, 0] := by
  decide +kernel

theorem rows7373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7373 = true := by
  decide +kernel

theorem tot7373 : totK PD2M8K2 D2M8K2.t7373 = [0, 0, 165297632584, 428426617952, 245714267209, 43343872722, 2463340669, 0] := by
  decide +kernel

theorem rows7374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7374 = true := by
  decide +kernel

theorem tot7374 : totK PD2M8K2 D2M8K2.t7374 = [0, 0, 154700765775, 464546153858, 260545180401, 18252358503, 0, 0] := by
  decide +kernel

theorem rows7375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7375 = true := by
  decide +kernel

theorem tot7375 : totK PD2M8K2 D2M8K2.t7375 = [0, 0, 90638896091, 374527738591, 342597899005, 58139981748, 1021600638, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
