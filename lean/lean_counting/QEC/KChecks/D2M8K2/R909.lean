import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3636 = true := by
  decide +kernel

theorem tot3636 : totK PD2M8K2 D2M8K2.t3636 = [0, 174622309206, 456964800959, 269014010914, 25842428429, 0, 0, 0] := by
  decide +kernel

theorem rows3637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3637 = true := by
  decide +kernel

theorem tot3637 : totK PD2M8K2 D2M8K2.t3637 = [0, 88155739502, 357325712240, 376212635245, 75114356919, 1181638453, 0, 0] := by
  decide +kernel

theorem rows3638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3638 = true := by
  decide +kernel

theorem tot3638 : totK PD2M8K2 D2M8K2.t3638 = [0, 45160700657, 281767822632, 450855832446, 120451349601, 3699256714, 0, 0] := by
  decide +kernel

theorem rows3639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3639 = true := by
  decide +kernel

theorem tot3639 : totK PD2M8K2 D2M8K2.t3639 = [0, 177771782894, 474168039233, 217098991785, 10968077050, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
