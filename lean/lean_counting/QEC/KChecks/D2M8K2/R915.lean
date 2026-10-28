import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3660 = true := by
  decide +kernel

theorem tot3660 : totK PD2M8K2 D2M8K2.t3660 = [0, 0, 267123248965, 510032531658, 97093385605, 1326647619, 0, 0] := by
  decide +kernel

theorem rows3661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3661 = true := by
  decide +kernel

theorem tot3661 : totK PD2M8K2 D2M8K2.t3661 = [0, 133377405113, 400398567241, 340465573978, 41503138589, 0, 0, 0] := by
  decide +kernel

theorem rows3662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3662 = true := by
  decide +kernel

theorem tot3662 : totK PD2M8K2 D2M8K2.t3662 = [0, 180857352920, 462452116143, 235899854657, 16903437389, 0, 0, 0] := by
  decide +kernel

theorem rows3663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3663 = true := by
  decide +kernel

theorem tot3663 : totK PD2M8K2 D2M8K2.t3663 = [0, 106678162435, 423308229854, 351047946506, 45115306868, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
