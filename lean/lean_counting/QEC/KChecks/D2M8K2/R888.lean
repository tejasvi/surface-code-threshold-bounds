import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3552 = true := by
  decide +kernel

theorem tot3552 : totK PD2M8K2 D2M8K2.t3552 = [0, 196074008071, 474261512219, 190759730764, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows3553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3553 = true := by
  decide +kernel

theorem tot3553 : totK PD2M8K2 D2M8K2.t3553 = [170590953727, 445931761693, 258769936699, 25443674644, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3554 = true := by
  decide +kernel

theorem tot3554 : totK PD2M8K2 D2M8K2.t3554 = [195786644774, 467842620228, 227371456889, 15693844309, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3555 = true := by
  decide +kernel

theorem tot3555 : totK PD2M8K2 D2M8K2.t3555 = [51362919068, 317311127378, 416867759717, 92068537522, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
