import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14012 = true := by
  decide +kernel

theorem tot14012 : totK PD2M8K2 D2M8K2.t14012 = [0, 0, 187510814325, 494105623538, 199931605984, 6183963550, 0, 0] := by
  decide +kernel

theorem rows14013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14013 = true := by
  decide +kernel

theorem tot14013 : totK PD2M8K2 D2M8K2.t14013 = [0, 0, 175007533266, 470234989747, 207837356678, 12906904012, 0, 0] := by
  decide +kernel

theorem rows14014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14014 = true := by
  decide +kernel

theorem tot14014 : totK PD2M8K2 D2M8K2.t14014 = [0, 0, 236812391031, 483976567394, 169551040365, 14414509260, 0, 0] := by
  decide +kernel

theorem rows14015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14015 = true := by
  decide +kernel

theorem tot14015 : totK PD2M8K2 D2M8K2.t14015 = [0, 0, 167293712452, 448422297924, 265901249791, 19220775896, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
