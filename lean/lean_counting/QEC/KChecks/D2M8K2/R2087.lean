import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8348 = true := by
  decide +kernel

theorem tot8348 : totK PD2M8K2 D2M8K2.t8348 = [174456625603, 379632387528, 144482928193, 114875201646, 71452959291, 3882006667, 0, 0] := by
  decide +kernel

theorem rows8349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8349 = true := by
  decide +kernel

theorem tot8349 : totK PD2M8K2 D2M8K2.t8349 = [155548146664, 456555615697, 245766479044, 17030425649, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8350 = true := by
  decide +kernel

theorem tot8350 : totK PD2M8K2 D2M8K2.t8350 = [89411507079, 337827561377, 384797421757, 91255700045, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8351 = true := by
  decide +kernel

theorem tot8351 : totK PD2M8K2 D2M8K2.t8351 = [19899381531, 321886114251, 500151056910, 66293361221, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
