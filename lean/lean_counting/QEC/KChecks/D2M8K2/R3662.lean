import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14648 = true := by
  decide +kernel

theorem tot14648 : totK PD2M8K2 D2M8K2.t14648 = [0, 171724729119, 479315749253, 227583173728, 11007376219, 0, 0, 0] := by
  decide +kernel

theorem rows14649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14649 = true := by
  decide +kernel

theorem tot14649 : totK PD2M8K2 D2M8K2.t14649 = [0, 168622644478, 456364009098, 240207977140, 11378154205, 0, 0, 0] := by
  decide +kernel

theorem rows14650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14650 = true := by
  decide +kernel

theorem tot14650 : totK PD2M8K2 D2M8K2.t14650 = [0, 0, 274710512090, 504322699952, 101959537617, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14651 = true := by
  decide +kernel

theorem tot14651 : totK PD2M8K2 D2M8K2.t14651 = [0, 97501213428, 377018352204, 390575071985, 49691505599, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
