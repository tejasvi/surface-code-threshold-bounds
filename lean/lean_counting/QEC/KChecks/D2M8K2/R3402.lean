import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13608 = true := by
  decide +kernel

theorem tot13608 : totK PD2M8K2 D2M8K2.t13608 = [22764130012, 293994394323, 463864923689, 105471358198, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows13609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13609 = true := by
  decide +kernel

theorem tot13609 : totK PD2M8K2 D2M8K2.t13609 = [85167078157, 373809680745, 398095613018, 46655047385, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13610 = true := by
  decide +kernel

theorem tot13610 : totK PD2M8K2 D2M8K2.t13610 = [160084321778, 452919627541, 271183666762, 23762655905, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13611 = true := by
  decide +kernel

theorem tot13611 : totK PD2M8K2 D2M8K2.t13611 = [154883020582, 449589820541, 271266032126, 18633568711, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
