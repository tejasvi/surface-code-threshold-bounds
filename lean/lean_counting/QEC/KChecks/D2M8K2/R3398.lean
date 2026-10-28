import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13592 = true := by
  decide +kernel

theorem tot13592 : totK PD2M8K2 D2M8K2.t13592 = [0, 125457623494, 447513961431, 285802169895, 20023055003, 0, 0, 0] := by
  decide +kernel

theorem rows13593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13593 = true := by
  decide +kernel

theorem tot13593 : totK PD2M8K2 D2M8K2.t13593 = [0, 0, 285533999670, 484365998992, 84332632202, 1239866073, 0, 0] := by
  decide +kernel

theorem rows13594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13594 = true := by
  decide +kernel

theorem tot13594 : totK PD2M8K2 D2M8K2.t13594 = [0, 177647416780, 445437792267, 278535440585, 30845330517, 0, 0, 0] := by
  decide +kernel

theorem rows13595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13595 = true := by
  decide +kernel

theorem tot13595 : totK PD2M8K2 D2M8K2.t13595 = [0, 156820059053, 456362824194, 271927817888, 21715553216, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
