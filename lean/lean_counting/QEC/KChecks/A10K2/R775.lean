import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3100 = true := by
  decide +kernel

theorem tot3100 : totK PA10K2 A10K2.t3100 = [0, 0, 473027519034, 1838172947006, 2064887158502, 623717790027, 23615080461, 0, 0, 0] := by
  decide +kernel

theorem rows3101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3101 = true := by
  decide +kernel

theorem tot3101 : totK PA10K2 A10K2.t3101 = [0, 0, 0, 578508880012, 1963456140540, 1719618615607, 379222272212, 12477124820, 0, 0] := by
  decide +kernel

theorem rows3102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3102 = true := by
  decide +kernel

theorem tot3102 : totK PA10K2 A10K2.t3102 = [0, 0, 306257328157, 1454026447107, 2121071238410, 900240880903, 81716853670, 0, 0, 0] := by
  decide +kernel

theorem rows3103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3103 = true := by
  decide +kernel

theorem tot3103 : totK PA10K2 A10K2.t3103 = [0, 0, 568980142366, 1974188614428, 1966167379272, 497186216446, 24494752852, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
