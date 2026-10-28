import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t11 = true := by
  decide +kernel

theorem tot11 : totK PA6K2 A6K2.t11 = [313961522562, 1151148246571, 1632933708214, 1022661972251, 214877979776, 6999349134] := by
  decide +kernel

end QECKChecks.A6K2
