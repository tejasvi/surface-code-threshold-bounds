import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t8 = true := by
  decide +kernel

theorem tot8 : totK PA6K2 A6K2.t8 = [536160458595, 1761361818760, 1614648655563, 433044358011, 29473887443, 0] := by
  decide +kernel

end QECKChecks.A6K2
