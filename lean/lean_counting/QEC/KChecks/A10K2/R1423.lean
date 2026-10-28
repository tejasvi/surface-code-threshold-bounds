import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5692 = true := by
  decide +kernel

theorem tot5692 : totK PA10K2 A10K2.t5692 = [0, 0, 0, 585035497024, 2016464582277, 1785686074905, 328003167953, 11508786792, 0, 0] := by
  decide +kernel

theorem rows5693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5693 = true := by
  decide +kernel

theorem tot5693 : totK PA10K2 A10K2.t5693 = [0, 0, 0, 473281407498, 1823200244949, 1919692653108, 497717845660, 32356135070, 0, 0] := by
  decide +kernel

theorem rows5694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5694 = true := by
  decide +kernel

theorem tot5694 : totK PA10K2 A10K2.t5694 = [0, 0, 0, 514092785462, 1848567821570, 1829167204792, 421233193292, 31923085886, 0, 0] := by
  decide +kernel

theorem rows5695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5695 = true := by
  decide +kernel

theorem tot5695 : totK PA10K2 A10K2.t5695 = [0, 0, 0, 300916661433, 1568543675107, 2108063619595, 607776418752, 23918038849, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
