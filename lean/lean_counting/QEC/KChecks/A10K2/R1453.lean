import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5812 = true := by
  decide +kernel

theorem tot5812 : totK PA10K2 A10K2.t5812 = [0, 0, 0, 455135309642, 1772652517207, 1995149069999, 542355425813, 32523532663, 0, 0] := by
  decide +kernel

theorem rows5813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5813 = true := by
  decide +kernel

theorem tot5813 : totK PA10K2 A10K2.t5813 = [0, 0, 0, 60690433792, 961032058500, 2106829599350, 1365566609528, 306916162694, 25565504801, 0] := by
  decide +kernel

theorem rows5814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5814 = true := by
  decide +kernel

theorem tot5814 : totK PA10K2 A10K2.t5814 = [0, 0, 0, 379259283500, 1392318445695, 1803067784021, 926123428980, 153957329320, 5517381808, 0] := by
  decide +kernel

theorem rows5815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5815 = true := by
  decide +kernel

theorem tot5815 : totK PA10K2 A10K2.t5815 = [0, 0, 0, 359742414144, 1717895711666, 2031707808907, 557115503349, 32877822373, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
