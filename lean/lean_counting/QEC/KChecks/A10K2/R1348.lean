import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5392 = true := by
  decide +kernel

theorem tot5392 : totK PA10K2 A10K2.t5392 = [0, 298263154340, 1531899514628, 2065642790799, 726155665542, 45799782675, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5393 = true := by
  decide +kernel

theorem tot5393 : totK PA10K2 A10K2.t5393 = [0, 0, 680997749888, 2154576117011, 1571663990329, 262931578621, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5394 = true := by
  decide +kernel

theorem tot5394 : totK PA10K2 A10K2.t5394 = [0, 0, 533635944737, 1840210354664, 1837195741176, 492633903547, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows5395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5395 = true := by
  decide +kernel

theorem tot5395 : totK PA10K2 A10K2.t5395 = [0, 0, 426215882094, 1760733707040, 2040904645983, 579379499604, 32470943963, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
