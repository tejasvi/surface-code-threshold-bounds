import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4112 = true := by
  decide +kernel

theorem tot4112 : totK PA10K2 A10K2.t4112 = [0, 724974881289, 2129609695141, 1644883180032, 382850868170, 25351274858, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4113 = true := by
  decide +kernel

theorem tot4113 : totK PA10K2 A10K2.t4113 = [280582103063, 1237542614102, 1976460735660, 1252678781593, 209125392668, 5459593153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4114 = true := by
  decide +kernel

theorem tot4114 : totK PA10K2 A10K2.t4114 = [287992640199, 1415627878342, 2211918403530, 1119917822947, 111346865862, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4115 = true := by
  decide +kernel

theorem tot4115 : totK PA10K2 A10K2.t4115 = [510253157435, 1866737219420, 2036907426498, 628071040472, 36649520246, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
