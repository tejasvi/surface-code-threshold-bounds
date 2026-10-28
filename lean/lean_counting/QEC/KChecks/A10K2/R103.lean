import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t412 = true := by
  decide +kernel

theorem tot412 : totK PA10K2 A10K2.t412 = [203908507248, 1477985885126, 2318517953292, 912118212310, 70389100257, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t413 = true := by
  decide +kernel

theorem tot413 : totK PA10K2 A10K2.t413 = [0, 479963857915, 1844516360883, 1908518432625, 492258823955, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t414 = true := by
  decide +kernel

theorem tot414 : totK PA10K2 A10K2.t414 = [518135067396, 1837863729622, 1790044018787, 511672553176, 52163948410, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t415 = true := by
  decide +kernel

theorem tot415 : totK PA10K2 A10K2.t415 = [0, 562649191249, 1959958433489, 1689973318967, 388648866513, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
