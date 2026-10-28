import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7556 = true := by
  decide +kernel

theorem tot7556 : totK PA10K2 A10K2.t7556 = [0, 177435414779, 1171795185827, 2156848193982, 1365644432714, 233054106874, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows7557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7557 = true := by
  decide +kernel

theorem tot7557 : totK PA10K2 A10K2.t7557 = [0, 0, 539336039341, 1997016230534, 2134946750077, 532453933373, 12853939499, 0, 0, 0] := by
  decide +kernel

theorem rows7558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7558 = true := by
  decide +kernel

theorem tot7558 : totK PA10K2 A10K2.t7558 = [0, 0, 479850183922, 1761031339642, 1924919119467, 658099724119, 62981882744, 0, 0, 0] := by
  decide +kernel

theorem rows7559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7559 = true := by
  decide +kernel

theorem tot7559 : totK PA10K2 A10K2.t7559 = [0, 0, 296272581747, 1488370413693, 2210310702981, 946277760299, 93046017027, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
