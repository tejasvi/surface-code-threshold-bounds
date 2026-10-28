import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t532 = true := by
  decide +kernel

theorem tot532 : totK PA10K2 A10K2.t532 = [0, 461108409457, 1857698630554, 1903047004007, 450251531112, 25667075836, 0, 0, 0, 0] := by
  decide +kernel

theorem rows533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t533 = true := by
  decide +kernel

theorem tot533 : totK PA10K2 A10K2.t533 = [0, 231235616086, 1156238764615, 2009206668888, 1177123273871, 234244221127, 20060612110, 0, 0, 0] := by
  decide +kernel

theorem rows534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t534 = true := by
  decide +kernel

theorem tot534 : totK PA10K2 A10K2.t534 = [0, 111506641315, 790839688076, 1885972381015, 1504859864967, 321114035354, 10589884120, 0, 0, 0] := by
  decide +kernel

theorem rows535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t535 = true := by
  decide +kernel

theorem tot535 : totK PA10K2 A10K2.t535 = [0, 558076783208, 1851643761840, 1835838964855, 505237054154, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
