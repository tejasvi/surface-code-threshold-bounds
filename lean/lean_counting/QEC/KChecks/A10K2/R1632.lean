import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6528 = true := by
  decide +kernel

theorem tot6528 : totK PA10K2 A10K2.t6528 = [0, 0, 0, 521743275043, 1928082362117, 1958851265387, 544672610595, 35586898073, 0, 0] := by
  decide +kernel

theorem rows6529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6529 = true := by
  decide +kernel

theorem tot6529 : totK PA10K2 A10K2.t6529 = [0, 0, 0, 507577029673, 1903939289911, 1835516939465, 450260799427, 26479096260, 0, 0] := by
  decide +kernel

theorem rows6530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6530 = true := by
  decide +kernel

theorem tot6530 : totK PA10K2 A10K2.t6530 = [0, 0, 0, 281106718642, 1392916105901, 2144630412852, 930505734496, 84917271460, 0, 0] := by
  decide +kernel

theorem rows6531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6531 = true := by
  decide +kernel

theorem tot6531 : totK PA10K2 A10K2.t6531 = [0, 0, 0, 0, 529984083708, 1790708217825, 1728035489055, 464447484088, 31018567651, 0] := by
  decide +kernel

end QECKChecks.A10K2
