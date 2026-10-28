import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2344 = true := by
  decide +kernel

theorem tot2344 : totK PA10K2 A10K2.t2344 = [0, 45544482702, 876294423881, 2260628033032, 1606469119638, 283209824970, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows2345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2345 = true := by
  decide +kernel

theorem tot2345 : totK PA10K2 A10K2.t2345 = [0, 0, 538134293105, 1856235266384, 1929952950069, 620009131879, 49818275127, 0, 0, 0] := by
  decide +kernel

theorem rows2346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2346 = true := by
  decide +kernel

theorem tot2346 : totK PA10K2 A10K2.t2346 = [0, 0, 525699093747, 1898445608650, 1886201741039, 456635775042, 17320767229, 0, 0, 0] := by
  decide +kernel

theorem rows2347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2347 = true := by
  decide +kernel

theorem tot2347 : totK PA10K2 A10K2.t2347 = [0, 0, 0, 690532093720, 2076583639546, 1609907614923, 381712632084, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
