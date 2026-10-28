import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2548 = true := by
  decide +kernel

theorem tot2548 : totK PA10K2 A10K2.t2548 = [0, 0, 513138304173, 1880854870843, 1807115030321, 354480292281, 11740475125, 0, 0, 0] := by
  decide +kernel

theorem rows2549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2549 = true := by
  decide +kernel

theorem tot2549 : totK PA10K2 A10K2.t2549 = [0, 0, 581254439460, 1906978919668, 1789817901634, 481239519265, 32239129156, 0, 0, 0] := by
  decide +kernel

theorem rows2550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2550 = true := by
  decide +kernel

theorem tot2550 : totK PA10K2 A10K2.t2550 = [0, 0, 431303439499, 1783222883981, 2047449327409, 481530474922, 13113133354, 0, 0, 0] := by
  decide +kernel

theorem rows2551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2551 = true := by
  decide +kernel

theorem tot2551 : totK PA10K2 A10K2.t2551 = [0, 0, 578469238380, 1957197105244, 1772807398610, 382184149872, 30953568651, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
