import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2576 = true := by
  decide +kernel

theorem tot2576 : totK PA10K2 A10K2.t2576 = [0, 998293019772, 2439368062934, 1212407160161, 107167286853, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2577 = true := by
  decide +kernel

theorem tot2577 : totK PA10K2 A10K2.t2577 = [418857662174, 1441626722864, 1849456410811, 1014802149504, 194707687906, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2578 = true := by
  decide +kernel

theorem tot2578 : totK PA10K2 A10K2.t2578 = [83865859844, 941975422686, 2238658693979, 1601908873867, 291032543448, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2579 = true := by
  decide +kernel

theorem tot2579 : totK PA10K2 A10K2.t2579 = [0, 401438078771, 1665431525238, 2019686056928, 754843871222, 69118037806, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
