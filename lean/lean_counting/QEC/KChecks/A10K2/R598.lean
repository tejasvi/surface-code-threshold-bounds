import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2392 = true := by
  decide +kernel

theorem tot2392 : totK PA10K2 A10K2.t2392 = [0, 444206561081, 1647286251499, 2027134678520, 870161524815, 96232889395, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2393 = true := by
  decide +kernel

theorem tot2393 : totK PA10K2 A10K2.t2393 = [0, 335248154467, 1678458268524, 2242505091751, 833001093409, 63887184235, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2394 = true := by
  decide +kernel

theorem tot2394 : totK PA10K2 A10K2.t2394 = [0, 0, 563035420372, 2054933563141, 2041205171767, 459914999949, 13543209714, 0, 0, 0] := by
  decide +kernel

theorem rows2395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2395 = true := by
  decide +kernel

theorem tot2395 : totK PA10K2 A10K2.t2395 = [0, 0, 416660977273, 1662764265139, 2075143226124, 774621323154, 69440933453, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
