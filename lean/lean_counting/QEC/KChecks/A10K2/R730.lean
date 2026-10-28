import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2920 = true := by
  decide +kernel

theorem tot2920 : totK PA10K2 A10K2.t2920 = [332208314330, 1560043270249, 2187570503019, 902912908350, 75423133653, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2921 = true := by
  decide +kernel

theorem tot2921 : totK PA10K2 A10K2.t2921 = [0, 532749257364, 1987447191980, 1952998787384, 438877354038, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2922 = true := by
  decide +kernel

theorem tot2922 : totK PA10K2 A10K2.t2922 = [0, 619925266768, 1882801063946, 1805967424828, 588158741894, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2923 = true := by
  decide +kernel

theorem tot2923 : totK PA10K2 A10K2.t2923 = [0, 435690288822, 1811944430978, 2042780174735, 537712198538, 24727641535, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
