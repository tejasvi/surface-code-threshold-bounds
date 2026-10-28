import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7832 = true := by
  decide +kernel

theorem tot7832 : totK PA10K2 A10K2.t7832 = [0, 0, 643512510042, 2048554100213, 1719420003661, 414499462195, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows7833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7833 = true := by
  decide +kernel

theorem tot7833 : totK PA10K2 A10K2.t7833 = [0, 269380288048, 1159181098224, 1826902808361, 1237262968195, 212927771202, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows7834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7834 = true := by
  decide +kernel

theorem tot7834 : totK PA10K2 A10K2.t7834 = [0, 315590527581, 1536249465690, 2115981593043, 744621587481, 54678751475, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7835 = true := by
  decide +kernel

theorem tot7835 : totK PA10K2 A10K2.t7835 = [0, 190150337554, 1111566985635, 2065068762532, 1247766221874, 190765351122, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
