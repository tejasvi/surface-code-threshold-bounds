import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7752 = true := by
  decide +kernel

theorem tot7752 : totK PA10K2 A10K2.t7752 = [0, 0, 0, 777076686482, 2223717307772, 1674436994973, 287566387292, 6853348008, 0, 0] := by
  decide +kernel

theorem rows7753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7753 = true := by
  decide +kernel

theorem tot7753 : totK PA10K2 A10K2.t7753 = [0, 0, 0, 400221428745, 1699558366101, 2160105266957, 751257601992, 56143165367, 0, 0] := by
  decide +kernel

theorem rows7754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7754 = true := by
  decide +kernel

theorem tot7754 : totK PA10K2 A10K2.t7754 = [0, 0, 0, 611022369721, 2135060608554, 1920322895471, 400138489801, 12485167370, 0, 0] := by
  decide +kernel

theorem rows7755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7755 = true := by
  decide +kernel

theorem tot7755 : totK PA10K2 A10K2.t7755 = [0, 0, 0, 0, 810988881069, 2348490741277, 1550918150982, 231482546373, 6632180018, 0] := by
  decide +kernel

end QECKChecks.A10K2
