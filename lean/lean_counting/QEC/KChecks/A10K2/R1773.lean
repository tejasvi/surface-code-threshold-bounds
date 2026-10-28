import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7092 = true := by
  decide +kernel

theorem tot7092 : totK PA10K2 A10K2.t7092 = [0, 175361750573, 925223228393, 1961250201141, 1451287220139, 244516904782, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows7093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7093 = true := by
  decide +kernel

theorem tot7093 : totK PA10K2 A10K2.t7093 = [0, 506706600143, 1690467738066, 1763554734117, 550355145074, 37026429097, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7094 = true := by
  decide +kernel

theorem tot7094 : totK PA10K2 A10K2.t7094 = [0, 0, 1053101467330, 2285418125506, 1080893741102, 83101857740, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7095 = true := by
  decide +kernel

theorem tot7095 : totK PA10K2 A10K2.t7095 = [0, 477186847112, 1503573749765, 1797005009329, 954740128605, 179900697733, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
