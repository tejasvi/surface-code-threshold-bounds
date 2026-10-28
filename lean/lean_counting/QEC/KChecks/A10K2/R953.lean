import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3812 = true := by
  decide +kernel

theorem tot3812 : totK PA10K2 A10K2.t3812 = [0, 0, 294253341288, 1199946000808, 1878674656328, 1159791548409, 189103250763, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3813 = true := by
  decide +kernel

theorem tot3813 : totK PA10K2 A10K2.t3813 = [0, 0, 484330386846, 1846274491126, 1925972047923, 534084561371, 32875687108, 0, 0, 0] := by
  decide +kernel

theorem rows3814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3814 = true := by
  decide +kernel

theorem tot3814 : totK PA10K2 A10K2.t3814 = [0, 0, 0, 733523880819, 2270792506837, 1500121962519, 177593868521, 0, 0, 0] := by
  decide +kernel

theorem rows3815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3815 = true := by
  decide +kernel

theorem tot3815 : totK PA10K2 A10K2.t3815 = [0, 0, 266424507814, 1326374587388, 1984446346055, 1106714790518, 182575058984, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
