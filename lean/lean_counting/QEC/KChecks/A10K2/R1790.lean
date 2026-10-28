import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7160 = true := by
  decide +kernel

theorem tot7160 : totK PA10K2 A10K2.t7160 = [0, 0, 216629179474, 1187360933963, 2112300733902, 1273438756119, 216274787962, 5255105852, 0, 0] := by
  decide +kernel

theorem rows7161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7161 = true := by
  decide +kernel

theorem tot7161 : totK PA10K2 A10K2.t7161 = [0, 0, 295446790641, 1415067188358, 2212604480903, 1178557600520, 123454689539, 0, 0, 0] := by
  decide +kernel

theorem rows7162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7162 = true := by
  decide +kernel

theorem tot7162 : totK PA10K2 A10K2.t7162 = [0, 0, 350618160902, 1436990478541, 2050185314315, 1060999289121, 171171590648, 7151180950, 0, 0] := by
  decide +kernel

theorem rows7163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7163 = true := by
  decide +kernel

theorem tot7163 : totK PA10K2 A10K2.t7163 = [0, 0, 494137068270, 1876028380495, 2027650429429, 598646947992, 25491742696, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
