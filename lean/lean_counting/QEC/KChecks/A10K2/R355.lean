import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1420 = true := by
  decide +kernel

theorem tot1420 : totK PA10K2 A10K2.t1420 = [0, 0, 0, 0, 489192519076, 1831110073722, 1734046670286, 414260880492, 30259048844, 0] := by
  decide +kernel

theorem rows1421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1421 = true := by
  decide +kernel

theorem tot1421 : totK PA10K2 A10K2.t1421 = [0, 0, 0, 0, 0, 957247852224, 2292036653316, 1045346735497, 96953299776, 0] := by
  decide +kernel

theorem rows1422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1422 = true := by
  decide +kernel

theorem tot1422 : totK PA10K2 A10K2.t1422 = [0, 0, 0, 508734062887, 1789779087796, 1727490978381, 493626100479, 221482812926, 87067426044, 5676195732] := by
  decide +kernel

theorem rows1423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1423 = true := by
  decide +kernel

theorem tot1423 : totK PA10K2 A10K2.t1423 = [0, 0, 0, 299599262308, 1460057338788, 2193816079670, 898905726347, 68557683225, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
