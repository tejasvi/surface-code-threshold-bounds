import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7996 = true := by
  decide +kernel

theorem tot7996 : totK PA10K2 A10K2.t7996 = [0, 0, 0, 526953387664, 1932659918831, 1874293741174, 400315023061, 10946789654, 0, 0] := by
  decide +kernel

theorem rows7997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7997 = true := by
  decide +kernel

theorem tot7997 : totK PA10K2 A10K2.t7997 = [0, 0, 0, 0, 684404802864, 2074244155673, 1594581667778, 337217271832, 13364899180, 0] := by
  decide +kernel

theorem rows7998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7998 = true := by
  decide +kernel

theorem tot7998 : totK PA10K2 A10K2.t7998 = [0, 0, 0, 286850611385, 1311485536564, 2027808903709, 1031485680578, 112812237605, 0, 0] := by
  decide +kernel

theorem rows7999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7999 = true := by
  decide +kernel

theorem tot7999 : totK PA10K2 A10K2.t7999 = [0, 0, 0, 293454189941, 1487547873737, 2080038291135, 740058081383, 56135202890, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
