import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2980 = true := by
  decide +kernel

theorem tot2980 : totK PA10K2 A10K2.t2980 = [0, 0, 574854088153, 2070225342961, 2017864663073, 452556957889, 13532411735, 0, 0, 0] := by
  decide +kernel

theorem rows2981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2981 = true := by
  decide +kernel

theorem tot2981 : totK PA10K2 A10K2.t2981 = [0, 0, 344636018854, 1522833471410, 2115976790801, 850643004466, 74778429178, 0, 0, 0] := by
  decide +kernel

theorem rows2982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2982 = true := by
  decide +kernel

theorem tot2982 : totK PA10K2 A10K2.t2982 = [0, 0, 485111030086, 1902156091221, 1945288757879, 485009582299, 12350643961, 0, 0, 0] := by
  decide +kernel

theorem rows2983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2983 = true := by
  decide +kernel

theorem tot2983 : totK PA10K2 A10K2.t2983 = [0, 0, 0, 540194733021, 1909566428615, 1712728439910, 411913634069, 25239774317, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
