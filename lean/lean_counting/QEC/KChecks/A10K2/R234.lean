import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t936 = true := by
  decide +kernel

theorem tot936 : totK PA10K2 A10K2.t936 = [0, 0, 0, 741366285847, 2197307094884, 1617069127375, 252112768718, 6021244195, 0, 0] := by
  decide +kernel

theorem rows937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t937 = true := by
  decide +kernel

theorem tot937 : totK PA10K2 A10K2.t937 = [0, 77440209599, 107972602126, 354775417534, 1605186061542, 2037939450547, 709076559954, 54997142734, 0, 0] := by
  decide +kernel

theorem rows938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t938 = true := by
  decide +kernel

theorem tot938 : totK PA10K2 A10K2.t938 = [0, 489842011413, 1896674630487, 1927483874875, 465048994767, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t939 = true := by
  decide +kernel

theorem tot939 : totK PA10K2 A10K2.t939 = [0, 292098887399, 1444984877078, 2178877631469, 954545153472, 81940907313, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
