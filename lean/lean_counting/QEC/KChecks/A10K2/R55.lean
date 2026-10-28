import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t220 = true := by
  decide +kernel

theorem tot220 : totK PA10K2 A10K2.t220 = [0, 0, 0, 592470357735, 2022842485644, 1829734644857, 387463442136, 12132367858, 0, 0] := by
  decide +kernel

theorem rows221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t221 = true := by
  decide +kernel

theorem tot221 : totK PA10K2 A10K2.t221 = [0, 321107158991, 1008980148682, 976477859924, 924936974269, 1163319719327, 511713723036, 48886019071, 0, 0] := by
  decide +kernel

theorem rows222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t222 = true := by
  decide +kernel

theorem tot222 : totK PA10K2 A10K2.t222 = [0, 551962001073, 1931939579754, 1894529141582, 424903578447, 11765040145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t223 = true := by
  decide +kernel

theorem tot223 : totK PA10K2 A10K2.t223 = [0, 0, 673816687019, 2103375083012, 1705822944212, 395819049875, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
