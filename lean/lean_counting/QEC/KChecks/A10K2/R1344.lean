import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5376 = true := by
  decide +kernel

theorem tot5376 : totK PA10K2 A10K2.t5376 = [0, 469228150380, 1650363882787, 1904353603794, 810316931925, 152949453784, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5377 = true := by
  decide +kernel

theorem tot5377 : totK PA10K2 A10K2.t5377 = [0, 274182752643, 1330836017377, 2037510623754, 1126055414463, 159769804565, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5378 = true := by
  decide +kernel

theorem tot5378 : totK PA10K2 A10K2.t5378 = [0, 0, 486545195157, 1872052379034, 2005892166616, 525881833624, 12926121504, 0, 0, 0] := by
  decide +kernel

theorem rows5379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5379 = true := by
  decide +kernel

theorem tot5379 : totK PA10K2 A10K2.t5379 = [0, 0, 543757215368, 1782219287096, 1838857064331, 640954653522, 61986719512, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
