import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3728 = true := by
  decide +kernel

theorem tot3728 : totK PA10K2 A10K2.t3728 = [0, 0, 196489844652, 1004269628769, 1937959485420, 1371227943531, 222801456234, 5718040558, 0, 0] := by
  decide +kernel

theorem rows3729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3729 = true := by
  decide +kernel

theorem tot3729 : totK PA10K2 A10K2.t3729 = [0, 0, 583313821732, 1867083579040, 1793037059212, 519791789418, 31941609474, 0, 0, 0] := by
  decide +kernel

theorem rows3730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3730 = true := by
  decide +kernel

theorem tot3730 : totK PA10K2 A10K2.t3730 = [0, 0, 0, 1036618756961, 2411790899012, 1177367821882, 106330077380, 0, 0, 0] := by
  decide +kernel

theorem rows3731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3731 = true := by
  decide +kernel

theorem tot3731 : totK PA10K2 A10K2.t3731 = [0, 0, 390762680392, 1413527081950, 1849973460275, 1020647489399, 194271170553, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
