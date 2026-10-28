import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3868 = true := by
  decide +kernel

theorem tot3868 : totK PA10K2 A10K2.t3868 = [0, 0, 0, 0, 503482921238, 1890990997576, 1686063249025, 452342153375, 31690778550, 0] := by
  decide +kernel

theorem rows3869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3869 = true := by
  decide +kernel

theorem tot3869 : totK PA10K2 A10K2.t3869 = [0, 0, 0, 0, 640180816309, 2078870564148, 1617857369523, 273188809108, 6354609102, 0] := by
  decide +kernel

theorem rows3870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3870 = true := by
  decide +kernel

theorem tot3870 : totK PA10K2 A10K2.t3870 = [0, 0, 0, 0, 567348919079, 1857839565141, 1668694845721, 430249473295, 30874154442, 0] := by
  decide +kernel

theorem rows3871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3871 = true := by
  decide +kernel

theorem tot3871 : totK PA10K2 A10K2.t3871 = [0, 0, 0, 0, 0, 1013080942125, 2317689374174, 1070473902955, 87575124345, 0] := by
  decide +kernel

end QECKChecks.A10K2
