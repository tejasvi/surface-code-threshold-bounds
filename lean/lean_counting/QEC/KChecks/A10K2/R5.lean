import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows20 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t20 = true := by
  decide +kernel

theorem tot20 : totK PA10K2 A10K2.t20 = [279363014200, 1105306392509, 1673325017242, 1216613267907, 322334499553, 16597605730, 0, 0, 0, 0] := by
  decide +kernel

theorem rows21 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t21 = true := by
  decide +kernel

theorem tot21 : totK PA10K2 A10K2.t21 = [494735626471, 1666418057480, 1690042841441, 577965482985, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows22 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t22 = true := by
  decide +kernel

theorem tot22 : totK PA10K2 A10K2.t22 = [0, 954592347671, 2321879383149, 1199754236486, 106439743102, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows23 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t23 = true := by
  decide +kernel

theorem tot23 : totK PA10K2 A10K2.t23 = [0, 523952610352, 1848268494066, 1892988892398, 516807313265, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
