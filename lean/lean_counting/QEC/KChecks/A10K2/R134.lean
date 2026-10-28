import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t536 = true := by
  decide +kernel

theorem tot536 : totK PA10K2 A10K2.t536 = [0, 110080449477, 1301323265119, 2314423123891, 908955536391, 65326404304, 0, 0, 0, 0] := by
  decide +kernel

theorem rows537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t537 = true := by
  decide +kernel

theorem tot537 : totK PA10K2 A10K2.t537 = [0, 385871001132, 1439924105483, 1886721000170, 932061858792, 153851967938, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t538 = true := by
  decide +kernel

theorem tot538 : totK PA10K2 A10K2.t538 = [317716625926, 1225806457519, 1732053352241, 1184092293941, 425246316020, 43888357648, 0, 0, 0, 0] := by
  decide +kernel

theorem rows539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t539 = true := by
  decide +kernel

theorem tot539 : totK PA10K2 A10K2.t539 = [446257702948, 1787150368297, 2054697073917, 663965683881, 44294085443, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
