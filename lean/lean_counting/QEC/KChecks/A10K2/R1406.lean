import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5624 = true := by
  decide +kernel

theorem tot5624 : totK PA10K2 A10K2.t5624 = [0, 0, 0, 601628615169, 2020666981581, 1764863219530, 330886737368, 12918102615, 0, 0] := by
  decide +kernel

theorem rows5625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5625 = true := by
  decide +kernel

theorem tot5625 : totK PA10K2 A10K2.t5625 = [0, 0, 0, 519920033574, 1911883652517, 1797921220479, 399691086683, 25553601783, 0, 0] := by
  decide +kernel

theorem rows5626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5626 = true := by
  decide +kernel

theorem tot5626 : totK PA10K2 A10K2.t5626 = [0, 0, 0, 536537408623, 1964281002012, 1754821018265, 351401553756, 11323844185, 0, 0] := by
  decide +kernel

theorem rows5627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5627 = true := by
  decide +kernel

theorem tot5627 : totK PA10K2 A10K2.t5627 = [0, 0, 27745223503, 17170969028, 792519148355, 2166797773302, 1298229284544, 192289909650, 5676195732, 0] := by
  decide +kernel

end QECKChecks.A10K2
