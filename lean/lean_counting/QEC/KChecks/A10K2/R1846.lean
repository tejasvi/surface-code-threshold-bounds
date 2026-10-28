import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7384 = true := by
  decide +kernel

theorem tot7384 : totK PA10K2 A10K2.t7384 = [0, 0, 0, 552283864504, 1926316512821, 1811428404935, 401456560258, 25668410676, 0, 0] := by
  decide +kernel

theorem rows7385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7385 = true := by
  decide +kernel

theorem tot7385 : totK PA10K2 A10K2.t7385 = [0, 0, 0, 544870264593, 1936832326833, 1852637910769, 343365367926, 11323844185, 0, 0] := by
  decide +kernel

theorem rows7386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7386 = true := by
  decide +kernel

theorem tot7386 : totK PA10K2 A10K2.t7386 = [0, 0, 0, 0, 896356428521, 2407577958778, 1180372015496, 102167838679, 0, 0] := by
  decide +kernel

theorem rows7387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7387 = true := by
  decide +kernel

theorem tot7387 : totK PA10K2 A10K2.t7387 = [0, 0, 540022072669, 1706463564108, 1525223114798, 516414989698, 296468060818, 113074279875, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
