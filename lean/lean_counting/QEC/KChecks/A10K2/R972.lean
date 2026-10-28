import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3888 = true := by
  decide +kernel

theorem tot3888 : totK PA10K2 A10K2.t3888 = [0, 150101656682, 820056782872, 1871971706794, 1596867738070, 396750943003, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows3889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3889 = true := by
  decide +kernel

theorem tot3889 : totK PA10K2 A10K2.t3889 = [0, 444469074786, 1805956266206, 2137219667375, 702614027203, 39845801467, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3890 = true := by
  decide +kernel

theorem tot3890 : totK PA10K2 A10K2.t3890 = [0, 68933609069, 691754456857, 2059804710821, 1827593939040, 400482683020, 13561316338, 0, 0, 0] := by
  decide +kernel

theorem rows3891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3891 = true := by
  decide +kernel

theorem tot3891 : totK PA10K2 A10K2.t3891 = [0, 470066601429, 1836299135619, 2000193289847, 596050816384, 37435735146, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
