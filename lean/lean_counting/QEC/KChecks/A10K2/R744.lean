import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2976 = true := by
  decide +kernel

theorem tot2976 : totK PA10K2 A10K2.t2976 = [0, 455202233519, 1616560473803, 1959121146510, 836433062104, 84619529555, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2977 = true := by
  decide +kernel

theorem tot2977 : totK PA10K2 A10K2.t2977 = [0, 105278098493, 1159038632758, 2288042581600, 1070733571125, 86208235720, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2978 = true := by
  decide +kernel

theorem tot2978 : totK PA10K2 A10K2.t2978 = [0, 486648432359, 1678557203456, 1833640101891, 799812430467, 134587985557, 5976421810, 0, 0, 0] := by
  decide +kernel

theorem rows2979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2979 = true := by
  decide +kernel

theorem tot2979 : totK PA10K2 A10K2.t2979 = [0, 314008318368, 1471697795426, 2142465959729, 969579554859, 89191384614, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
